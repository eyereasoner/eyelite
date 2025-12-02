#!/usr/bin/env python3
# =====================================================================================
# eyeling — a minimal Notation3 (N3) reasoner in Python
# =====================================================================================
#
# This file is intentionally self-contained: we keep everything in one file so that
# the project is easy to hack on. If you want to grow this into a package, the
# natural split points are: lexer, parser/AST, unification, reasoner, builtins, CLI.
#
# High-level pipeline:
#
#   1) Read an N3 file from disk.
#   2) Lex it into Tokens.
#   3) Parse tokens into:
#        - ground triples (facts)
#        - forward rules  {premise} => {conclusion}.
#        - backward rules {head} <= {body}.
#   4) Run forward chaining to fixpoint.
#        - premises are proven using backward rules + builtins.
#   5) Print only newly derived forward facts.
#
# The implementation is a pragmatic subset of N3. It is not a full W3C N3 parser.
# The goal is to be small, understandable, and useful.

from __future__ import annotations

import sys
import math
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Iterable, Set

from datetime import datetime, date, timezone, timedelta

sys.setrecursionlimit(100000)

# Python ints are already arbitrary-precision, so we don't need BigInt.


# ==============================================================================
# Namespace constants we expand QNames against.
# ==============================================================================
RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
RDFS_NS = "http://www.w3.org/2000/01/rdf-schema#"
XSD_NS = "http://www.w3.org/2001/XMLSchema#"
LOG_NS = "http://www.w3.org/2000/10/swap/log#"
MATH_NS = "http://www.w3.org/2000/10/swap/math#"
STRING_NS = "http://www.w3.org/2000/10/swap/string#"
LIST_NS = "http://www.w3.org/2000/10/swap/list#"
TIME_NS = "http://www.w3.org/2000/10/swap/time#"

# Safety valve so backward proof doesn’t loop forever in degenerate cases.
MAX_BACKWARD_DEPTH = 50000


# =====================================================================================
# AST (Abstract Syntax Tree)
# =====================================================================================

# A term is any RDF-ish thing that can appear as subject, predicate, or object.
#
# We intentionally keep this small. N3 has more constructs, but these cover:
# - IRIs
# - Literals (numbers, strings, booleans, typed literals)
# - Variables ?x
# - Blank nodes []
# - Lists (...)
# - OpenLists (internal helper for bidirectional list:firstRest)
# - Quoted formulas { ... } (as conjunctions of triple patterns)
#
# In Rust this was an enum; here we model it as a small class hierarchy.


@dataclass(unsafe_hash=True)
class Term:
    """Base class; concrete subclasses hold the actual data."""
    pass


@dataclass(unsafe_hash=True)
class Iri(Term):
    value: str


@dataclass(unsafe_hash=True)
class Literal(Term):
    # Raw lexical form, e.g. "foo", 12, true,
    # or "\"1944-08-21\"^^<http://www.w3.org/2001/XMLSchema#date>"
    value: str


@dataclass(unsafe_hash=True)
class Var(Term):
    # Variable name *without* the leading '?'
    name: str


@dataclass(unsafe_hash=True)
class Blank(Term):
    # Blank node identifier we invent, like _:b1
    label: str


@dataclass(unsafe_hash=True)
class ListTerm(Term):
    # Proper closed list: (a b c)
    elems: List[Term]


@dataclass(unsafe_hash=True)
class OpenListTerm(Term):
    # Internal open list: fixed prefix + tail variable name (like Prolog [H|T]).
    #
    # Example internal state:
    #   OpenListTerm([?H], "T")  means  (?H ?T)
    # but the tail ?T is not yet known.
    #
    # Once ?T becomes a real ListTerm, we "close" it into a ListTerm.
    prefix: List[Term]
    tail_var: str


@dataclass(unsafe_hash=True)
class FormulaTerm(Term):
    # Quoted formula = a conjunction of triple patterns inside `{ ... }`.
    triples: List["Triple"]


# A triple pattern / RDF triple.
@dataclass(unsafe_hash=True, eq=True)
class Triple:
    s: Term
    p: Term
    o: Term


# A Horn-like rule.
# - `premise` is a conjunction.
# - `conclusion` is a conjunction.
# - `is_forward`: true for =>, false for <=.
@dataclass
class Rule:
    premise: List[Triple]
    conclusion: List[Triple]
    is_forward: bool
    # { ... } => false.   (inference fuse / constraint)
    is_fuse: bool


# Substitution mapping variable name -> term.
Subst = Dict[str, Term]


# One forward-derived fact together with a simple justification.
@dataclass
class DerivedFact:
    # The ground triple that was finally added to the fact base.
    fact: Triple
    # The forward rule (in schematic form) that produced this triple.
    rule: Rule
    # The rule body instantiated with the substitution that fired the rule.
    premises: List[Triple]
    # The substitution used when the rule fired.
    subst: Subst


# =====================================================================================
# LEXER
# =====================================================================================

# We implement a simple hand-written lexer, roughly mirroring the Rust version.


@dataclass
class Token:
    # `typ` is the token kind (string label). `value` is extra data (e.g. identifier text).
    typ: str
    value: Optional[str] = None

    def __repr__(self) -> str:
        if self.value is None:
            return f"Token({self.typ})"
        return f"Token({self.typ!r}, {self.value!r})"


def is_ws(c: str) -> bool:
    return c.isspace()


def is_name_char(c: str) -> bool:
    # Characters allowed in identifiers (QName-ish).
    return c.isalnum() or c in "_-:"


def lex(input_text: str) -> List[Token]:
    """
    Lex a whole file into a list of Token objects.

    - We scan left-to-right using an index.
    - We emit tokens as we go.
    - We skip whitespace and comments starting with '#'.
    - On unexpected input we raise a ValueError.
    """
    chars = list(input_text)
    n = len(chars)
    i = 0
    tokens: List[Token] = []

    def peek(offset: int = 0) -> Optional[str]:
        j = i + offset
        return chars[j] if 0 <= j < n else None

    while i < n:
        c = peek()
        if c is None:
            break

        # 1) Skip whitespace
        if is_ws(c):
            i += 1
            continue

        # 2) Skip # comments to end of line
        if c == "#":
            while i < n and chars[i] not in "\n\r":
                i += 1
            continue

        # 3) Two-character operators: => and <=
        if c == "=":
            if peek(1) == ">":
                tokens.append(Token("OpImplies"))
                i += 2
                continue
            else:
                raise ValueError("Unexpected '='")

        if c == "<":
            # either <= or IRIREF <...>
            if peek(1) == "=":
                tokens.append(Token("OpImpliedBy"))
                i += 2
                continue

            # Otherwise IRIREF: <http://...>
            i += 1  # skip '<'
            iri_chars = []
            while i < n and chars[i] != ">":
                iri_chars.append(chars[i])
                i += 1
            if i >= n or chars[i] != ">":
                raise ValueError("Unterminated IRI <...>")
            i += 1  # skip '>'
            iri = "".join(iri_chars)
            tokens.append(Token("IriRef", iri))
            continue

        # 4) Datatype operator ^^ after literals
        if c == "^":
            if peek(1) == "^":
                tokens.append(Token("HatHat"))
                i += 2
                continue
            else:
                raise ValueError("Unexpected '^' (did you mean ^^?)")

        # 5) Single-character punctuation
        if c in "{}()[];,.":  # braces, parens, brackets, semicolon, comma, dot
            mapping = {
                "{": "LBrace",
                "}": "RBrace",
                "(": "LParen",
                ")": "RParen",
                "[": "LBracket",
                "]": "RBracket",
                ";": "Semicolon",
                ",": "Comma",
                ".": "Dot",
            }
            tokens.append(Token(mapping[c]))
            i += 1
            continue

        if c == '"':
            # String literal "...", with minimal escape handling.
            i += 1  # consume opening "
            s_chars = []
            while i < n:
                cc = chars[i]
                i += 1
                if cc == "\\":
                    # keep escapes literally
                    if i < n:
                        esc = chars[i]
                        i += 1
                        s_chars.append("\\")
                        s_chars.append(esc)
                    continue
                if cc == '"':
                    break
                s_chars.append(cc)
            s = '"' + "".join(s_chars) + '"'
            tokens.append(Token("Literal", s))
            continue

        if c == "?":
            # Variable: ?name
            i += 1  # consume '?'
            name_chars = []
            while (cc := peek()) is not None and is_name_char(cc):
                name_chars.append(cc)
                i += 1
            name = "".join(name_chars)
            tokens.append(Token("Var", name))
            continue

        if c == "@":
            # Directives: @prefix, @base
            i += 1  # consume '@'
            word_chars = []
            while (cc := peek()) is not None and cc.isalpha():
                word_chars.append(cc)
                i += 1
            word = "".join(word_chars)
            if word == "prefix":
                tokens.append(Token("AtPrefix"))
            elif word == "base":
                tokens.append(Token("AtBase"))
            else:
                raise ValueError(f"Unknown directive @{word}")
            continue

        # 6) Numeric literal (integer or float)
        #    We treat a leading '-' as part of a number only if followed by digit.
        if c.isdigit() or (
            c == "-"
            and peek(1) is not None
            and peek(1).isdigit()
        ):
            num_chars = [c]
            i += 1
            while i < n:
                cc = chars[i]
                if cc.isdigit():
                    num_chars.append(cc)
                    i += 1
                    continue
                if cc == ".":
                    # only keep '.' if it's a decimal point; otherwise '.' ends statement.
                    if (i + 1 < n) and chars[i + 1].isdigit():
                        num_chars.append(".")
                        i += 1
                        continue
                    else:
                        break
                break
            tokens.append(Token("Literal", "".join(num_chars)))
            continue

        # 7) Identifiers / keywords / QNames
        word_chars = []
        while (cc := peek()) is not None and is_name_char(cc):
            word_chars.append(cc)
            i += 1
        if not word_chars:
            raise ValueError(f"Unexpected char: {c!r}")
        word = "".join(word_chars)

        if word in ("true", "false"):
            tokens.append(Token("Literal", word))
        elif all(ch.isdigit() or ch in ".-" for ch in word):
            tokens.append(Token("Literal", word))
        else:
            tokens.append(Token("Ident", word))

    tokens.append(Token("EOF"))
    return tokens


# =====================================================================================
# PREFIX ENVIRONMENT
# =====================================================================================

@dataclass
class PrefixEnv:
    # Maps prefixes (`rdf`, `xsd`, `:`) to full IRIs.
    # Prefix expansion only happens during parsing.
    map: Dict[str, str] = field(default_factory=dict)

    @staticmethod
    def new_default() -> "PrefixEnv":
        # "Built-in" defaults so most files work without explicit prefix handling.
        m: Dict[str, str] = {}
        m["rdf"] = RDF_NS
        m["rdfs"] = RDFS_NS
        m["xsd"] = XSD_NS
        m["log"] = LOG_NS
        m["math"] = MATH_NS
        m["string"] = STRING_NS
        m["list"] = LIST_NS
        m["time"] = TIME_NS
        # Default prefix ":" maps to base IRI (possibly @base).
        m[""] = ""
        return PrefixEnv(m)

    def set(self, pref: str, base: str) -> None:
        # Set or override a prefix mapping.
        self.map[pref] = base

    def expand_qname(self, q: str) -> str:
        # Expand a QName like `xsd:date` to a full IRI.
        if ":" in q:
            p, local = q.split(":", 1)
            base = self.map.get(p, "")
            if base:
                return base + local
        # If we don’t know this prefix, return unchanged.
        return q

    def shrink_iri(self, iri: str) -> Optional[str]:
        """
        Try to shrink a full IRI back to a QName for pretty printing.
        We pick the “best” (shortest local name) matching prefix.
        """
        best: Optional[Tuple[str, str]] = None  # (prefix, local)
        for p, base in self.map.items():
            if not base:
                continue
            if iri.startswith(base):
                local = iri[len(base) :]
                if not local:
                    continue
                cand = (p, local)
                if best is None or len(cand[1]) < len(best[1]):
                    best = cand
        if best is None:
            return None
        p, local = best
        if p == "":
            return f":{local}"
        else:
            return f"{p}:{local}"

    def prefixes_used_for_output(self, triples: List[Triple]) -> List[Tuple[str, str]]:
        """
        Decide which prefixes are actually needed in output.
        Returns a list of (prefix, iri) pairs sorted by prefix.
        """
        used: Set[str] = set()
        for t in triples:
            iris: List[str] = []
            iris.extend(collect_iris_in_term(t.s))
            if not is_rdf_type_pred(t.p):
                iris.extend(collect_iris_in_term(t.p))
            iris.extend(collect_iris_in_term(t.o))

            for iri in iris:
                for p, base in self.map.items():
                    if base and iri.startswith(base):
                        used.add(p)

        v: List[Tuple[str, str]] = [
            (p, self.map[p]) for p in used if p in self.map
        ]
        v.sort(key=lambda x: x[0])
        return v


def collect_iris_in_term(t: Term) -> List[str]:
    """
    Collect all IRIs appearing inside a term (recursing into lists/formulas).
    """
    out: List[str] = []
    if isinstance(t, Iri):
        out.append(t.value)
    elif isinstance(t, ListTerm):
        for x in t.elems:
            out.extend(collect_iris_in_term(x))
    elif isinstance(t, OpenListTerm):
        for x in t.prefix:
            out.extend(collect_iris_in_term(x))
    elif isinstance(t, FormulaTerm):
        for tr in t.triples:
            out.extend(collect_iris_in_term(tr.s))
            out.extend(collect_iris_in_term(tr.p))
            out.extend(collect_iris_in_term(tr.o))
    # Literals, Vars, Blanks have no IRIs
    return out


def collect_vars_in_term(t: Term, acc: Set[str]) -> None:
    """
    Collect all variable names appearing inside a term
    (recursing into lists and formulas).
    """
    if isinstance(t, Var):
        acc.add(t.name)
    elif isinstance(t, ListTerm):
        for x in t.elems:
            collect_vars_in_term(x, acc)
    elif isinstance(t, OpenListTerm):
        for x in t.prefix:
            collect_vars_in_term(x, acc)
        acc.add(t.tail_var)
    elif isinstance(t, FormulaTerm):
        for tr in t.triples:
            collect_vars_in_term(tr.s, acc)
            collect_vars_in_term(tr.p, acc)
            collect_vars_in_term(tr.o, acc)
    # Iri, Literal, Blank: nothing to collect


def vars_in_rule(rule: Rule) -> Set[str]:
    """
    Collect the set of variable names that syntactically occur in a rule
    (both in the premise and the conclusion).
    """
    acc: Set[str] = set()
    for tr in rule.premise:
        collect_vars_in_term(tr.s, acc)
        collect_vars_in_term(tr.p, acc)
        collect_vars_in_term(tr.o, acc)
    for tr in rule.conclusion:
        collect_vars_in_term(tr.s, acc)
        collect_vars_in_term(tr.p, acc)
        collect_vars_in_term(tr.o, acc)
    return acc


# =====================================================================================
# PARSER
# =====================================================================================

class Parser:
    """
    A tiny recursive-descent parser.

    We parse from tokens into facts + rules.
    This is not a full N3 parser; it supports the patterns used in examples.
    """

    def __init__(self, tokens: List[Token]) -> None:
        self.toks = tokens
        self.pos = 0
        self.prefixes = PrefixEnv.new_default()
        self.blank_counter = 0
        self.pending_triples: List[Triple] = []

    def peek(self) -> Token:
        return self.toks[self.pos]

    def next(self) -> Token:
        tok = self.toks[self.pos]
        self.pos += 1
        return tok

    def expect_dot(self) -> None:
        tok = self.next()
        if tok.typ != "Dot":
            raise ValueError(f"Expected '.', got {tok!r}")

    def parse_document(
        self,
    ) -> Tuple[PrefixEnv, List[Triple], List[Rule], List[Rule]]:
        """
        Parse a whole document.

        Returns:
        - prefixes
        - ground triples
        - forward rules
        - backward rules
        """
        triples: List[Triple] = []
        forward_rules: List[Rule] = []
        backward_rules: List[Rule] = []

        while self.peek().typ != "EOF":
            if self.peek().typ == "AtPrefix":
                self.next()
                self.parse_prefix_directive()
            elif self.peek().typ == "AtBase":
                self.next()
                self.parse_base_directive()
            else:
                # statement:
                #   term (=>|<= term)? .
                # OR a normal triple statement.
                first = self.parse_term()

                if self.peek().typ == "OpImplies":
                    self.next()
                    second = self.parse_term()
                    self.expect_dot()
                    forward_rules.append(self.make_rule(first, second, True))
                elif self.peek().typ == "OpImpliedBy":
                    self.next()
                    second = self.parse_term()
                    self.expect_dot()
                    backward_rules.append(self.make_rule(first, second, False))
                else:
                    # classic subject predicateObjectList .
                    more = self.parse_predicate_object_list(first)
                    self.expect_dot()

                    # normalize explicit log:implies / log:impliedBy at top-level
                    for tr in more:
                        if (
                            is_log_implies(tr.p)
                            and isinstance(tr.s, FormulaTerm)
                            and isinstance(tr.o, FormulaTerm)
                        ):
                            forward_rules.append(
                                self.make_rule(tr.s, tr.o, True)
                            )
                        elif (
                            is_log_implied_by(tr.p)
                            and isinstance(tr.s, FormulaTerm)
                            and isinstance(tr.o, FormulaTerm)
                        ):
                            backward_rules.append(
                                self.make_rule(tr.s, tr.o, False)
                            )
                        else:
                            triples.append(tr)

        return self.prefixes, triples, forward_rules, backward_rules

    def parse_prefix_directive(self) -> None:
        """
        Parse `@prefix p: <...> .` or `@prefix p: .`
        """
        tok = self.next()
        if tok.typ != "Ident":
            raise ValueError(f"Expected prefix name, got {tok!r}")
        pref = tok.value or ""

        if pref.endswith(":"):
            pref_name = pref[:-1]
        else:
            pref_name = pref

        # Allow @prefix p: . (empty IRI)
        if self.peek().typ == "Dot":
            self.next()
            if pref_name not in self.prefixes.map:
                self.prefixes.set(pref_name, "")
            return

        tok2 = self.next()
        if tok2.typ == "IriRef":
            iri = tok2.value or ""
        elif tok2.typ == "Ident":
            iri = self.prefixes.expand_qname(tok2.value or "")
        else:
            raise ValueError(f"Expected IRI after @prefix, got {tok2!r}")

        self.expect_dot()
        self.prefixes.set(pref_name, iri)

    def parse_base_directive(self) -> None:
        """
        Parse `@base <...> .`
        """
        tok = self.next()
        if tok.typ == "IriRef":
            iri = tok.value or ""
        elif tok.typ == "Ident":
            iri = tok.value or ""
        else:
            raise ValueError(f"Expected IRI after @base, got {tok!r}")
        self.expect_dot()
        self.prefixes.set("", iri)

    def parse_term(self) -> Term:
        tok = self.next()
        typ = tok.typ
        val = tok.value

        if typ == "IriRef":
            return Iri(val or "")

        if typ == "Ident":
            name = val or ""
            if name == "a":
                # rdf:type keyword
                return Iri(RDF_NS + "type")
            elif name.startswith("_:"):
                # Labeled blank node (Turtle/N3 syntax _:foo)
                return Blank(name)
            elif ":" in name:
                # QName
                return Iri(self.prefixes.expand_qname(name))
            else:
                # Bareword treated as an IRI-ish identifier
                return Iri(name)

        if typ == "Literal":
            s = val or ""
            # Typed literal: "..."^^xsd:date
            if self.peek().typ == "HatHat":
                self.next()  # consume ^^
                dt_tok = self.next()
                if dt_tok.typ == "IriRef":
                    dt_iri = dt_tok.value or ""
                elif dt_tok.typ == "Ident":
                    qn = dt_tok.value or ""
                    if ":" in qn:
                        dt_iri = self.prefixes.expand_qname(qn)
                    else:
                        dt_iri = qn
                else:
                    raise ValueError(f"Expected datatype after ^^, got {dt_tok!r}")
                s = f"{s}^^<{dt_iri}>"
            return Literal(s)

        if typ == "Var":
            return Var(val or "")

        if typ == "LParen":
            return self.parse_list()

        if typ == "LBracket":
            return self.parse_blank()

        if typ == "LBrace":
            return self.parse_formula()

        raise ValueError(f"Unexpected term token: {tok!r}")

    def parse_list(self) -> Term:
        """
        Parse `( ... )` list.
        """
        elems: List[Term] = []
        while self.peek().typ != "RParen":
            elems.append(self.parse_term())
        self.next()  # consume ')'
        return ListTerm(elems)

    def parse_blank(self) -> Term:
        """
        Parse blank node `[]` or `[ ... ]` property list.

        - `[]`          => a fresh Blank
        - `[ :p :o ]`   => a fresh Blank plus extra triples
                           _:bN :p :o .
        """
        # Simple [] with no property list
        if self.peek().typ == "RBracket":
            self.next()
            self.blank_counter += 1
            return Blank(f"_:b{self.blank_counter}")

        # Blank node property list: [ predicateObjectList ]
        self.blank_counter += 1
        id_ = f"_:b{self.blank_counter}"
        subj = Blank(id_)

        # Minimal inline `predicateObjectList` for the blank node.
        while True:
            # Verb (can also be 'a')
            if self.peek().typ == "Ident" and (self.peek().value or "") == "a":
                self.next()
                pred: Term = Iri(RDF_NS + "type")
            else:
                pred = self.parse_term()

            # Object list: o1, o2, ...
            objs: List[Term] = [self.parse_term()]
            while self.peek().typ == "Comma":
                self.next()
                objs.append(self.parse_term())

            for o in objs:
                self.pending_triples.append(Triple(subj, pred, o))

            if self.peek().typ == "Semicolon":
                self.next()
                if self.peek().typ == "RBracket":
                    break
                continue
            break

        # Expect closing ']'
        if self.peek().typ == "RBracket":
            self.next()
        else:
            raise ValueError(
                f"Expected ']' at end of blank node property list, got {self.peek()!r}"
            )

        # Return the blank node term; the extra triples are now in
        # self.pending_triples and will be attached by the caller.
        return Blank(id_)

    def parse_formula(self) -> Term:
        """
        Parse `{ ... }` formula.

        Inside formulas the last '.' can be omitted, so we accept either '.' or '}'.
        Nested rules `{ A } => { B }` and `{ A } <= { B }` inside a formula are
        represented as explicit `log:implies` / `log:impliedBy` triples:

          { A } => { B }   ==>   (A) log:implies (B)
          { A } <= { B }   ==>   (A) log:impliedBy (B)
        """
        triples: List[Triple] = []

        while self.peek().typ != "RBrace":
            left = self.parse_term()

            if self.peek().typ == "OpImplies":
                # { left } => { right }  inside a formula
                self.next()
                right = self.parse_term()
                pred = Iri(LOG_NS + "implies")
                triples.append(Triple(left, pred, right))

                if self.peek().typ == "Dot":
                    self.next()
                elif self.peek().typ == "RBrace":
                    pass
                else:
                    raise ValueError(
                        f"Expected '.' or '}}', got {self.peek()!r}"
                    )

            elif self.peek().typ == "OpImpliedBy":
                # { left } <= { right }  inside a formula
                self.next()
                right = self.parse_term()
                pred = Iri(LOG_NS + "impliedBy")
                triples.append(Triple(left, pred, right))

                if self.peek().typ == "Dot":
                    self.next()
                elif self.peek().typ == "RBrace":
                    pass
                else:
                    raise ValueError(
                        f"Expected '.' or '}}', got {self.peek()!r}"
                    )

            else:
                triples.extend(self.parse_predicate_object_list(left))
                if self.peek().typ == "Dot":
                    self.next()
                elif self.peek().typ == "RBrace":
                    pass
                else:
                    raise ValueError(
                        f"Expected '.' or '}}', got {self.peek()!r}"
                    )

        self.next()  # consume '}'
        return FormulaTerm(triples)

    def parse_predicate_object_list(self, subject: Term) -> List[Triple]:
        """
        Parse `subject predicateObjectList` allowing ; and ,.
        """
        out: List[Triple] = []

        while True:
            # Verb can be 'a'
            if self.peek().typ == "Ident" and (self.peek().value or "") == "a":
                self.next()
                verb: Term = Iri(RDF_NS + "type")
            else:
                verb = self.parse_term()

            objects = self.parse_object_list()
            for o in objects:
                out.append(Triple(subject, verb, o))

            if self.peek().typ == "Semicolon":
                self.next()
                if self.peek().typ == "Dot":
                    break
                continue
            break

        # Attach any triples created by blank node property lists `[ ... ]`
        if self.pending_triples:
            out.extend(self.pending_triples)
            self.pending_triples = []

        return out

    def parse_object_list(self) -> List[Term]:
        """
        Parse object list `o1, o2, ...`
        """
        objs = [self.parse_term()]
        while self.peek().typ == "Comma":
            self.next()
            objs.append(self.parse_term())
        return objs

    def make_rule(self, left: Term, right: Term, is_forward: bool) -> Rule:
        """
        Convert lhs/rhs terms into Rule struct.
        For <= rules, swap to keep premise/body on the left.
        """
        if is_forward:
            premise_term, concl_term = left, right
        else:
            premise_term, concl_term = right, left

        # Inference fuse: { ... } => false.
        is_fuse = False
        if is_forward:
            if isinstance(concl_term, Literal) and concl_term.value == "false":
                is_fuse = True

        if isinstance(premise_term, FormulaTerm):
            raw_premise = premise_term.triples
        elif isinstance(premise_term, Literal) and premise_term.value == "true":
            raw_premise = []
        else:
            raw_premise = []

        if isinstance(concl_term, FormulaTerm):
            raw_conclusion = concl_term.triples
        elif isinstance(concl_term, Literal) and concl_term.value == "false":
            # For fuses, there are no head triples to derive.
            raw_conclusion = []
        else:
            raw_conclusion = []

        # lift rule-local blank nodes to variables.
        premise, conclusion = lift_blank_rule_vars(raw_premise, raw_conclusion)

        return Rule(premise=premise, conclusion=conclusion,
                    is_forward=is_forward, is_fuse=is_fuse)


# =====================================================================================
# Blank-node lifting and Skolemization
# =====================================================================================

def lift_blank_rule_vars(
    premise: List[Triple],
    conclusion: List[Triple],
) -> Tuple[List[Triple], List[Triple]]:
    """
    Convert every Blank *in the premise* into a rule-scoped variable.

    Blank nodes in the rule body become “pattern variables”.
    Blank nodes in the head stay blank and are treated existentially.
    """

    def convert_term(
        t: Term,
        mapping: Dict[str, str],
        counter: List[int],  # single-element list to mimic mutable counter
    ) -> Term:
        if isinstance(t, Blank):
            label = t.label
            if label not in mapping:
                counter[0] += 1
                mapping[label] = f"_b{counter[0]}"
            var_name = mapping[label]
            return Var(var_name)

        if isinstance(t, ListTerm):
            return ListTerm([convert_term(e, mapping, counter) for e in t.elems])

        if isinstance(t, OpenListTerm):
            return OpenListTerm(
                [convert_term(e, mapping, counter) for e in t.prefix],
                t.tail_var,
            )

        if isinstance(t, FormulaTerm):
            triples = [
                Triple(
                    convert_term(tr.s, mapping, counter),
                    convert_term(tr.p, mapping, counter),
                    convert_term(tr.o, mapping, counter),
                )
                for tr in t.triples
            ]
            return FormulaTerm(triples)

        return t

    def convert_triple(
        tr: Triple,
        mapping: Dict[str, str],
        counter: List[int],
    ) -> Triple:
        return Triple(
            convert_term(tr.s, mapping, counter),
            convert_term(tr.p, mapping, counter),
            convert_term(tr.o, mapping, counter),
        )

    mapping: Dict[str, str] = {}
    counter = [0]

    new_premise = [convert_triple(tr, mapping, counter) for tr in premise]
    # Head blanks are left untouched → existentials.
    return new_premise, conclusion


def skolemize_term(
    t: Term,
    mapping: Dict[str, str],
    sk_counter: List[int],
) -> Term:
    """
    Skolemize blank nodes in a conclusion term.

    mapping: maps original blank labels (e.g. "_:B") to fresh "_:sk_N" for
    THIS rule application.
    sk_counter: global counter for fresh blank ids across the whole run.
    """
    if isinstance(t, Blank):
        label = t.label
        if label not in mapping:
            idx = sk_counter[0]
            sk_counter[0] += 1
            mapping[label] = f"_:sk_{idx}"
        return Blank(mapping[label])

    if isinstance(t, ListTerm):
        return ListTerm([skolemize_term(e, mapping, sk_counter) for e in t.elems])

    if isinstance(t, OpenListTerm):
        return OpenListTerm(
            [skolemize_term(e, mapping, sk_counter) for e in t.prefix],
            t.tail_var,
        )

    if isinstance(t, FormulaTerm):
        return FormulaTerm(
            [skolemize_triple(tr, mapping, sk_counter) for tr in t.triples]
        )

    return t


def skolemize_triple(
    tr: Triple,
    mapping: Dict[str, str],
    sk_counter: List[int],
) -> Triple:
    return Triple(
        skolemize_term(tr.s, mapping, sk_counter),
        skolemize_term(tr.p, mapping, sk_counter),
        skolemize_term(tr.o, mapping, sk_counter),
    )


def alpha_eq_term(
    a: Term,
    b: Term,
    bmap: Dict[str, str],
) -> bool:
    """
    Alpha-equivalence on terms: blanks may differ by name but must map consistently.
    """
    if isinstance(a, Blank) and isinstance(b, Blank):
        x, y = a.label, b.label
        if x in bmap:
            return bmap[x] == y
        else:
            bmap[x] = y
            return True

    if isinstance(a, Iri) and isinstance(b, Iri):
        return a.value == b.value

    if isinstance(a, Literal) and isinstance(b, Literal):
        return a.value == b.value

    if isinstance(a, Var) and isinstance(b, Var):
        return a.name == b.name

    if isinstance(a, ListTerm) and isinstance(b, ListTerm):
        if len(a.elems) != len(b.elems):
            return False
        return all(alpha_eq_term(x, y, bmap) for x, y in zip(a.elems, b.elems))

    if isinstance(a, OpenListTerm) and isinstance(b, OpenListTerm):
        if a.tail_var != b.tail_var or len(a.prefix) != len(b.prefix):
            return False
        return all(
            alpha_eq_term(x, y, bmap) for x, y in zip(a.prefix, b.prefix)
        )

    # For formulas we keep the simple equality used elsewhere.
    if isinstance(a, FormulaTerm) and isinstance(b, FormulaTerm):
        return a.triples == b.triples

    return False


def alpha_eq_triple(a: Triple, b: Triple) -> bool:
    bmap: Dict[str, str] = {}
    return (
        alpha_eq_term(a.s, b.s, bmap)
        and alpha_eq_term(a.p, b.p, bmap)
        and alpha_eq_term(a.o, b.o, bmap)
    )


from typing import Iterable  # you already import Iterable at the top

def has_alpha_equiv(triples: Iterable[Triple], tr: Triple) -> bool:
    return any(alpha_eq_triple(t, tr) for t in triples)


# =====================================================================================
# Small helpers about special predicates
# =====================================================================================

def is_rdf_type_pred(p: Term) -> bool:
    return isinstance(p, Iri) and p.value == RDF_NS + "type"


def is_log_implies(p: Term) -> bool:
    return isinstance(p, Iri) and p.value == LOG_NS + "implies"


def is_log_implied_by(p: Term) -> bool:
    return isinstance(p, Iri) and p.value == LOG_NS + "impliedBy"


# =====================================================================================
# Unification + substitution
# =====================================================================================

def contains_var_term(t: Term, v: str) -> bool:
    """
    Does term t contain variable v?
    """
    if isinstance(t, Var):
        return t.name == v
    if isinstance(t, ListTerm):
        return any(contains_var_term(e, v) for e in t.elems)
    if isinstance(t, OpenListTerm):
        return any(contains_var_term(e, v) for e in t.prefix) or t.tail_var == v
    if isinstance(t, FormulaTerm):
        return any(
            contains_var_term(tr.s, v)
            or contains_var_term(tr.p, v)
            or contains_var_term(tr.o, v)
            for tr in t.triples
        )
    return False


def is_ground_term(t: Term) -> bool:
    """
    Is a term fully ground (no variables, no open tails)?
    """
    if isinstance(t, Var):
        return False
    if isinstance(t, ListTerm):
        return all(is_ground_term(e) for e in t.elems)
    if isinstance(t, OpenListTerm):
        return False
    if isinstance(t, FormulaTerm):
        return all(is_ground_triple(tr) for tr in t.triples)
    return True


def is_ground_triple(tr: Triple) -> bool:
    return is_ground_term(tr.s) and is_ground_term(tr.p) and is_ground_term(tr.o)


def apply_subst_term(t: Term, s: Subst) -> Term:
    """
    Apply substitution to a term.
    """
    if isinstance(t, Var):
        # Follow substitution chains ?X -> ?Y -> ... to a fixed point.
        cur: Term = Var(t.name)
        seen: Set[str] = set()

        while isinstance(cur, Var):
            name = cur.name
            if name in seen:
                break  # cycle
            seen.add(name)
            nxt = s.get(name)
            if nxt is None:
                break
            cur = nxt

        if isinstance(cur, Var):
            return Var(cur.name)
        else:
            # apply again in case there are nested Vars
            return apply_subst_term(cur, s)

    if isinstance(t, ListTerm):
        return ListTerm([apply_subst_term(e, s) for e in t.elems])

    if isinstance(t, OpenListTerm):
        new_prefix = [apply_subst_term(e, s) for e in t.prefix]
        # If the tail variable is bound, try to “close” the open list.
        tail_term = s.get(t.tail_var)
        if tail_term is not None:
            tail_applied = apply_subst_term(tail_term, s)
            if isinstance(tail_applied, ListTerm):
                all_elems = new_prefix + tail_applied.elems
                return ListTerm(all_elems)
            elif isinstance(tail_applied, OpenListTerm):
                all_prefix = new_prefix + tail_applied.prefix
                return OpenListTerm(all_prefix, tail_applied.tail_var)
            else:
                return OpenListTerm(new_prefix, t.tail_var)
        else:
            return OpenListTerm(new_prefix, t.tail_var)

    if isinstance(t, FormulaTerm):
        return FormulaTerm([apply_subst_triple(tr, s) for tr in t.triples])

    # Iri, Literal, Blank
    return t


def apply_subst_triple(tr: Triple, s: Subst) -> Triple:
    return Triple(
        apply_subst_term(tr.s, s),
        apply_subst_term(tr.p, s),
        apply_subst_term(tr.o, s),
    )


def unify_open_with_list(
    prefix: List[Term],
    tailv: str,
    ys: List[Term],
    subst: Subst,
) -> Optional[Subst]:
    """
    Helper for OpenListTerm unification with a concrete list.
    """
    if len(ys) < len(prefix):
        return None

    s2 = dict(subst)
    for x, y in zip(prefix, ys):
        s2 = unify_term(x, y, s2)
        if s2 is None:
            return None

    rest = ListTerm(list(ys[len(prefix) :]))
    s2 = unify_term(Var(tailv), rest, s2)
    if s2 is None:
        return None
    return s2


def unify_term(a: Term, b: Term, subst: Subst) -> Optional[Subst]:
    """
    Unify two terms under an existing substitution.
    Returns an extended substitution, or None if they can't match.
    """
    a = apply_subst_term(a, subst)
    b = apply_subst_term(b, subst)

    # Variable binding (either side)
    if isinstance(a, Var):
        v = a.name
        t = b
        if isinstance(t, Var) and t.name == v:
            return dict(subst)
        if contains_var_term(t, v):
            return None
        s2 = dict(subst)
        s2[v] = t
        return s2

    if isinstance(b, Var):
        return unify_term(b, a, subst)

    # Exact matches
    if isinstance(a, Iri) and isinstance(b, Iri) and a.value == b.value:
        return dict(subst)
    if isinstance(a, Literal) and isinstance(b, Literal) and a.value == b.value:
        return dict(subst)
    if isinstance(a, Blank) and isinstance(b, Blank) and a.label == b.label:
        return dict(subst)

    # Open list vs concrete list
    if isinstance(a, OpenListTerm) and isinstance(b, ListTerm):
        return unify_open_with_list(a.prefix, a.tail_var, b.elems, subst)
    if isinstance(a, ListTerm) and isinstance(b, OpenListTerm):
        return unify_open_with_list(b.prefix, b.tail_var, a.elems, subst)

    # Open list vs open list (same tail var required)
    if isinstance(a, OpenListTerm) and isinstance(b, OpenListTerm):
        if a.tail_var != b.tail_var or len(a.prefix) != len(b.prefix):
            return None
        s2 = dict(subst)
        for x, y in zip(a.prefix, b.prefix):
            s2 = unify_term(x, y, s2)
            if s2 is None:
                return None
        return s2

    # List element-wise unification
    if isinstance(a, ListTerm) and isinstance(b, ListTerm):
        if len(a.elems) != len(b.elems):
            return None
        s2 = dict(subst)
        for x, y in zip(a.elems, b.elems):
            s2 = unify_term(x, y, s2)
            if s2 is None:
                return None
        return s2

    # Formulas are treated as opaque unless exactly equal.
    if isinstance(a, FormulaTerm) and isinstance(b, FormulaTerm) and a.triples == b.triples:
        return dict(subst)

    return None


def unify_triple(pat: Triple, fact: Triple, subst: Subst) -> Optional[Subst]:
    s1 = unify_term(pat.s, fact.s, subst)
    if s1 is None:
        return None
    s2 = unify_term(pat.p, fact.p, s1)
    if s2 is None:
        return None
    s3 = unify_term(pat.o, fact.o, s2)
    return s3


def compose_subst(outer: Subst, delta: Subst) -> Optional[Subst]:
    """
    Combine an "outer" substitution with a delta-substitution coming from
    solving a single goal. If there is a conflicting binding we drop that
    solution.
    """
    if not delta:
        return dict(outer)
    out = dict(outer)
    for k, v in delta.items():
        if k in out:
            if out[k] != v:
                return None
        else:
            out[k] = v
    return out


# =====================================================================================
# BUILTINS
# =====================================================================================

from typing import Optional, Union

Number = Union[int, float]

def parse_number_literal(t: Term) -> Optional[Number]:
    """
    Try to interpret Term `t` as either an int or a float.

    Semantics:
      - Prefer integer parsing when the literal is a plain decimal integer
        (possibly with a leading '-'; typed or untyped).
      - Fall back to the existing float parsing for other numeric-looking literals.
      - Does *not* touch durations / dates – those still go through
        parse_num_or_duration where needed.
    """
    # 1) Exact integer mode (this already handles typed xsd:int-style literals)
    i = parse_int_literal(t)
    if i is not None:
        return i

    # 2) Fallback: normal numeric literal parsing (float)
    f = parse_num(t)
    if f is not None:
        return f

    return None


def parse_num(t: Term) -> Optional[float]:
    if isinstance(t, Literal):
        try:
            return float(t.value)
        except ValueError:
            return None
    return None


def parse_int_literal(t: Term) -> Optional[int]:
    """
    Parse a literal as an arbitrary-precision integer if it looks like
    a plain decimal integer (optionally with a leading '-').
    """
    if not isinstance(t, Literal):
        return None
    s = t.value
    lex, _dt = literal_parts(s)
    lex = strip_quotes(lex)

    if not lex:
        return None

    if all(c.isdigit() for c in lex) or (
        lex.startswith("-") and all(c.isdigit() for c in lex[1:])
    ):
        try:
            return int(lex, 10)
        except ValueError:
            return None
    return None


def format_num(n: float) -> str:
    if n.is_integer():
        return str(int(n))
    return repr(n)


def is_builtin_pred(p: Term) -> bool:
    return (
        isinstance(p, Iri)
        and (
            p.value.startswith(MATH_NS)
            or p.value.startswith(LOG_NS)
            or p.value.startswith(STRING_NS)
            or p.value.startswith(TIME_NS)
            or p.value.startswith(LIST_NS)
        )
    )


# ----- typed literal helpers (dates/durations) ----------------------------------------

def literal_parts(lit: str) -> Tuple[str, Optional[str]]:
    """
    Split a literal like `"foo"^^<xsd:string>` into (lex, datatypeIRI).
    """
    if "^^" in lit:
        idx = lit.index("^^")
        lex = lit[:idx]
        dt = lit[idx + 2 :].strip()
        if dt.startswith("<") and dt.endswith(">"):
            dt = dt[1:-1]
        return lex, dt
    return lit, None


def strip_quotes(lex: str) -> str:
    if len(lex) >= 2 and lex[0] == '"' and lex[-1] == '"':
        return lex[1:-1]
    return lex


def parse_xsd_date_term(t: Term) -> Optional[date]:
    if not isinstance(t, Literal):
        return None
    s = t.value
    lex, dt = literal_parts(s)
    val = strip_quotes(lex)
    if dt == XSD_NS + "date" or len(val) == 10:
        try:
            return date.fromisoformat(val)
        except ValueError:
            return None
    return None


def parse_xsd_datetime_term(t: Term) -> Optional[datetime]:
    if not isinstance(t, Literal):
        return None
    s = t.value
    lex, dt = literal_parts(s)
    val = strip_quotes(lex)
    if dt == XSD_NS + "dateTime" or "T" in val:
        try:
            # Python's fromisoformat handles "YYYY-MM-DDTHH:MM:SS+HH:MM"
            dt_obj = datetime.fromisoformat(val)
            # Normalize to UTC
            if dt_obj.tzinfo is None:
                dt_obj = dt_obj.replace(tzinfo=timezone.utc)
            return dt_obj.astimezone(timezone.utc)
        except ValueError:
            return None
    return None


def parse_datetime_like(t: Term) -> Optional[datetime]:
    d = parse_xsd_date_term(t)
    if d is not None:
        return datetime(d.year, d.month, d.day, tzinfo=timezone.utc)
    return parse_xsd_datetime_term(t)


def parse_iso8601_duration_to_seconds(s: str) -> Optional[float]:
    """
    Parse an ISO8601 duration like P80Y or P3DT4H into seconds (approx).
    We implement a very small parser good enough for eyeling’s use.
    """
    if not s:
        return None
    if s[0] != "P":
        return None

    it = iter(s[1:])
    num = ""
    in_time = False

    years = months = weeks = days = hours = minutes = seconds = 0.0

    for c in it:
        if c == "T":
            in_time = True
            continue
        if c.isdigit() or c == ".":
            num += c
            continue

        if not num:
            return None
        try:
            val = float(num)
        except ValueError:
            return None
        num = ""

        if not in_time and c == "Y":
            years += val
        elif not in_time and c == "M":
            months += val
        elif not in_time and c == "W":
            weeks += val
        elif not in_time and c == "D":
            days += val
        elif in_time and c == "H":
            hours += val
        elif in_time and c == "M":
            minutes += val
        elif in_time and c == "S":
            seconds += val
        else:
            return None

    # Approximate conversion to seconds.
    total_days = (
        years * 365.2425
        + months * 30.436875
        + weeks * 7.0
        + days
        + hours / 24.0
        + minutes / (24.0 * 60.0)
        + seconds / (24.0 * 3600.0)
    )
    return total_days * 86400.0


def parse_num_or_duration(t: Term) -> Optional[float]:
    n = parse_num(t)
    if n is not None:
        return n

    if isinstance(t, Literal):
        s = t.value
        lex, dt = literal_parts(s)
        val = strip_quotes(lex)

        if dt == XSD_NS + "duration" or val.startswith("P") or val.startswith("-P"):
            negative = val.startswith("-")
            core = val[1:] if negative else val
            secs = parse_iso8601_duration_to_seconds(core)
            if secs is None:
                return None
            return -secs if negative else secs

        dtval = parse_datetime_like(t)
        if dtval is not None:
            return dtval.timestamp()

    return None


def format_duration_literal_from_seconds(secs: float) -> Term:
    """
    Represent a duration in days as an xsd:duration literal PnD or -PnD.
    """
    neg = secs < 0
    abs_secs = abs(secs)
    days = int(round(abs_secs / 86400.0))
    if neg:
        lex = f"\"-P{days}D\""
    else:
        lex = f"\"P{days}D\""
    return Literal(f"{lex}^^<{XSD_NS}duration>")


def list_append_split(
    parts: List[Term], res_elems: List[Term], subst: Subst
) -> List[Subst]:
    """
    Relational list:append, following the N3 spec:
    ( $s.i?[*] )+ list:append $o?
    true iff `o` is the concatenation of all lists `s.i`.
    """
    if not parts:
        if not res_elems:
            return [dict(subst)]
        return []

    out: List[Subst] = []
    n = len(res_elems)

    for k in range(n + 1):
        left = ListTerm(list(res_elems[:k]))
        s1 = unify_term(parts[0], left, subst)
        if s1 is None:
            continue
        rest_elems = res_elems[k:]
        out.extend(list_append_split(parts[1:], list(rest_elems), s1))

    return out


# =====================================================================================
# Backward proof and builtins mutually recurse, so we declare the signatures first.
# =====================================================================================

def prove_goals(
    goals: List[Triple],
    subst: Subst,
    facts: List[Triple],
    back_rules: List[Rule],
    depth: int,
    visited: List[Triple],
    var_gen: List[int],
) -> List[Subst]:
    ...


def eval_builtin(
    goal: Triple,
    subst: Subst,
    facts: List[Triple],
    back_rules: List[Rule],
    depth: int,
    var_gen: List[int],
) -> List[Subst]:
    """
    Evaluate a builtin triple under current substitution.
    Returns zero or more new substitutions (for backtracking).

    Some builtins (e.g. log:collectAllIn) need to look at the current
    fact base and backward rules, so we thread those through.
    """
    g = apply_subst_triple(goal, subst)

    # -------------------------------------------------------------------------
    # time:localTime
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == TIME_NS + "localTime":
        # "" time:localTime ?D.  binds ?D to “now” as xsd:dateTime.
        now = datetime.now().astimezone().isoformat()
        if isinstance(g.o, Var):
            s2 = dict(subst)
            s2[g.o.name] = Literal(f"\"{now}\"^^<{XSD_NS}dateTime>")
            return [s2]
        if isinstance(g.o, Literal):
            lex_o, _ = literal_parts(g.o.value)
            if strip_quotes(lex_o) == now:
                return [dict(subst)]
        return []

    # -------------------------------------------------------------------------
    # math: comparisons (binary OR list form)
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "greaterThan":
        # Binary: A greaterThan B
        a = parse_num_or_duration(g.s)
        b = parse_num_or_duration(g.o)
        if a is not None and b is not None:
            return [dict(subst)] if a > b else []
        # List: (A B) greaterThan true
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num_or_duration(g.s.elems[0])
            b = parse_num_or_duration(g.s.elems[1])
            if a is not None and b is not None and a > b:
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "lessThan":
        a = parse_num_or_duration(g.s)
        b = parse_num_or_duration(g.o)
        if a is not None and b is not None:
            return [dict(subst)] if a < b else []
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num_or_duration(g.s.elems[0])
            b = parse_num_or_duration(g.s.elems[1])
            if a is not None and b is not None and a < b:
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "notLessThan":
        a = parse_num_or_duration(g.s)
        b = parse_num_or_duration(g.o)
        if a is not None and b is not None:
            return [dict(subst)] if a >= b else []
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num_or_duration(g.s.elems[0])
            b = parse_num_or_duration(g.s.elems[1])
            if a is not None and b is not None and a >= b:
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "notGreaterThan":
        a = parse_num_or_duration(g.s)
        b = parse_num_or_duration(g.o)
        if a is not None and b is not None:
            return [dict(subst)] if a <= b else []
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num_or_duration(g.s.elems[0])
            b = parse_num_or_duration(g.s.elems[1])
            if a is not None and b is not None and a <= b:
                return [dict(subst)]
        return []

    # -------------------------------------------------------------------------
    # math: arithmetic
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "sum":
        # (a b c) math:sum ?z
        if isinstance(g.s, ListTerm) and len(g.s.elems) >= 2:
            xs = g.s.elems

            # Use a generic number parser, but still prefer exact ints
            values: List[Number] = []
            for t in xs:
                v = parse_number_literal(t)
                if v is None:
                    # Not a numeric literal we understand
                    return []
                values.append(v)

            # All arguments are ints -> stay in integer land
            if all(isinstance(v, int) for v in values):
                total_int = sum(values)  # type: ignore[arg-type]
                lit = Literal(str(total_int))
            else:
                # Mixed or non-integer -> fall back to float semantics
                total_float = sum(float(v) for v in values)
                lit = Literal(format_num(total_float))

            if isinstance(g.o, Var):
                s2 = dict(subst)
                s2[g.o.name] = lit
                return [s2]

            s2 = unify_term(g.o, lit, subst)
            return [s2] if s2 is not None else []

        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "product":
        # (a b c) math:product ?z
        if isinstance(g.s, ListTerm) and len(g.s.elems) >= 2:
            xs = g.s.elems

            values: List[Number] = []
            for t in xs:
                v = parse_number_literal(t)
                if v is None:
                    return []
                values.append(v)

            if all(isinstance(v, int) for v in values):
                prod_int = 1
                for v in values:
                    prod_int *= v  # type: ignore[operator]
                lit = Literal(str(prod_int))
            else:
                prod_float = 1.0
                for v in values:
                    prod_float *= float(v)
                lit = Literal(format_num(prod_float))

            if isinstance(g.o, Var):
                s2 = dict(subst)
                s2[g.o.name] = lit
                return [s2]
            if isinstance(g.o, Literal) and g.o.value == lit.value:
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "difference":
        # (?A ?B) math:difference ?C
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a0, b0 = g.s.elems

            # Big integer difference for integer literals
            ai = parse_int_literal(a0)
            bi = parse_int_literal(b0)
            if ai is not None and bi is not None:
                ci = ai - bi
                lit = Literal(str(ci))
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = lit
                    return [s2]
                else:
                    s2 = unify_term(g.o, lit, subst)
                    return [s2] if s2 is not None else []

            # Numeric difference via floats
            a = parse_num(a0)
            b = parse_num(b0)
            if a is not None and b is not None:
                c = a - b
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = Literal(format_num(c))
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == format_num(c):
                    return [dict(subst)]

            # Date/datetime difference -> duration
            a_dt = parse_datetime_like(a0)
            b_dt = parse_datetime_like(b0)
            if a_dt is not None and b_dt is not None:
                diff = a_dt - b_dt
                secs = diff.total_seconds()
                dur_term = format_duration_literal_from_seconds(secs)
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = dur_term
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == dur_term.value:
                    return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "quotient":
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num(g.s.elems[0])
            b = parse_num(g.s.elems[1])
            if a is not None and b is not None and b != 0.0:
                c = a / b
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = Literal(format_num(c))
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == format_num(c):
                    return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "exponentiation":
        # (?A ?B) exponentiation ?C  =>  C = A^B
        if isinstance(g.s, ListTerm) and len(g.s.elems) == 2:
            a = parse_num(g.s.elems[0])
            b0 = g.s.elems[1]
            c = parse_num(g.o)
            if a is not None and isinstance(b0, Literal):
                b = parse_num(b0)
            else:
                b = None

            if a is not None and b is not None:
                c_val = a ** b
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = Literal(format_num(c_val))
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == format_num(c_val):
                    return [dict(subst)]

            # Inverse mode for exponent:
            # (A ?B) exponentiation C => B = ln(C)/ln(A)
            if a is not None and isinstance(b0, Var) and c is not None:
                if a > 0.0 and a != 1.0 and c > 0.0:
                    b_val = math.log(c) / math.log(a)
                    s2 = dict(subst)
                    s2[b0.name] = Literal(format_num(b_val))
                    return [s2]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "negation":
        # x negation ?y => y = -x
        a = parse_num(g.s)
        if a is not None and isinstance(g.o, Var):
            s2 = dict(subst)
            s2[g.o.name] = Literal(format_num(-a))
            return [s2]
        # ?x negation y => x = -y
        b = parse_num(g.o)
        if isinstance(g.s, Var) and b is not None:
            s2 = dict(subst)
            s2[g.s.name] = Literal(format_num(-b))
            return [s2]
        # ground check
        a2 = parse_num(g.s)
        b2 = parse_num(g.o)
        if a2 is not None and b2 is not None:
            if abs((-a2) - b2) < 1e-9:
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "absoluteValue":
        a = parse_num(g.s)
        if a is not None and isinstance(g.o, Var):
            s2 = dict(subst)
            s2[g.o.name] = Literal(format_num(abs(a)))
            return [s2]
        if a is not None and (b := parse_num(g.o)) is not None:
            if abs(abs(a) - b) < 1e-9:
                return [dict(subst)]
        return []

    # Trig builtins
    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "cos":
        a = parse_num(g.s)
        if a is not None:
            c_val = math.cos(a)
            if isinstance(g.o, Var):
                s2 = dict(subst)
                s2[g.o.name] = Literal(format_num(c_val))
                return [s2]
            if isinstance(g.o, Literal) and g.o.value == format_num(c_val):
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "sin":
        a = parse_num(g.s)
        if a is not None:
            c_val = math.sin(a)
            if isinstance(g.o, Var):
                s2 = dict(subst)
                s2[g.o.name] = Literal(format_num(c_val))
                return [s2]
            if isinstance(g.o, Literal) and g.o.value == format_num(c_val):
                return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "acos":
        a = parse_num(g.s)
        if a is not None:
            c_val = math.acos(a)
            if math.isfinite(c_val):
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = Literal(format_num(c_val))
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == format_num(c_val):
                    return [dict(subst)]
        return []

    if isinstance(g.p, Iri) and g.p.value == MATH_NS + "asin":
        a = parse_num(g.s)
        if a is not None:
            c_val = math.asin(a)
            if math.isfinite(c_val):
                if isinstance(g.o, Var):
                    s2 = dict(subst)
                    s2[g.o.name] = Literal(format_num(c_val))
                    return [s2]
                if isinstance(g.o, Literal) and g.o.value == format_num(c_val):
                    return [dict(subst)]
        return []

    # -------------------------------------------------------------------------
    # log: equality builtins
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LOG_NS + "equalTo":
        # Relational log:equalTo: succeeds iff subject and object can be made
        # equal by extending the current substitution.
        s2 = unify_term(goal.s, goal.o, subst)
        return [s2] if s2 is not None else []

    if isinstance(g.p, Iri) and g.p.value == LOG_NS + "notEqualTo":
        # log:notEqualTo is the exact complement: it succeeds iff there is
        # *no* unifier for subject and object under the current substitution.
        s2 = unify_term(goal.s, goal.o, subst)
        if s2 is not None:
            return []
        return [dict(subst)]

    # -------------------------------------------------------------------------
    # log:notIncludes  (Scoped Negation As Failure)
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LOG_NS + "notIncludes":
        # ?Scope log:notIncludes { pattern } .
        # Object must be a quoted formula { ... }.
        if not isinstance(g.o, FormulaTerm):
            return []
        body = g.o.triples

        if depth >= MAX_BACKWARD_DEPTH:
            return []

        visited2: List[Triple] = []
        sols = prove_goals(
            list(body),
            {},
            facts,
            back_rules,
            depth + 1,
            visited2,
            var_gen,
        )
        if not sols:
            # No way to prove all triples in {body} → notIncludes holds.
            return [dict(subst)]
        else:
            return []

    # -------------------------------------------------------------------------
    # log:collectAllIn
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LOG_NS + "collectAllIn":
        # (?V { clause } ?List) log:collectAllIn ?Scope.
        if not isinstance(g.s, ListTerm) or len(g.s.elems) != 3:
            return []
        value_templ, clause_term, list_term = g.s.elems

        if not isinstance(clause_term, FormulaTerm):
            return []

        body = clause_term.triples

        if depth >= MAX_BACKWARD_DEPTH:
            return []

        visited2: List[Triple] = []
        sols = prove_goals(
            list(body),
            {},
            facts,
            back_rules,
            depth + 1,
            visited2,
            var_gen,
        )

        # Collect instantiated values, preserving order and removing simple duplicates.
        collected: List[Term] = []
        for s_body in sols:
            v = apply_subst_term(value_templ, s_body)
            if v not in collected:
                collected.append(v)

        collected_list = ListTerm(collected)
        out: List[Subst] = []

        if isinstance(list_term, (Var, ListTerm, OpenListTerm)):
            s2 = unify_term(list_term, collected_list, subst)
            if s2 is not None:
                out.append(s2)
        else:
            if unify_term(list_term, collected_list, subst) is not None:
                out.append(dict(subst))
        return out

    # -------------------------------------------------------------------------
    # list:append
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "append":
        if not isinstance(g.s, ListTerm):
            return []
        parts = g.s.elems

        if isinstance(g.o, ListTerm):
            # Relational mode: object is a (possibly non-ground) list.
            return list_append_split(parts, g.o.elems, subst)

        # Functional mode: subject is list-of-lists, object is anything
        # (typically a variable). Here we just concatenate all subject lists.
        out_elems: List[Term] = []
        for part in parts:
            if not isinstance(part, ListTerm):
                return []
            out_elems.extend(part.elems)
        result = ListTerm(out_elems)

        if isinstance(g.o, Var):
            s2 = dict(subst)
            s2[g.o.name] = result
            return [s2]
        if g.o == result:
            return [dict(subst)]
        return []

    # -------------------------------------------------------------------------
    # list:firstRest  (experimental, bidirectional, open tail support)
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "firstRest":
        # Forward split of a concrete list.
        if isinstance(g.s, ListTerm):
            if not g.s.elems:
                return []
            first = g.s.elems[0]
            rest = ListTerm(list(g.s.elems[1:]))
            pair = ListTerm([first, rest])
            s2 = unify_term(g.o, pair, subst)
            return [s2] if s2 is not None else []

        # Inverse construction from (first rest).
        if isinstance(g.o, ListTerm) and len(g.o.elems) == 2:
            first = g.o.elems[0]
            rest = g.o.elems[1]

            if isinstance(rest, ListTerm):
                xs = [first] + list(rest.elems)
                constructed = ListTerm(xs)
                s2 = unify_term(g.s, constructed, subst)
                return [s2] if s2 is not None else []

            if isinstance(rest, Var):
                constructed = OpenListTerm([first], rest.name)
                s2 = unify_term(g.s, constructed, subst)
                return [s2] if s2 is not None else []

            if isinstance(rest, OpenListTerm):
                new_prefix = [first] + list(rest.prefix)
                constructed = OpenListTerm(new_prefix, rest.tail_var)
                s2 = unify_term(g.s, constructed, subst)
                return [s2] if s2 is not None else []

        return []

    # -------------------------------------------------------------------------
    # list:member / list:in / list:length / list:map / list:notMember / list:reverse / list:sort
    # -------------------------------------------------------------------------
    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "member":
        if not isinstance(g.s, ListTerm):
            return []
        outs: List[Subst] = []
        for x in g.s.elems:
            s2 = unify_term(g.o, x, subst)
            if s2 is not None:
                outs.append(s2)
        return outs

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "in":
        if not isinstance(g.o, ListTerm):
            return []
        outs: List[Subst] = []
        for x in g.o.elems:
            s2 = unify_term(g.s, x, subst)
            if s2 is not None:
                outs.append(s2)
        return outs

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "length":
        if not isinstance(g.s, ListTerm):
            return []
        n_term = Literal(str(len(g.s.elems)))
        s2 = unify_term(g.o, n_term, subst)
        return [s2] if s2 is not None else []

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "notMember":
        if not isinstance(g.s, ListTerm):
            return []
        for el in g.s.elems:
            if unify_term(g.o, el, subst) is not None:
                return []
        return [dict(subst)]

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "reverse":
        # One side must be a closed list; the other side is that list reversed.
        if isinstance(g.s, ListTerm):
            rev = list(reversed(g.s.elems))
            rterm = ListTerm(rev)
            s2 = unify_term(g.o, rterm, subst)
            return [s2] if s2 is not None else []
        if isinstance(g.o, ListTerm):
            rev = list(reversed(g.o.elems))
            rterm = ListTerm(rev)
            s2 = unify_term(g.s, rterm, subst)
            return [s2] if s2 is not None else []
        return []

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "sort":
        # ?List list:sort ?Sorted.
        from functools import cmp_to_key

        def cmp_term_for_sort(a: Term, b: Term) -> int:
            # Numeric comparison for literal numbers, lexicographic fallback.
            if isinstance(a, Literal) and isinstance(b, Literal):
                lex_a, _ = literal_parts(a.value)
                lex_b, _ = literal_parts(b.value)
                sa = strip_quotes(lex_a)
                sb = strip_quotes(lex_b)
                try:
                    na = float(sa)
                    nb = float(sb)
                    if na < nb:
                        return -1
                    if na > nb:
                        return 1
                    return 0
                except ValueError:
                    if sa < sb:
                        return -1
                    if sa > sb:
                        return 1
                    return 0

            if isinstance(a, ListTerm) and isinstance(b, ListTerm):
                xs = a.elems
                ys = b.elems
                i = 0
                while True:
                    if i >= len(xs) and i >= len(ys):
                        return 0
                    if i >= len(xs):
                        return -1
                    if i >= len(ys):
                        return 1
                    c = cmp_term_for_sort(xs[i], ys[i])
                    if c != 0:
                        return c
                    i += 1

            if isinstance(a, Iri) and isinstance(b, Iri):
                if a.value < b.value:
                    return -1
                if a.value > b.value:
                    return 1
                return 0

            # Lists before non-lists
            if isinstance(a, ListTerm) and not isinstance(b, ListTerm):
                return -1
            if not isinstance(a, ListTerm) and isinstance(b, ListTerm):
                return 1

            sa = repr(a)
            sb = repr(b)
            if sa < sb:
                return -1
            if sa > sb:
                return 1
            return 0

        if isinstance(g.s, ListTerm):
            input_list = g.s.elems
        elif isinstance(g.o, ListTerm):
            input_list = g.o.elems
        else:
            return []

        if not all(is_ground_term(e) for e in input_list):
            return []

        sorted_list = sorted(input_list, key=cmp_to_key(cmp_term_for_sort))
        sorted_term = ListTerm(sorted_list)

        if isinstance(g.s, ListTerm):
            s2 = unify_term(g.o, sorted_term, subst)
            return [s2] if s2 is not None else []
        if isinstance(g.o, ListTerm):
            s2 = unify_term(g.s, sorted_term, subst)
            return [s2] if s2 is not None else []
        return []

    if isinstance(g.p, Iri) and g.p.value == LIST_NS + "map":
        # Pragmatic eyeling subset of list:map:
        #   ((inputList) predicateIRI) list:map outputList
        if not isinstance(g.s, ListTerm) or len(g.s.elems) != 2:
            return []
        args = g.s.elems
        input_term = args[0]
        pred_term = args[1]

        if not isinstance(input_term, ListTerm):
            return []
        input_list = input_term.elems

        if not isinstance(pred_term, Iri):
            return []
        pred = Iri(pred_term.value)
        if not is_builtin_pred(pred):
            return []
        if not all(is_ground_term(e) for e in input_list):
            return []

        results: List[Term] = []
        for el in input_list:
            yvar = Var("_mapY")
            goal2 = Triple(el, pred, yvar)
            sols = eval_builtin(goal2, subst, facts, back_rules, depth + 1, var_gen)
            if not sols:
                return []
            yval = apply_subst_term(yvar, sols[0])
            if isinstance(yval, Var):
                return []
            results.append(yval)

        out_list = ListTerm(results)
        s2 = unify_term(g.o, out_list, subst)
        return [s2] if s2 is not None else []

    # Unknown builtin: fail.
    return []


# =====================================================================================
# Backward proof (SLD-style)
# =====================================================================================

def standardize_rule(rule: Rule, gen: List[int]) -> Rule:
    """
    Standardize a rule apart: rename all variables in the rule to fresh ones
    so different uses of the same rule don't clash.
    """

    def rename_term(
        t: Term,
        vmap: Dict[str, str],
        gen: List[int],
    ) -> Term:
        if isinstance(t, Var):
            if t.name not in vmap:
                name = f"{t.name}__{gen[0]}"
                gen[0] += 1
                vmap[t.name] = name
            return Var(vmap[t.name])

        if isinstance(t, ListTerm):
            return ListTerm([rename_term(e, vmap, gen) for e in t.elems])

        if isinstance(t, OpenListTerm):
            new_xs = [rename_term(e, vmap, gen) for e in t.prefix]
            if t.tail_var not in vmap:
                name = f"{t.tail_var}__{gen[0]}"
                gen[0] += 1
                vmap[t.tail_var] = name
            new_tail = vmap[t.tail_var]
            return OpenListTerm(new_xs, new_tail)

        if isinstance(t, FormulaTerm):
            return FormulaTerm(
                [
                    Triple(
                        rename_term(tr.s, vmap, gen),
                        rename_term(tr.p, vmap, gen),
                        rename_term(tr.o, vmap, gen),
                    )
                    for tr in t.triples
                ]
            )

        return t

    vmap2: Dict[str, str] = {}
    premise = [
        Triple(
            rename_term(tr.s, vmap2, gen),
            rename_term(tr.p, vmap2, gen),
            rename_term(tr.o, vmap2, gen),
        )
        for tr in rule.premise
    ]
    conclusion = [
        Triple(
            rename_term(tr.s, vmap2, gen),
            rename_term(tr.p, vmap2, gen),
            rename_term(tr.o, vmap2, gen),
        )
        for tr in rule.conclusion
    ]
    return Rule(
        premise=premise,
        conclusion=conclusion,
        is_forward=rule.is_forward,
        is_fuse=rule.is_fuse,
    )


def solve_single_goal(
    goal: Triple,
    facts: List[Triple],
    back_rules: List[Rule],
    depth: int,
    visited: List[Triple],
    var_gen: List[int],
) -> List[Subst]:
    """
    Solve a single goal triple under an *empty* substitution.
    """

    # Builtins are pure. Evaluate them directly (no loop check).
    if is_builtin_pred(goal.p):
        return eval_builtin(goal, {}, facts, back_rules, depth, var_gen)

    if depth > MAX_BACKWARD_DEPTH:
        return []

    # Loop check to avoid trivial cycles like ?X :p ?Y <= {?X :p ?Y}
    if goal in visited:
        return []

    visited.append(goal)
    results: List[Subst] = []

    # 1) Try matching known facts, starting from an empty substitution.
    for f in facts:
        s2 = unify_triple(goal, f, {})
        if s2 is not None:
            results.append(s2)

    # 2) Try backward rules (Horn head must be one triple).
    for r in back_rules:
        if len(r.conclusion) != 1:
            continue

        r_std = standardize_rule(r, var_gen)
        head = r_std.conclusion[0]

        s2 = unify_triple(head, goal, {})
        if s2 is None:
            continue

        # Instantiate the body under the head substitution s2.
        body = [apply_subst_triple(b, s2) for b in r_std.premise]

        # Prove the body starting from s2. Any solution is a delta
        # substitution for this goal (w.r.t. an empty outer subst).
        body_solutions = prove_goals(
            body, s2, facts, back_rules, depth + 1, visited, var_gen
        )
        results.extend(body_solutions)

    visited.pop()
    return results


def prove_goals(
    goals: List[Triple],
    subst: Subst,
    facts: List[Triple],
    back_rules: List[Rule],
    depth: int,
    visited: List[Triple],
    var_gen: List[int],
) -> List[Subst]:
    """
    Prove a conjunction of goals under an *outer* substitution, using
    solve_single_goal for the first goal and then recursing on the rest.
    """
    if not goals:
        return [dict(subst)]
    if depth > MAX_BACKWARD_DEPTH:
        return []

    goal0 = apply_subst_triple(goals[0], subst)
    rest = goals[1:]

    results: List[Subst] = []

    deltas = solve_single_goal(goal0, facts, back_rules, depth, visited, var_gen)
    for delta in deltas:
        composed = compose_subst(subst, delta)
        if composed is None:
            continue
        if not rest:
            results.append(composed)
        else:
            tail_solutions = prove_goals(
                rest,
                composed,
                facts,
                back_rules,
                depth + 1,
                visited,
                var_gen,
            )
            results.extend(tail_solutions)

    return results


# =====================================================================================
# Forward chaining to fixpoint
# =====================================================================================

def forward_chain(
    facts: List[Triple],
    forward_rules: List[Rule],
    back_rules: List[Rule],
) -> List[DerivedFact]:
    """
    Forward chaining to fixpoint.

    - We keep a database of ground facts.
    - We repeatedly fire forward rules whose premises are provable
      (using facts + backward rules + builtins).
    - We collect all newly derived forward facts together with a
      short justification (which rule fired with which premises).
    """
    # Use a simple list for accumulating facts; we avoid using Triple as a
    # set/dict key because some triples contain list-valued terms.
    fact_list: List[Triple] = list(facts)

    derived_forward: List[DerivedFact] = []
    var_gen = [0]          # global var name seed
    skolem_counter = [0]   # _:sk_N counter

    while True:
        changed = False
        i = 0

        # We may add new forward/backward rules while looping, so iterate by index.
        while i < len(forward_rules):
            r = forward_rules[i]
            i += 1

            empty: Subst = {}
            visited: List[Triple] = []

            sols = prove_goals(
                list(r.premise),
                empty,
                facts,
                back_rules,
                0,
                visited,
                var_gen,
            )

            # Inference fuse handling
            if r.is_fuse and sols:
                print("# Inference fuse triggered: a { ... } => false. rule fired.")
                sys.exit(2)

            for s in sols:
                instantiated_premises = [apply_subst_triple(b, s) for b in r.premise]

                # New head existentials per rule application:
                blank_map: Dict[str, str] = {}

                for cpat in r.conclusion:
                    instantiated = apply_subst_triple(cpat, s)

                    # --- rule-producing conclusions ---------------------------------
                    is_fw_rule_triple = (
                        is_log_implies(instantiated.p)
                        and isinstance(instantiated.s, FormulaTerm)
                        and isinstance(instantiated.o, FormulaTerm)
                    )
                    is_bw_rule_triple = (
                        is_log_implied_by(instantiated.p)
                        and isinstance(instantiated.s, FormulaTerm)
                        and isinstance(instantiated.o, FormulaTerm)
                    )

                    if is_fw_rule_triple or is_bw_rule_triple:
                        # 1) Keep the triple itself as derived output, even if non-ground,
                        #    so it shows up in the final printing.
                        if (
                            instantiated not in fact_list
                            and not has_alpha_equiv(fact_list, instantiated)
                        ):
                            fact_list.append(instantiated)
                            facts.append(instantiated)
                            derived_forward.append(
                                DerivedFact(
                                    fact=instantiated,
                                    rule=r,
                                    premises=list(instantiated_premises),
                                    subst=dict(s),
                                )
                            )
                            changed = True

                        # 2) Turn it into a *live* rule (forward or backward).
                        if isinstance(instantiated.s, FormulaTerm) and isinstance(
                            instantiated.o, FormulaTerm
                        ):
                            left = instantiated.s.triples
                            right = instantiated.o.triples

                            if is_fw_rule_triple:
                                # { left } log:implies { right } ≅ { left } => { right }
                                premise, conclusion = lift_blank_rule_vars(
                                    left, right
                                )
                                new_rule = Rule(
                                    premise=premise,
                                    conclusion=conclusion,
                                    is_forward=True,
                                    is_fuse=False,
                                )

                                already_there = any(
                                    rr.is_forward == new_rule.is_forward
                                    and rr.is_fuse == new_rule.is_fuse
                                    and rr.premise == new_rule.premise
                                    and rr.conclusion == new_rule.conclusion
                                    for rr in forward_rules
                                )
                                if not already_there:
                                    forward_rules.append(new_rule)

                            elif is_bw_rule_triple:
                                # { left } log:impliedBy { right } ≅ { left } <= { right }
                                # Backward rule: head = left, body = right
                                # Internally: premise = body, conclusion = head
                                premise, conclusion = lift_blank_rule_vars(
                                    right, left
                                )
                                new_rule = Rule(
                                    premise=premise,
                                    conclusion=conclusion,
                                    is_forward=False,
                                    is_fuse=False,
                                )

                                already_there = any(
                                    rr.is_forward == new_rule.is_forward
                                    and rr.is_fuse == new_rule.is_fuse
                                    and rr.premise == new_rule.premise
                                    and rr.conclusion == new_rule.conclusion
                                    for rr in back_rules
                                )
                                if not already_there:
                                    back_rules.append(new_rule)

                        # Skip normal fact handling for rule triples.
                        continue

                    # --- normal fact conclusion -----------------------------------
                    inst = skolemize_triple(
                        instantiated, blank_map, skolem_counter
                    )

                    # Only add fully ground facts (no variables/OpenList)
                    if not is_ground_triple(inst):
                        continue

                    # Avoid duplicates up to blank renaming.
                    if inst in fact_list or has_alpha_equiv(fact_list, inst):
                        continue

                    fact_list.append(inst)
                    facts.append(inst)
                    derived_forward.append(
                        DerivedFact(
                            fact=inst,
                            rule=r,
                            premises=list(instantiated_premises),
                            subst=dict(s),
                        )
                    )
                    changed = True

        if not changed:
            break

    return derived_forward


# =====================================================================================
# Pretty printing as N3/Turtle
# =====================================================================================

def term_to_n3(t: Term, pref: PrefixEnv) -> str:
    if isinstance(t, Iri):
        i = t.value
        q = pref.shrink_iri(i)
        if q is not None:
            return q
        if i.startswith("_:"):
            return i
        return f"<{i}>"

    if isinstance(t, Literal):
        return t.value

    if isinstance(t, Var):
        return f"?{t.name}"

    if isinstance(t, Blank):
        return t.label

    if isinstance(t, ListTerm):
        inside = [term_to_n3(e, pref) for e in t.elems]
        return "(" + " ".join(inside) + ")"

    if isinstance(t, OpenListTerm):
        inside = [term_to_n3(e, pref) for e in t.prefix]
        inside.append(f"?{t.tail_var}")
        return "(" + " ".join(inside) + ")"

    if isinstance(t, FormulaTerm):
        s = "{\n"
        for tr in t.triples:
            line = triple_to_n3(tr, pref)
            line = line.rstrip()
            if line:
                s += "    " + line + "\n"
        s += "}"
        return s

    return repr(t)


def triple_to_n3(tr: Triple, prefixes: PrefixEnv) -> str:
    # Pretty-print rule triples of the form:
    #   { ... } log:implies { ... }   as   { ... } => { ... } .
    if is_log_implies(tr.p):
        if isinstance(tr.s, FormulaTerm) and isinstance(tr.o, FormulaTerm):
            prem_s = term_to_n3(FormulaTerm(tr.s.triples), prefixes)
            concl_s = term_to_n3(FormulaTerm(tr.o.triples), prefixes)
            return f"{prem_s} => {concl_s} ."

    if is_log_implied_by(tr.p):
        if isinstance(tr.s, FormulaTerm) and isinstance(tr.o, FormulaTerm):
            head_s = term_to_n3(FormulaTerm(tr.s.triples), prefixes)
            body_s = term_to_n3(FormulaTerm(tr.o.triples), prefixes)
            return f"{head_s} <= {body_s} ."

    s = term_to_n3(tr.s, prefixes)
    if is_rdf_type_pred(tr.p):
        p = "a"
    else:
        p = term_to_n3(tr.p, prefixes)
    o = term_to_n3(tr.o, prefixes)
    return f"{s} {p} {o} ."


def print_explanation(df: DerivedFact, prefixes: PrefixEnv) -> None:
    """
    Pretty-print a derived fact together with a small mathematical-English proof
    as N3 comments. The triple itself is **not** printed here; caller prints it.
    """
    print("# ----------------------------------------------------------------------")
    print("# Proof for derived triple:")
    for line in triple_to_n3(df.fact, prefixes).splitlines():
        trimmed = line.rstrip()
        if trimmed:
            print(f"#   {trimmed}")

    if not df.premises:
        print("# This triple is the head of a forward rule with an empty premise,")
        print("# so it holds unconditionally whenever the program is loaded.")
    else:
        print("# It holds because the following instantiated premises are all satisfied:")
        for prem in df.premises:
            for line in triple_to_n3(prem, prefixes).splitlines():
                trimmed = line.rstrip()
                if trimmed:
                    print(f"#   {trimmed}")

    print("# via the schematic forward rule:")
    print("#   {")
    for tr in df.rule.premise:
        for line in triple_to_n3(tr, prefixes).splitlines():
            trimmed = line.rstrip()
            if trimmed:
                print(f"#     {trimmed}")
    print("#   } => {")
    for tr in df.rule.conclusion:
        for line in triple_to_n3(tr, prefixes).splitlines():
            trimmed = line.rstrip()
            if trimmed:
                print(f"#     {trimmed}")
    print("#   } .")

    rule_vars = vars_in_rule(df.rule)

    # Only show variables that actually occur in *this* rule,
    # but print their fully instantiated values (follow chains).
    visible_names = sorted(
        name for name in df.subst.keys() if name in rule_vars
    )

    if visible_names:
        print("# with substitution (on rule variables):")
        for v in visible_names:
            # Start from the variable itself and chase its binding to a fixed point
            full_term = apply_subst_term(Var(v), df.subst)
            print(f"#   ?{v} = {term_to_n3(full_term, prefixes)}")

    print("# Therefore the derived triple above is entailed by the rules and facts.")
    print("# ----------------------------------------------------------------------")


# =====================================================================================
# CLI entry point
# =====================================================================================

def main() -> None:
    # Command-line interface, mirroring the Rust version.
    args = sys.argv
    if len(args) != 2:
        print("Usage: eyeling <file.n3>", file=sys.stderr)
        sys.exit(1)

    path = args[1]
    try:
        with open(path, "r", encoding="utf-8") as f:
            text = f.read()
    except OSError as e:
        print(f"Error reading file {path!r}: {e}", file=sys.stderr)
        sys.exit(1)

    toks = lex(text)
    parser = Parser(toks)
    prefixes, triples, frules, brules = parser.parse_document()

    # Keep only ground input facts for the forward database.
    facts = [tr for tr in triples if is_ground_triple(tr)]

    # Run the engine!
    derived = forward_chain(facts, frules, brules)

    # Collect just the triples for prefix analysis.
    derived_triples = [df.fact for df in derived]

    # Print only prefixes needed by derived output.
    used_prefixes = prefixes.prefixes_used_for_output(derived_triples)
    for pfx, base in used_prefixes:
        if pfx == "":
            print(f"@prefix : <{base}> .")
        else:
            print(f"@prefix {pfx}: <{base}> .")
    if derived and used_prefixes:
        print()

    # Print derived triples interlaced with comment proofs.
    for df in derived:
        print_explanation(df, prefixes)
        print(triple_to_n3(df.fact, prefixes))
        print()


if __name__ == "__main__":
    main()

