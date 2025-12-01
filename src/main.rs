// =====================================================================================
// eyeling — a minimal Notation3 (N3) reasoner in Rust
// =====================================================================================
//
// This file is intentionally self-contained: we keep everything in main.rs so that
// the project is easy to hack on. If you want to grow this into a crate, the
// natural split points are: lexer, parser/AST, unification, reasoner, builtins, CLI.
//
// High-level pipeline:
//
//   1) Read an N3 file from disk.
//   2) Lex it into Tokens.
//   3) Parse tokens into:
//        - ground triples (facts)
//        - forward rules  {premise} => {conclusion}.
//        - backward rules {head} <= {body}.
//   4) Run forward chaining to fixpoint.
//        - premises are proven using backward rules + builtins.
//   5) Print only newly derived forward facts.
//
// The implementation is a pragmatic subset of N3. It is not a full W3C N3 parser.
// The goal is to be small, understandable, and useful.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;
// We use chrono only for time/date builtins (time:localTime, math:difference on dates).
use chrono::{DateTime, Local, NaiveDate, TimeZone, Utc};
use num_bigint::BigInt;

/// Namespace constants we expand QNames against.
/// Rust tip: `const` is compile-time and has no runtime cost.
const RDF_NS: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS_NS: &str = "http://www.w3.org/2000/01/rdf-schema#";
const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";
const LOG_NS: &str = "http://www.w3.org/2000/10/swap/log#";
const MATH_NS: &str = "http://www.w3.org/2000/10/swap/math#";
const STRING_NS: &str = "http://www.w3.org/2000/10/swap/string#";
const LIST_NS: &str = "http://www.w3.org/2000/10/swap/list#";
const TIME_NS: &str = "http://www.w3.org/2000/10/swap/time#";

/// Safety valve so backward proof doesn’t loop forever in degenerate cases.
const MAX_BACKWARD_DEPTH: usize = 50000;

// =====================================================================================
// AST (Abstract Syntax Tree)
// =====================================================================================

/// A term is any RDF-ish thing that can appear as subject, predicate, or object.
///
/// We intentionally keep this small. N3 has more constructs, but these cover:
/// - IRIs
/// - Literals (numbers, strings, booleans, typed literals)
/// - Variables ?x
/// - Blank nodes []
/// - Lists (...)
/// - OpenLists (internal helper for bidirectional list:firstRest)
/// - Quoted formulas { ... } (as conjunctions of triple patterns)
///
/// Rust tip: `enum` lets us model a “sum type” (one of many possibilities).
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Term {
    /// Expanded IRI (we store it as a normal String).
    Iri(String),

    /// Literal lexical form, kept raw.
    /// Examples:
    ///   "foo"
    ///   12
    ///   true
    ///   "1944-08-21"^^<http://www.w3.org/2001/XMLSchema#date>
    Literal(String),

    /// Variable name *without* the leading `?`.
    Var(String),

    /// Blank node identifier we invent, like _:b1.
    Blank(String),

    /// Proper closed list: (a b c)
    List(Vec<Term>),

    /// Internal open list: fixed prefix + tail variable (like Prolog [H|T]).
    /// This is needed for bidirectional list:firstRest.
    ///
    /// Example internal state:
    ///   OpenList([?H], "T")  means  (?H ?T)
    /// but the tail ?T is not yet known.
    ///
    /// Once ?T becomes a real List, we "close" it into a List.
    OpenList(Vec<Term>, String),

    /// Quoted formula = a conjunction of triple patterns inside `{ ... }`.
    /// N3 allows nested formulas/rules, but in this subset formulas are flat.
    Formula(Vec<Triple>),
}

/// A triple pattern / RDF triple.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Triple {
    s: Term,
    p: Term,
    o: Term,
}

/// A Horn-like rule.
/// - `premise` is a conjunction.
/// - `conclusion` is a conjunction.
/// - `is_forward`: true for =>, false for <=.
#[derive(Clone, Debug)]
struct Rule {
    premise: Vec<Triple>,
    conclusion: Vec<Triple>,
    is_forward: bool,
    /// { ... } => false.   (inference fuse / constraint)
    is_fuse: bool,
}

/// Substitution mapping variable name -> term.
/// Rust tip: `type Foo = ...` makes a readable alias.
type Subst = HashMap<String, Term>;

/// One forward-derived fact together with a simple justification.
#[derive(Clone, Debug)]
struct DerivedFact {
    /// The ground triple that was finally added to the fact base.
    fact: Triple,
    /// The forward rule (in schematic form) that produced this triple.
    rule: Rule,
    /// The rule body instantiated with the substitution that fired the rule.
    premises: Vec<Triple>,
    /// The substitution used when the rule fired.
    subst: Subst,
}

/// Tiny memo table for backward goals during one forward-rule proof.
type GoalCache = HashMap<Triple, Vec<Subst>>;

// =====================================================================================
// LEXER
// =====================================================================================

/// Token kinds in our small grammar.
/// Rust tip: enums can carry data (Ident(String), Literal(String), ...).
#[derive(Clone, Debug, PartialEq)]
enum TokenKind {
    AtPrefix,
    AtBase,
    OpImplies,    // =>
    OpImpliedBy,  // <=
    LBrace, RBrace,
    LParen, RParen,
    LBracket, RBracket,
    Semicolon,
    Comma,
    Dot,
    Ident(String),   // QName / bareword / keyword
    IriRef(String),  // <...>
    Var(String),     // ?x
    Literal(String), // numbers, booleans, "strings"
    HatHat,          // ^^ datatype operator (used after a literal)
    EOF,
}

/// A token with just one field. We keep it a struct for extensibility.
#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
}

/// Helper: whitespace?
fn is_ws(c: char) -> bool {
    c.is_whitespace()
}

/// Helper: characters allowed in identifiers (QName-ish).
fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '-' || c == ':'
}

/// Lex a whole file into a Vec<Token>.
///
/// This is a *simple hand-written lexer*:
/// - We scan left-to-right using a peekable iterator.
/// - We emit tokens as we go.
/// - We skip whitespace and comments.
/// - Errors panic with a message (fine for a toy reasoner).
fn lex(input: &str) -> Vec<Token> {
    let mut chars = input.chars().peekable();
    let mut tokens = Vec::new();

    while let Some(&c) = chars.peek() {
        // 1) Skip whitespace
        if is_ws(c) {
            chars.next();
            continue;
        }

        // 2) Skip # comments to end of line
        if c == '#' {
            while let Some(cc) = chars.next() {
                if cc == '\n' || cc == '\r' { break; }
            }
            continue;
        }

        // 3) Two-character operators: => and <=
        if c == '=' {
            chars.next();
            if let Some('>') = chars.peek() {
                chars.next();
                tokens.push(Token { kind: TokenKind::OpImplies });
                continue;
            } else {
                panic!("Unexpected '='");
            }
        }

        if c == '<' {
            chars.next();
            if let Some('=') = chars.peek() {
                chars.next();
                tokens.push(Token { kind: TokenKind::OpImpliedBy });
                continue;
            }

            // Otherwise it’s an IRIREF: <http://...>
            let mut iri = String::new();
            while let Some(cc) = chars.next() {
                if cc == '>' { break; }
                iri.push(cc);
            }
            tokens.push(Token { kind: TokenKind::IriRef(iri) });
            continue;
        }

        // 4) Datatype operator ^^ after literals
        if c == '^' {
            chars.next();
            if let Some('^') = chars.peek() {
                chars.next();
                tokens.push(Token { kind: TokenKind::HatHat });
                continue;
            } else {
                panic!("Unexpected '^' (did you mean ^^?)");
            }
        }

        // 5) Single-character punctuation
        match c {
            '{' => { chars.next(); tokens.push(Token { kind: TokenKind::LBrace }); continue; }
            '}' => { chars.next(); tokens.push(Token { kind: TokenKind::RBrace }); continue; }
            '(' => { chars.next(); tokens.push(Token { kind: TokenKind::LParen }); continue; }
            ')' => { chars.next(); tokens.push(Token { kind: TokenKind::RParen }); continue; }
            '[' => { chars.next(); tokens.push(Token { kind: TokenKind::LBracket }); continue; }
            ']' => { chars.next(); tokens.push(Token { kind: TokenKind::RBracket }); continue; }
            ';' => { chars.next(); tokens.push(Token { kind: TokenKind::Semicolon }); continue; }
            ',' => { chars.next(); tokens.push(Token { kind: TokenKind::Comma }); continue; }
            '.' => { chars.next(); tokens.push(Token { kind: TokenKind::Dot }); continue; }

            '"' => {
                // String literal "...", with minimal escape handling.
                chars.next(); // consume opening "
                let mut s = String::new();
                while let Some(cc) = chars.next() {
                    if cc == '\\' {
                        // keep escapes literally
                        if let Some(esc) = chars.next() {
                            s.push('\\');
                            s.push(esc);
                        }
                        continue;
                    }
                    if cc == '"' { break; }
                    s.push(cc);
                }
                tokens.push(Token { kind: TokenKind::Literal(format!("\"{}\"", s)) });
                continue;
            }

            '?' => {
                // Variable: ?name
                chars.next(); // consume '?'
                let mut name = String::new();
                while let Some(&cc) = chars.peek() {
                    if is_name_char(cc) {
                        name.push(cc);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token { kind: TokenKind::Var(name) });
                continue;
            }

            '@' => {
                // Directives: @prefix, @base
                chars.next(); // consume '@'
                let mut word = String::new();
                while let Some(&cc) = chars.peek() {
                    if cc.is_alphabetic() {
                        word.push(cc);
                        chars.next();
                    } else {
                        break;
                    }
                }
                match word.as_str() {
                    "prefix" => tokens.push(Token { kind: TokenKind::AtPrefix }),
                    "base"   => tokens.push(Token { kind: TokenKind::AtBase }),
                    _ => panic!("Unknown directive @{}", word),
                }
                continue;
            }

            _ => {}
        }

        // 6) Numeric literal (integer or float)
        //
        // We treat a leading '-' as part of a number only if followed by digit.
        if c.is_ascii_digit() || (c == '-' && {
            let mut it = chars.clone();
            it.next(); // skip '-'
            matches!(it.peek(), Some(d) if d.is_ascii_digit())
        }) {
            let mut num = String::new();
            num.push(chars.next().unwrap());

            while let Some(&cc) = chars.peek() {
                if cc.is_ascii_digit() {
                    num.push(cc);
                    chars.next();
                    continue;
                }
                if cc == '.' {
                    // only keep '.' if it's a decimal point; otherwise '.' ends a statement.
                    let mut it = chars.clone();
                    it.next();
                    if matches!(it.peek(), Some(d) if d.is_ascii_digit()) {
                        num.push('.');
                        chars.next();
                        continue;
                    } else {
                        break;
                    }
                }
                break;
            }

            tokens.push(Token { kind: TokenKind::Literal(num) });
            continue;
        }

        // 7) Identifiers / keywords / QNames
        let mut word = String::new();
        while let Some(&cc) = chars.peek() {
            if is_name_char(cc) {
                word.push(cc);
                chars.next();
            } else {
                break;
            }
        }

        if word.is_empty() {
            panic!("Unexpected char: {}", c);
        }

        // Booleans are treated as literals.
        if word == "true" || word == "false" {
            tokens.push(Token { kind: TokenKind::Literal(word) });
        } else if word.chars().all(|ch| ch.is_ascii_digit() || ch == '.' || ch == '-') {
            // Another numeric-ish literal
            tokens.push(Token { kind: TokenKind::Literal(word) });
        } else {
            tokens.push(Token { kind: TokenKind::Ident(word) });
        }
    }

    tokens.push(Token { kind: TokenKind::EOF });
    tokens
}

// =====================================================================================
// PREFIX ENVIRONMENT
// =====================================================================================

/// Maps prefixes (`rdf`, `xsd`, `:`) to full IRIs.
///
/// We store expanded IRIs internally.
/// Prefix expansion only happens during parsing.
#[derive(Clone, Debug)]
struct PrefixEnv {
    map: HashMap<String, String>, // prefix -> base IRI
}

impl PrefixEnv {
    fn new() -> Self {
        let mut map = HashMap::new();
        // "Built-in" defaults so most files work without explicit prefix handling.
        map.insert("rdf".to_string(), RDF_NS.to_string());
        map.insert("rdfs".to_string(), RDFS_NS.to_string());
        map.insert("xsd".to_string(), XSD_NS.to_string());
        map.insert("log".to_string(), LOG_NS.to_string());
        map.insert("math".to_string(), MATH_NS.to_string());
        map.insert("string".to_string(), STRING_NS.to_string());
        map.insert("list".to_string(), LIST_NS.to_string());
        map.insert("time".to_string(), TIME_NS.to_string());

        // Default prefix ":" maps to base IRI (possibly @base).
        map.insert("".to_string(), "".to_string());

        PrefixEnv { map }
    }

    /// Set or override a prefix mapping.
    fn set(&mut self, pref: &str, base: &str) {
        self.map.insert(pref.to_string(), base.to_string());
    }

    /// Expand a QName like `xsd:date` to a full IRI.
    fn expand_qname(&self, q: &str) -> String {
        if let Some(idx) = q.find(':') {
            let (p, local) = q.split_at(idx);
            let local = &local[1..]; // skip ':'
            let base = self.map.get(p).cloned().unwrap_or_default();
            if !base.is_empty() {
                return format!("{}{}", base, local);
            }
        }
        // If we don’t know this prefix, return unchanged.
        q.to_string()
    }

    /// Try to shrink a full IRI back to a QName for pretty printing.
    /// We pick the “best” (shortest local name) matching prefix.
    fn shrink_iri(&self, iri: &str) -> Option<String> {
        let mut best: Option<(String, String)> = None; // (prefix, local)

        for (p, base) in &self.map {
            if base.is_empty() { continue; }
            if iri.starts_with(base) {
                let local = &iri[base.len()..];
                if local.is_empty() { continue; }

                let cand = (p.clone(), local.to_string());
                if best.is_none() || cand.1.len() < best.as_ref().unwrap().1.len() {
                    best = Some(cand);
                }
            }
        }

        best.map(|(p, local)| {
            if p.is_empty() { format!(":{}", local) }
            else { format!("{}:{}", p, local) }
        })
    }

    /// Decide which prefixes are actually needed in output.
    fn prefixes_used_for_output(&self, triples: &[Triple]) -> Vec<(String, String)> {
        let mut used = HashSet::new();

        for t in triples {
            // Always consider subject + object IRIs.
            // Only include predicate IRIs if it’s not rdf:type -> `a`.
            let mut iris = Vec::new();
            iris.extend(collect_iris_in_term(&t.s));
            if !is_rdf_type_pred(&t.p) {
                iris.extend(collect_iris_in_term(&t.p));
            }
            iris.extend(collect_iris_in_term(&t.o));

            for iri in iris {
                for (p, base) in &self.map {
                    if base.is_empty() { continue; }
                    if iri.starts_with(base) {
                        used.insert(p.clone());
                    }
                }
            }
        }

        let mut v: Vec<(String, String)> = used
            .into_iter()
            .filter_map(|p| self.map.get(&p).map(|b| (p, b.clone())))
            .collect();

        v.sort_by(|a, b| a.0.cmp(&b.0));
        v
    }
}

/// Collect all IRIs appearing inside a term (recursing into lists/formulas).
fn collect_iris_in_term(t: &Term) -> Vec<String> {
    let mut out = Vec::new();
    match t {
        Term::Iri(i) => out.push(i.clone()),

        Term::List(vs) => {
            for x in vs { out.extend(collect_iris_in_term(x)); }
        }

        Term::OpenList(vs, _) => {
            for x in vs { out.extend(collect_iris_in_term(x)); }
        }

        Term::Formula(fs) => {
            for tr in fs {
                out.extend(collect_iris_in_term(&tr.s));
                out.extend(collect_iris_in_term(&tr.p));
                out.extend(collect_iris_in_term(&tr.o));
            }
        }

        Term::Literal(_) | Term::Var(_) | Term::Blank(_) => {}
    }
    out
}

/// Collect all variable names appearing inside a term
/// (recursing into lists and formulas).
fn collect_vars_in_term(t: &Term, acc: &mut HashSet<String>) {
    match t {
        Term::Var(v) => {
            acc.insert(v.clone());
        }
        Term::List(xs) => {
            for x in xs {
                collect_vars_in_term(x, acc);
            }
        }
        Term::OpenList(xs, tailv) => {
            for x in xs {
                collect_vars_in_term(x, acc);
            }
            acc.insert(tailv.clone());
        }
        Term::Formula(ts) => {
            for tr in ts {
                collect_vars_in_term(&tr.s, acc);
                collect_vars_in_term(&tr.p, acc);
                collect_vars_in_term(&tr.o, acc);
            }
        }
        Term::Iri(_) | Term::Literal(_) | Term::Blank(_) => {}
    }
}

/// Collect the set of variable names that syntactically occur in a rule
/// (both in the premise and the conclusion).
fn vars_in_rule(rule: &Rule) -> HashSet<String> {
    let mut acc = HashSet::new();

    for tr in &rule.premise {
        collect_vars_in_term(&tr.s, &mut acc);
        collect_vars_in_term(&tr.p, &mut acc);
        collect_vars_in_term(&tr.o, &mut acc);
    }
    for tr in &rule.conclusion {
        collect_vars_in_term(&tr.s, &mut acc);
        collect_vars_in_term(&tr.p, &mut acc);
        collect_vars_in_term(&tr.o, &mut acc);
    }

    acc
}

// =====================================================================================
// PARSER
// =====================================================================================

/// A tiny recursive-descent parser.
///
/// We parse from tokens into facts + rules.
/// This is not a full N3 parser; it supports the patterns used in examples.
struct Parser {
    toks: Vec<Token>,
    pos: usize,
    prefixes: PrefixEnv,
    blank_counter: usize,
    pending_triples: Vec<Triple>,
}

impl Parser {
    fn new(toks: Vec<Token>) -> Self {
        Parser {
            toks,
            pos: 0,
            prefixes: PrefixEnv::new(),
            blank_counter: 0,
            pending_triples: Vec::new(),
        }
    }

    /// Peek without consuming.
    fn peek(&self) -> &TokenKind {
        &self.toks[self.pos].kind
    }

    /// Consume and return one token kind.
    fn next(&mut self) -> TokenKind {
        let k = self.toks[self.pos].kind.clone();
        self.pos += 1;
        k
    }

    /// Expect and consume a '.'.
    fn expect_dot(&mut self) {
        match self.next() {
            TokenKind::Dot => {}
            other => panic!("Expected '.', got {:?}", other),
        }
    }

    /// Parse a whole document.
    ///
    /// Returns:
    /// - prefixes
    /// - ground triples
    /// - forward rules
    /// - backward rules
    fn parse_document(&mut self) -> (PrefixEnv, Vec<Triple>, Vec<Rule>, Vec<Rule>) {
        let mut triples = vec![];
        let mut forward_rules = vec![];
        let mut backward_rules = vec![];

        while *self.peek() != TokenKind::EOF {
            match self.peek() {
                TokenKind::AtPrefix => {
                    self.next();
                    self.parse_prefix_directive();
                }
                TokenKind::AtBase => {
                    self.next();
                    self.parse_base_directive();
                }
                _ => {
                    // statement:
                    //   term (=>|<= term)? .
                    // OR a normal triple statement.
                    let first = self.parse_term();

                    match self.peek() {
                        TokenKind::OpImplies => {
                            self.next();
                            let second = self.parse_term();
                            self.expect_dot();
                            forward_rules.push(self.make_rule(first, second, true));
                        }
                        TokenKind::OpImpliedBy => {
                            self.next();
                            let second = self.parse_term();
                            self.expect_dot();
                            backward_rules.push(self.make_rule(first, second, false));
                        }
                        _ => {
                            // classic subject predicateObjectList .
                            let mut more = self.parse_predicate_object_list(first);
                            self.expect_dot();

                            // normalize explicit log:implies / log:impliedBy at top-level
                            for tr in more.drain(..) {
                                if is_log_implies(&tr.p)
                                    && matches!(tr.s, Term::Formula(_))
                                    && matches!(tr.o, Term::Formula(_))
                                {
                                    forward_rules.push(self.make_rule(tr.s.clone(), tr.o.clone(), true));
                                } else if is_log_implied_by(&tr.p)
                                    && matches!(tr.s, Term::Formula(_))
                                    && matches!(tr.o, Term::Formula(_))
                                {
                                    backward_rules.push(self.make_rule(tr.s.clone(), tr.o.clone(), false));
                                } else {
                                    triples.push(tr);
                                }
                            }
                        }
                    }
                }
            }
        }

        (self.prefixes.clone(), triples, forward_rules, backward_rules)
    }

    /// Parse `@prefix p: <...> .` or `@prefix p: .`
    fn parse_prefix_directive(&mut self) {
        let pref = match self.next() {
            TokenKind::Ident(s) => s,
            other => panic!("Expected prefix name, got {:?}", other),
        };

        let pref_name = if pref.ends_with(':') {
            pref[..pref.len() - 1].to_string()
        } else {
            pref
        };

        // Allow @prefix p: . (empty IRI)
        if *self.peek() == TokenKind::Dot {
            self.next();
            if !self.prefixes.map.contains_key(&pref_name) {
                self.prefixes.set(&pref_name, "");
            }
            return;
        }

        let iri = match self.next() {
            TokenKind::IriRef(s) => s,
            TokenKind::Ident(s) => self.prefixes.expand_qname(&s),
            other => panic!("Expected IRI after @prefix, got {:?}", other),
        };

        self.expect_dot();
        self.prefixes.set(&pref_name, &iri);
    }

    /// Parse `@base <...> .`
    fn parse_base_directive(&mut self) {
        let iri = match self.next() {
            TokenKind::IriRef(s) => s,
            TokenKind::Ident(s) => s,
            other => panic!("Expected IRI after @base, got {:?}", other),
        };
        self.expect_dot();
        self.prefixes.set("", &iri);
    }

    /// Parse a single term.
    fn parse_term(&mut self) -> Term {
        match self.next() {
            TokenKind::IriRef(iri) => Term::Iri(iri),

            TokenKind::Ident(name) => {
                if name == "a" {
                    // rdf:type keyword
                    Term::Iri(format!("{}type", RDF_NS))
                } else if name.starts_with("_:") {
                    // Labeled blank node (Turtle/N3 syntax _:foo)
                    Term::Blank(name)
                } else if name.contains(':') {
                    // QName
                    Term::Iri(self.prefixes.expand_qname(&name))
                } else {
                    // Bareword treated as an IRI-ish identifier
                    Term::Iri(name)
                }
            }

            TokenKind::Literal(mut s) => {
                // Typed literal: "..."^^xsd:date
                if *self.peek() == TokenKind::HatHat {
                    self.next(); // consume ^^
                    let dt_iri = match self.next() {
                        TokenKind::IriRef(i) => i,
                        TokenKind::Ident(qn) => {
                            if qn.contains(':') {
                                self.prefixes.expand_qname(&qn)
                            } else {
                                qn
                            }
                        }
                        other => panic!("Expected datatype after ^^, got {:?}", other),
                    };
                    s = format!("{}^^<{}>", s, dt_iri);
                }
                Term::Literal(s)
            }

            TokenKind::Var(v) => Term::Var(v),
            TokenKind::LParen => self.parse_list(),
            TokenKind::LBracket => self.parse_blank(),
            TokenKind::LBrace => self.parse_formula(),

            other => panic!("Unexpected term token: {:?}", other),
        }
    }

    /// Parse `( ... )` list.
    fn parse_list(&mut self) -> Term {
        let mut elems = vec![];
        while *self.peek() != TokenKind::RParen {
            elems.push(self.parse_term());
        }
        self.next(); // consume ')'
        Term::List(elems)
    }

    /// Parse blank node `[]` or `[ ... ]` property list.
    ///
    /// - `[]`          => a fresh Term::Blank
    /// - `[ :p :o ]`   => a fresh Term::Blank plus extra triples
    ///                    _:bN :p :o .
    fn parse_blank(&mut self) -> Term {
        // Simple [] with no property list
        if *self.peek() == TokenKind::RBracket {
            self.next(); // consume ']'
            self.blank_counter += 1;
            return Term::Blank(format!("_:b{}", self.blank_counter));
        }

        // Blank node property list: [ predicateObjectList ]
        self.blank_counter += 1;
        let id = format!("_:b{}", self.blank_counter);
        let subj = Term::Blank(id.clone());

        // Minimal inlined `predicateObjectList` for the blank node.
        // We *don't* use parse_predicate_object_list here to avoid
        // mixing the subject with the outer statement.
        loop {
            // Verb (can also be 'a')
            let pred = match self.peek() {
                TokenKind::Ident(s) if s == "a" => {
                    self.next();
                    Term::Iri(format!("{}type", RDF_NS))
                }
                _ => self.parse_term(),
            };

            // Object list: o1, o2, ...
            let mut objs = vec![self.parse_term()];
            while *self.peek() == TokenKind::Comma {
                self.next();
                objs.push(self.parse_term());
            }

            for o in objs {
                self.pending_triples.push(Triple {
                    s: subj.clone(),
                    p: pred.clone(),
                    o,
                });
            }

            if *self.peek() == TokenKind::Semicolon {
                self.next();
                if *self.peek() == TokenKind::RBracket {
                    break;
                }
                continue;
            }
            break;
        }

        // Expect closing ']'
        match self.peek() {
            TokenKind::RBracket => {
                self.next(); // consume ']'
            }
            other => panic!("Expected ']' at end of blank node property list, got {:?}", other),
        }

        // Return the blank node term; the extra triples are now in
        // self.pending_triples and will be attached by the caller.
        Term::Blank(id)
    }

    /// Parse `{ ... }` formula.
    ///
    /// Inside formulas the last '.' can be omitted, so we accept either '.' or '}'.
    /// Nested rules `{ A } => { B }` and `{ A } <= { B }` inside a formula are
    /// represented as explicit `log:implies` / `log:impliedBy` triples:
    ///
    ///   { A } => { B }   ==>   (A) log:implies (B)
    ///   { A } <= { B }   ==>   (A) log:impliedBy (B)
    fn parse_formula(&mut self) -> Term {
        let mut triples = vec![];

        while *self.peek() != TokenKind::RBrace {
            let left = self.parse_term();

            match self.peek() {
                TokenKind::OpImplies => {
                    // { left } => { right }  inside a formula
                    self.next(); // consume =>
                    let right = self.parse_term();

                    let pred = Term::Iri(format!("{}implies", LOG_NS));
                    triples.push(Triple {
                        s: left,
                        p: pred,
                        o: right,
                    });

                    match self.peek() {
                        TokenKind::Dot => {
                            self.next();
                        }
                        TokenKind::RBrace => {}
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                }

                TokenKind::OpImpliedBy => {
                    // { left } <= { right }  inside a formula
                    self.next(); // consume <=
                    let right = self.parse_term();

                    let pred = Term::Iri(format!("{}impliedBy", LOG_NS));
                    triples.push(Triple {
                        s: left,
                        p: pred,
                        o: right,
                    });

                    match self.peek() {
                        TokenKind::Dot => {
                            self.next();
                        }
                        TokenKind::RBrace => {}
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                }

                _ => {
                    triples.append(&mut self.parse_predicate_object_list(left));
                    match self.peek() {
                        TokenKind::Dot => {
                            self.next();
                        }
                        TokenKind::RBrace => {}
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                }
            }
        }

        self.next(); // consume '}'
        Term::Formula(triples)
    }

    /// Parse `subject predicateObjectList` allowing ; and ,.
    fn parse_predicate_object_list(&mut self, subject: Term) -> Vec<Triple> {
        let mut out = vec![];

        loop {
            // Verb can be 'a'
            let verb = match self.peek() {
                TokenKind::Ident(s) if s == "a" => {
                    self.next();
                    Term::Iri(format!("{}type", RDF_NS))
                }
                _ => self.parse_term(),
            };

            let objects = self.parse_object_list();
            for o in objects {
                out.push(Triple {
                    s: subject.clone(),
                    p: verb.clone(),
                    o,
                });
            }

            if *self.peek() == TokenKind::Semicolon {
                self.next();
                if *self.peek() == TokenKind::Dot {
                    break;
                }
                continue;
            }
            break;
        }

        // Attach any triples created by blank node property lists `[ ... ]`
        if !self.pending_triples.is_empty() {
            out.extend(self.pending_triples.drain(..));
        }

        out
    }

    /// Parse object list `o1, o2, ...`
    fn parse_object_list(&mut self) -> Vec<Term> {
        let mut objs = vec![self.parse_term()];
        while *self.peek() == TokenKind::Comma {
            self.next();
            objs.push(self.parse_term());
        }
        objs
    }

    /// Convert lhs/rhs terms into Rule struct.
    fn make_rule(&self, left: Term, right: Term, is_forward: bool) -> Rule {
        // For <= rules, swap to keep premise/body on the left.
        let (premise_term, concl_term) = if is_forward { (left, right) } else { (right, left) };

        // Inference fuse: { ... } => false.
        let is_fuse = if is_forward {
            if let Term::Literal(ref lit) = concl_term {
                lit == "false"
            } else {
                false
            }
        } else {
            false
        };

        let raw_premise = match premise_term {
            Term::Formula(ts) => ts,
            Term::Literal(lit) if lit == "true" => Vec::new(),
            _ => Vec::new(),
        };

        let raw_conclusion = match concl_term {
            Term::Formula(ts) => ts,
            // For fuses, there are no head triples to derive.
            Term::Literal(lit) if lit == "false" => Vec::new(),
            _ => Vec::new(),
        };

        // lift rule-local blank nodes to variables.
        let (premise, conclusion) = lift_blank_rule_vars(raw_premise, raw_conclusion);

        Rule {
            premise,
            conclusion,
            is_forward,
            is_fuse,
        }
    }
}

/// Convert every Term::Blank *in the premise* into a rule-scoped variable.
///
/// Blank nodes in the rule body become “pattern variables”.
/// Blank nodes in the head stay blank and are treated existentially.
fn lift_blank_rule_vars(
    premise: Vec<Triple>,
    conclusion: Vec<Triple>,
) -> (Vec<Triple>, Vec<Triple>) {
    fn convert_term(
        t: &Term,
        mapping: &mut HashMap<String, String>,
        counter: &mut usize,
    ) -> Term {
        match t {
            Term::Blank(label) => {
                // One variable per distinct blank label in this rule body.
                let var_name = mapping
                    .entry(label.clone())
                    .or_insert_with(|| {
                        *counter += 1;
                        format!("_b{}", *counter)
                    })
                    .clone();
                Term::Var(var_name)
            }
            Term::List(xs) => {
                Term::List(xs.iter().map(|e| convert_term(e, mapping, counter)).collect())
            }
            Term::OpenList(xs, tail) => {
                Term::OpenList(
                    xs.iter().map(|e| convert_term(e, mapping, counter)).collect(),
                    tail.clone(),
                )
            }
            Term::Formula(ts) => {
                let triples = ts
                    .iter()
                    .map(|tr| Triple {
                        s: convert_term(&tr.s, mapping, counter),
                        p: convert_term(&tr.p, mapping, counter),
                        o: convert_term(&tr.o, mapping, counter),
                    })
                    .collect();
                Term::Formula(triples)
            }
            _ => t.clone(),
        }
    }

    fn convert_triple(
        tr: &Triple,
        mapping: &mut HashMap<String, String>,
        counter: &mut usize,
    ) -> Triple {
        Triple {
            s: convert_term(&tr.s, mapping, counter),
            p: convert_term(&tr.p, mapping, counter),
            o: convert_term(&tr.o, mapping, counter),
        }
    }

    let mut mapping: HashMap<String, String> = HashMap::new();
    let mut counter: usize = 0;

    let new_premise: Vec<Triple> = premise
        .iter()
        .map(|tr| convert_triple(tr, &mut mapping, &mut counter))
        .collect();

    // Head blanks are left untouched → existentials.
    (new_premise, conclusion)
}

/// Skolemize blank nodes in a conclusion term.
///
/// mapping: maps original blank labels (e.g. "_:B") to fresh "_:sk_N" for
/// THIS rule application.
/// sk_counter: global counter for fresh blank ids across the whole run.
fn skolemize_term(
    t: &Term,
    mapping: &mut HashMap<String, String>,
    sk_counter: &mut usize,
) -> Term {
    match t {
        Term::Blank(label) => {
            let new_label = mapping
                .entry(label.clone())
                .or_insert_with(|| {
                    let id = *sk_counter;
                    *sk_counter += 1;
                    format!("_:sk_{}", id)
                })
                .clone();
            Term::Blank(new_label)
        }
        Term::List(xs) => {
            Term::List(xs.iter().map(|e| skolemize_term(e, mapping, sk_counter)).collect())
        }
        Term::OpenList(xs, tailv) => {
            Term::OpenList(
                xs.iter().map(|e| skolemize_term(e, mapping, sk_counter)).collect(),
                tailv.clone(),
            )
        }
        Term::Formula(ts) => {
            Term::Formula(
                ts.iter()
                    .map(|tr| skolemize_triple(tr, mapping, sk_counter))
                    .collect(),
            )
        }
        _ => t.clone(),
    }
}

fn skolemize_triple(
    tr: &Triple,
    mapping: &mut HashMap<String, String>,
    sk_counter: &mut usize,
) -> Triple {
    Triple {
        s: skolemize_term(&tr.s, mapping, sk_counter),
        p: skolemize_term(&tr.p, mapping, sk_counter),
        o: skolemize_term(&tr.o, mapping, sk_counter),
    }
}

/// Alpha-equivalence on terms: blanks may differ by name but must map consistently.
fn alpha_eq_term(
    a: &Term,
    b: &Term,
    bmap: &mut HashMap<String, String>,
) -> bool {
    match (a, b) {
        (Term::Blank(x), Term::Blank(y)) => {
            if let Some(existing) = bmap.get(x) {
                existing == y
            } else {
                bmap.insert(x.clone(), y.clone());
                true
            }
        }
        (Term::Iri(x), Term::Iri(y)) => x == y,
        (Term::Literal(x), Term::Literal(y)) => x == y,
        (Term::Var(x), Term::Var(y)) => x == y,
        (Term::List(xs), Term::List(ys)) => {
            xs.len() == ys.len()
                && xs.iter()
                    .zip(ys.iter())
                    .all(|(u, v)| alpha_eq_term(u, v, bmap))
        }
        (Term::OpenList(xs, tx), Term::OpenList(ys, ty)) => {
            tx == ty
                && xs.len() == ys.len()
                && xs.iter()
                    .zip(ys.iter())
                    .all(|(u, v)| alpha_eq_term(u, v, bmap))
        }
        // For formulas we keep the simple equality used elsewhere.
        (Term::Formula(xs), Term::Formula(ys)) => xs == ys,
        _ => false,
    }
}

fn alpha_eq_triple(a: &Triple, b: &Triple) -> bool {
    let mut bmap: HashMap<String, String> = HashMap::new();
    alpha_eq_term(&a.s, &b.s, &mut bmap)
        && alpha_eq_term(&a.p, &b.p, &mut bmap)
        && alpha_eq_term(&a.o, &b.o, &mut bmap)
}

fn has_alpha_equiv(set: &HashSet<Triple>, tr: &Triple) -> bool {
    set.iter().any(|t| alpha_eq_triple(t, tr))
}

// =====================================================================================
// Small helpers about special predicates
// =====================================================================================

fn is_rdf_type_pred(p: &Term) -> bool {
    matches!(p, Term::Iri(i) if i == &format!("{}type", RDF_NS))
}

fn is_log_implies(p: &Term) -> bool {
    matches!(p, Term::Iri(i) if i.as_str() == format!("{}implies", LOG_NS))
}

fn is_log_implied_by(p: &Term) -> bool {
    matches!(p, Term::Iri(i) if i.as_str() == format!("{}impliedBy", LOG_NS))
}

// =====================================================================================
// Unification + substitution
// =====================================================================================
//
// Unification is “pattern matching with variables”.
// It is the engine behind both backward proof and forward rule instantiation.
//
// We use a classic “occurs check light” unifier.
// Substitutions are applied recursively to terms/triples.

// Does term t contain variable v?
fn contains_var_term(t: &Term, v: &str) -> bool {
    match t {
        Term::Var(x) => x == v,
        Term::List(xs) => xs.iter().any(|e| contains_var_term(e, v)),
        Term::OpenList(xs, tailv) => {
            xs.iter().any(|e| contains_var_term(e, v)) || tailv == v
        }
        Term::Formula(ts) => ts.iter().any(|tr| {
            contains_var_term(&tr.s, v)
                || contains_var_term(&tr.p, v)
                || contains_var_term(&tr.o, v)
        }),
        _ => false,
    }
}

// Is a term fully ground (no variables, no open tails)?
fn is_ground_term(t: &Term) -> bool {
    match t {
        Term::Var(_) => false,
        Term::List(xs) => xs.iter().all(is_ground_term),
        Term::OpenList(_, _) => false,
        Term::Formula(ts) => ts.iter().all(is_ground_triple),
        _ => true,
    }
}

fn is_ground_triple(tr: &Triple) -> bool {
    is_ground_term(&tr.s) && is_ground_term(&tr.p) && is_ground_term(&tr.o)
}

// Apply substitution to a term.
fn apply_subst_term(t: &Term, s: &Subst) -> Term {
    match t {
        Term::Var(v) => {
            // Follow substitution chains ?X -> ?Y -> ... to a fixed point.
            let mut cur = Term::Var(v.clone());
            let mut seen = HashSet::new();

            loop {
                if let Term::Var(name) = &cur {
                    if !seen.insert(name.clone()) {
                        break; // cycle
                    }
                    if let Some(next) = s.get(name) {
                        cur = next.clone();
                        continue;
                    }
                }
                break;
            }

            match cur {
                Term::Var(name) => Term::Var(name),
                other => apply_subst_term(&other, s),
            }
        }

        Term::List(xs) => {
            Term::List(xs.iter().map(|e| apply_subst_term(e, s)).collect())
        }

        Term::OpenList(prefix, tailv) => {
            // First apply subst to the fixed prefix.
            let new_prefix: Vec<Term> =
                prefix.iter().map(|e| apply_subst_term(e, s)).collect();

            // If the tail variable is bound, try to “close” the open list.
            if let Some(tail_term) = s.get(tailv) {
                let tail_applied = apply_subst_term(tail_term, s);
                match tail_applied {
                    Term::List(tail_elems) => {
                        let mut all = new_prefix;
                        all.extend(tail_elems);
                        Term::List(all)
                    }
                    Term::OpenList(tail_prefix, tail_tailv) => {
                        let mut all_prefix = new_prefix;
                        all_prefix.extend(tail_prefix);
                        Term::OpenList(all_prefix, tail_tailv)
                    }
                    _ => Term::OpenList(new_prefix, tailv.clone()),
                }
            } else {
                Term::OpenList(new_prefix, tailv.clone())
            }
        }

        Term::Formula(ts) => {
            Term::Formula(ts.iter().map(|tr| apply_subst_triple(tr, s)).collect())
        }

        _ => t.clone(),
    }
}

fn apply_subst_triple(tr: &Triple, s: &Subst) -> Triple {
    Triple {
        s: apply_subst_term(&tr.s, s),
        p: apply_subst_term(&tr.p, s),
        o: apply_subst_term(&tr.o, s),
    }
}

/// Helper for OpenList unification with a concrete list.
fn unify_open_with_list(
    prefix: &[Term],
    tailv: &str,
    ys: &[Term],
    subst: &Subst,
) -> Option<Subst> {
    // Concrete list must be at least as long as the open prefix.
    if ys.len() < prefix.len() {
        return None;
    }

    let mut s2 = subst.clone();

    for (x, y) in prefix.iter().zip(ys.iter()) {
        s2 = unify_term(x, y, &s2)?;
    }

    // Bind tail variable to the remaining suffix.
    let rest = Term::List(ys[prefix.len()..].to_vec());
    s2 = unify_term(&Term::Var(tailv.to_string()), &rest, &s2)?;

    Some(s2)
}

/// Unify two terms under an existing substitution.
/// Returns an extended substitution, or None if they can't match.
///
/// Rust tip: `Option<T>` is Rust’s safe “maybe” type.
fn unify_term(a: &Term, b: &Term, subst: &Subst) -> Option<Subst> {
    let a = apply_subst_term(a, subst);
    let b = apply_subst_term(b, subst);

    match (a, b) {
        // Variable binding (either side)
        (Term::Var(v), t) | (t, Term::Var(v)) => {
            // If same variable, already unified.
            if let Term::Var(v2) = &t {
                if v2 == &v {
                    return Some(subst.clone());
                }
            }

            // Occurs check: prevent ?X = ( ... ?X ... )
            if contains_var_term(&t, &v) {
                return None;
            }

            let mut s2 = subst.clone();
            s2.insert(v, t);
            Some(s2)
        }

        // Exact matches
        (Term::Iri(x), Term::Iri(y)) if x == y => Some(subst.clone()),
        (Term::Literal(x), Term::Literal(y)) if x == y => Some(subst.clone()),
        (Term::Blank(x), Term::Blank(y)) if x == y => Some(subst.clone()),

        // Open list vs concrete list
        (Term::OpenList(pref, tailv), Term::List(ys)) => {
            unify_open_with_list(&pref, &tailv, &ys, subst)
        }
        (Term::List(xs), Term::OpenList(pref, tailv)) => {
            unify_open_with_list(&pref, &tailv, &xs, subst)
        }

        // Open list vs open list (same tail var required)
        (Term::OpenList(p1, t1), Term::OpenList(p2, t2)) => {
            if t1 != t2 || p1.len() != p2.len() {
                return None;
            }
            let mut s2 = subst.clone();
            for (x, y) in p1.iter().zip(p2.iter()) {
                s2 = unify_term(x, y, &s2)?;
            }
            Some(s2)
        }

        // List element-wise unification
        (Term::List(xs), Term::List(ys)) => {
            if xs.len() != ys.len() {
                return None;
            }
            let mut s2 = subst.clone();
            for (x, y) in xs.iter().zip(ys.iter()) {
                s2 = unify_term(x, y, &s2)?;
            }
            Some(s2)
        }

        // Formulas are treated as opaque unless exactly equal.
        (Term::Formula(xs), Term::Formula(ys)) if xs == ys => Some(subst.clone()),

        _ => None,
    }
}

fn unify_triple(pat: &Triple, fact: &Triple, subst: &Subst) -> Option<Subst> {
    let s1 = unify_term(&pat.s, &fact.s, subst)?;
    let s2 = unify_term(&pat.p, &fact.p, &s1)?;
    let s3 = unify_term(&pat.o, &fact.o, &s2)?;
    Some(s3)
}

/// Combine an "outer" substitution with a delta-substitution coming from
/// solving a single goal. If there is a conflicting binding we drop that
/// solution.
fn compose_subst(outer: &Subst, delta: &Subst) -> Option<Subst> {
    if delta.is_empty() {
        return Some(outer.clone());
    }
    let mut out = outer.clone();
    for (k, v) in delta {
        if let Some(existing) = out.get(k) {
            if existing != v {
                // inconsistent; this answer can't be joined with the outer context
                return None;
            }
        } else {
            out.insert(k.clone(), v.clone());
        }
    }
    Some(out)
}

// =====================================================================================
// BUILTINS
// =====================================================================================
//
// Builtins are evaluated during backward proving.
// They behave like predicates with special meaning.
//
// We keep this “builtin VM” extremely small: each builtin is just a match arm
// in eval_builtin.
//
// The builtins implemented so far include math:, log:, time:, and list:.
//

fn parse_num(t: &Term) -> Option<f64> {
    if let Term::Literal(s) = t {
        s.parse::<f64>().ok()
    } else {
        None
    }
}

/// Parse a literal as an arbitrary-precision integer if it looks like
/// a plain decimal integer (optionally with a leading '-').
fn parse_int_literal(t: &Term) -> Option<BigInt> {
    if let Term::Literal(s) = t {
        let (lex, _dt) = literal_parts(s);
        let lex = strip_quotes(&lex);

        if lex.is_empty() {
            return None;
        }

        let is_dec_int = lex.chars().all(|c| c.is_ascii_digit())
            || (lex.starts_with('-')
                && lex[1..].chars().all(|c| c.is_ascii_digit()));

        if is_dec_int {
            return BigInt::parse_bytes(lex.as_bytes(), 10);
        }
    }
    None
}

fn format_num(n: f64) -> String {
    if n.fract() == 0.0 {
        format!("{}", n as i64)
    } else {
        format!("{}", n)
    }
}

/// Decide whether a predicate IRI is a builtin we handle internally.
fn is_builtin_pred(p: &Term) -> bool {
    matches!(p, Term::Iri(i)
        if i.starts_with(MATH_NS)
        || i.starts_with(LOG_NS)
        || i.starts_with(STRING_NS)
        || i.starts_with(TIME_NS)
        || i.starts_with(LIST_NS))
}

// ----- typed literal helpers (dates/durations) -----
//
// N3 builtins often work on xsd:date, xsd:dateTime, xsd:duration.
// We store literals raw, so these helpers interpret strings.

fn literal_parts(lit: &str) -> (String, Option<String>) {
    if let Some(idx) = lit.find("^^") {
        let (lex, rest) = lit.split_at(idx);
        let mut dt = rest.trim_start_matches("^^").trim().to_string();
        if dt.starts_with('<') && dt.ends_with('>') {
            dt = dt[1..dt.len() - 1].to_string();
        }
        return (lex.to_string(), Some(dt));
    }
    (lit.to_string(), None)
}

fn strip_quotes(lex: &str) -> String {
    if lex.starts_with('"') && lex.ends_with('"') && lex.len() >= 2 {
        lex[1..lex.len() - 1].to_string()
    } else {
        lex.to_string()
    }
}

fn parse_xsd_date_term(t: &Term) -> Option<NaiveDate> {
    if let Term::Literal(s) = t {
        let (lex, dt) = literal_parts(s);
        let val = strip_quotes(&lex);
        if dt.as_deref() == Some(&format!("{}date", XSD_NS)) || val.len() == 10 {
            return NaiveDate::parse_from_str(&val, "%Y-%m-%d").ok();
        }
    }
    None
}

fn parse_xsd_datetime_term(t: &Term) -> Option<DateTime<Utc>> {
    if let Term::Literal(s) = t {
        let (lex, dt) = literal_parts(s);
        let val = strip_quotes(&lex);
        if dt.as_deref() == Some(&format!("{}dateTime", XSD_NS)) || val.contains('T') {
            if let Ok(p) = DateTime::parse_from_rfc3339(&val) {
                return Some(p.with_timezone(&Utc));
            }
        }
    }
    None
}

fn parse_datetime_like(t: &Term) -> Option<DateTime<Utc>> {
    if let Some(d) = parse_xsd_date_term(t) {
        let ndt = d.and_hms_opt(0, 0, 0)?;
        return Some(Utc.from_utc_datetime(&ndt));
    }
    parse_xsd_datetime_term(t)
}

/// Parse an ISO8601 duration like P80Y or P3DT4H into seconds (approx).
fn parse_iso8601_duration_to_seconds(s: &str) -> Option<f64> {
    let mut it = s.chars().peekable();
    if it.next()? != 'P' { return None; }

    let mut num = String::new();
    let mut in_time = false;

    let mut years = 0.0;
    let mut months = 0.0;
    let mut weeks = 0.0;
    let mut days = 0.0;
    let mut hours = 0.0;
    let mut minutes = 0.0;
    let mut seconds = 0.0;

    while let Some(c) = it.next() {
        if c == 'T' { in_time = true; continue; }
        if c.is_ascii_digit() || c == '.' { num.push(c); continue; }

        if num.is_empty() { return None; }
        let val: f64 = num.parse().ok()?;
        num.clear();

        match (in_time, c) {
            (false, 'Y') => years += val,
            (false, 'M') => months += val,
            (false, 'W') => weeks += val,
            (false, 'D') => days += val,
            (true, 'H') => hours += val,
            (true, 'M') => minutes += val,
            (true, 'S') => seconds += val,
            _ => return None,
        }
    }

    // Approximate conversion to seconds.
    let total_days =
        years * 365.2425 +
        months * 30.436875 +
        weeks * 7.0 +
        days +
        hours / 24.0 +
        minutes / (24.0 * 60.0) +
        seconds / (24.0 * 3600.0);

    Some(total_days * 86400.0)
}

fn parse_num_or_duration(t: &Term) -> Option<f64> {
    if let Some(n) = parse_num(t) { return Some(n); }

    if let Term::Literal(s) = t {
        let (lex, dt) = literal_parts(s);
        let val = strip_quotes(&lex);

        if dt.as_deref() == Some(&format!("{}duration", XSD_NS))
            || val.starts_with('P')
            || val.starts_with("-P")
        {
            let v = val.trim_start_matches('-');
            let secs = parse_iso8601_duration_to_seconds(v)?;
            return Some(if val.starts_with('-') { -secs } else { secs });
        }

        if let Some(dtval) = parse_datetime_like(t) {
            return Some(dtval.timestamp() as f64);
        }
    }
    None
}

fn format_duration_literal_from_seconds(secs: f64) -> Term {
    let neg = secs.is_sign_negative();
    let abs_secs = secs.abs();
    let days = (abs_secs / 86400.0).round() as i64;
    let lex = if neg { format!("\"-P{}D\"", days) } else { format!("\"P{}D\"", days) };
    Term::Literal(format!("{}^^<{}duration>", lex, XSD_NS))
}

/// Relational list:append, following the N3 spec:
/// ( $s.i?[*] )+ list:append $o?
/// true iff `o` is the concatenation of all lists `s.i`.
fn list_append_split(parts: &[Term], res_elems: &[Term], subst: &Subst) -> Vec<Subst> {
    // If we ran out of parts, the remaining result must be empty.
    if parts.is_empty() {
        return if res_elems.is_empty() {
            vec![subst.clone()]
        } else {
            vec![]
        };
    }

    let mut out = Vec::new();
    let n = res_elems.len();

    // Choose a split point k for the first part:
    // left = res[0..k], right = res[k..]
    for k in 0..=n {
        let left = Term::List(res_elems[..k].to_vec());

        if let Some(s1) = unify_term(&parts[0], &left, subst) {
            let rest_elems = &res_elems[k..];
            out.extend(list_append_split(&parts[1..], rest_elems, &s1));
        }
    }

    out
}

/// Evaluate a builtin triple under current substitution.
/// Returns zero or more new substitutions (for backtracking).
///
/// Some builtins (e.g. log:collectAllIn) need to look at the current
/// fact base and backward rules, so we thread those through.
fn eval_builtin(
    goal: &Triple,
    subst: &Subst,
    facts: &[Triple],
    back_rules: &[Rule],
    depth: usize,
    var_gen: &mut usize,
) -> Vec<Subst> {
    let g = apply_subst_triple(goal, subst);

    match &g.p {
        // ---------------------------------------------------------------------
        // time:localTime
        // ---------------------------------------------------------------------
        // "" time:localTime ?D.  binds ?D to “now” as xsd:dateTime.
        Term::Iri(p) if p == &format!("{}localTime", TIME_NS) => {
            let now = Local::now().to_rfc3339();
            match &g.o {
                Term::Var(v) => {
                    let mut s2 = subst.clone();
                    s2.insert(
                        v.clone(),
                        Term::Literal(format!("\"{}\"^^<{}dateTime>", now, XSD_NS)),
                    );
                    vec![s2]
                }
                Term::Literal(o) => {
                    let (lex_o, _) = literal_parts(o);
                    if strip_quotes(&lex_o) == now { vec![subst.clone()] } else { vec![] }
                }
                _ => vec![],
            }
        }

        // ---------------------------------------------------------------------
        // math: comparisons (binary OR list form)
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}greaterThan", MATH_NS) => {
            // Binary: A greaterThan B
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o)) {
                return if a > b { vec![subst.clone()] } else { vec![] };
            }
            // List: (A B) greaterThan true
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a > b { return vec![subst.clone()]; }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}lessThan", MATH_NS) => {
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o)) {
                return if a < b { vec![subst.clone()] } else { vec![] };
            }
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a < b { return vec![subst.clone()]; }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}notLessThan", MATH_NS) => {
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o)) {
                return if a >= b { vec![subst.clone()] } else { vec![] };
            }
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a >= b { return vec![subst.clone()]; }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}notGreaterThan", MATH_NS) => {
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o)) {
                return if a <= b { vec![subst.clone()] } else { vec![] };
            }
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a <= b { return vec![subst.clone()]; }
                    }
                }
            }
            vec![]
        }

        // ---------------------------------------------------------------------
        // math: arithmetic
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}sum", MATH_NS) => {
            // (a b c) math:sum ?z
            if let Term::List(xs) = &g.s {
                if xs.len() >= 2 {
                    // ----- Exact big-integer mode for plain integer literals -----
                    if let Some(total_big) = {
                        let mut acc = BigInt::from(0_i32);
                        let mut ok = true;
                        for t in xs {
                            match parse_int_literal(t) {
                                Some(n) => acc += n,
                                None => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        if ok { Some(acc) } else { None }
                    } {
                        let lit = Term::Literal(total_big.to_string());
                        return match &g.o {
                            // ?z is a variable: bind it to the big integer literal.
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), lit);
                                vec![s2]
                            }
                            // Otherwise, unify object with the computed literal (relational behaviour).
                            _ => {
                                if let Some(s2) = unify_term(&g.o, &lit, subst) {
                                    vec![s2]
                                } else {
                                    vec![]
                                }
                            }
                        };
                    }

                    // ----- Fallback: old float-based behaviour -----
                    if xs.iter().all(|t| parse_num(t).is_some()) {
                        let total: f64 = xs.iter().map(|t| parse_num(t).unwrap()).sum();
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(total)));
                                vec![s2]
                            }
                            Term::Literal(o) if o == &format_num(total) => vec![subst.clone()],
                            _ => vec![],
                        };
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}product", MATH_NS) => {
            if let Term::List(xs) = &g.s {
                if xs.len() >= 2 && xs.iter().all(|t| parse_num(t).is_some()) {
                    let prod: f64 = xs.iter().map(|t| parse_num(t).unwrap()).product();
                    return match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(prod)));
                            vec![s2]
                        }
                        Term::Literal(o) if o == &format_num(prod) => vec![subst.clone()],
                        _ => vec![],
                    };
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}difference", MATH_NS) => {
            // (?A ?B) math:difference ?C
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    // ----- Exact big-integer difference for integer literals -----
                    if let (Some(a_big), Some(b_big)) =
                        (parse_int_literal(&xs[0]), parse_int_literal(&xs[1]))
                    {
                        let c_big = a_big - b_big;
                        let lit = Term::Literal(c_big.to_string());
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), lit);
                                vec![s2]
                            }
                            _ => {
                                if let Some(s2) = unify_term(&g.o, &lit, subst) {
                                    vec![s2]
                                } else {
                                    vec![]
                                }
                            }
                        };
                    }

                    // ----- Fallback: numeric difference via f64 (existing behaviour) -----
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        let c = a - b;
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                vec![s2]
                            }
                            Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                            _ => vec![],
                        };
                    }

                    // ----- Date(dateTime) difference -> duration (unchanged) -----
                    if let (Some(a_dt), Some(b_dt)) =
                        (parse_datetime_like(&xs[0]), parse_datetime_like(&xs[1]))
                    {
                        let diff = a_dt - b_dt;
                        let secs = diff.num_seconds() as f64;
                        let dur_term = format_duration_literal_from_seconds(secs);
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), dur_term);
                                vec![s2]
                            }
                            Term::Literal(o) if Term::Literal(o.clone()) == dur_term => vec![subst.clone()],
                            _ => vec![],
                        };
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}quotient", MATH_NS) => {
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        if b == 0.0 { return vec![]; }
                        let c = a / b;
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                vec![s2]
                            }
                            Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                            _ => vec![],
                        };
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}exponentiation", MATH_NS) => {
            // (?A ?B) exponentiation ?C  =>  C = A^B
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        let c = a.powf(b);
                        return match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                vec![s2]
                            }
                            Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                            _ => vec![],
                        };
                    }

                    // Inverse mode for exponent:
                    // (A ?B) exponentiation C => B = ln(C)/ln(A)
                    if let (Some(a), Term::Var(bv), Some(c)) =
                        (parse_num(&xs[0]), &xs[1], parse_num(&g.o))
                    {
                        if a > 0.0 && a != 1.0 && c > 0.0 {
                            let b = c.ln() / a.ln();
                            let mut s2 = subst.clone();
                            s2.insert(bv.clone(), Term::Literal(format_num(b)));
                            return vec![s2];
                        }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}negation", MATH_NS) => {
            // x negation ?y => y = -x
            if let (Some(a), Term::Var(v)) = (parse_num(&g.s), &g.o) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(-a)));
                return vec![s2];
            }
            // ?x negation y => x = -y
            if let (Term::Var(v), Some(b)) = (&g.s, parse_num(&g.o)) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(-b)));
                return vec![s2];
            }
            // ground check
            if let (Some(a), Some(b)) = (parse_num(&g.s), parse_num(&g.o)) {
                if (-a - b).abs() < 1e-9 { return vec![subst.clone()]; }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}absoluteValue", MATH_NS) => {
            if let (Some(a), Term::Var(v)) = (parse_num(&g.s), &g.o) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(a.abs())));
                return vec![s2];
            }
            if let (Some(a), Some(b)) = (parse_num(&g.s), parse_num(&g.o)) {
                if (a.abs() - b).abs() < 1e-9 { return vec![subst.clone()]; }
            }
            vec![]
        }

        // Trig builtins
        Term::Iri(p) if p == &format!("{}cos", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.cos();
                return match &g.o {
                    Term::Var(v) => {
                        let mut s2 = subst.clone();
                        s2.insert(v.clone(), Term::Literal(format_num(c)));
                        vec![s2]
                    }
                    Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                    _ => vec![],
                };
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}sin", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.sin();
                return match &g.o {
                    Term::Var(v) => {
                        let mut s2 = subst.clone();
                        s2.insert(v.clone(), Term::Literal(format_num(c)));
                        vec![s2]
                    }
                    Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                    _ => vec![],
                };
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}acos", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.acos();
                if c.is_finite() {
                    return match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(c)));
                            vec![s2]
                        }
                        Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                        _ => vec![],
                    };
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}asin", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.asin();
                if c.is_finite() {
                    return match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(c)));
                            vec![s2]
                        }
                        Term::Literal(o) if o == &format_num(c) => vec![subst.clone()],
                        _ => vec![],
                    };
                }
            }
            vec![]
        }

        // ---------------------------------------------------------------------
        // log: equality builtins
        // ---------------------------------------------------------------------
        // Relational log:equalTo: succeeds iff subject and object can be made
        // equal by extending the current substitution.
        Term::Iri(p) if p == &format!("{}equalTo", LOG_NS) => {
            // Use the original goal terms with the current substitution.
            unify_term(&goal.s, &goal.o, subst).into_iter().collect()
        }

        // log:notEqualTo is the exact complement: it succeeds iff there is
        // *no* unifier for subject and object under the current substitution.
        Term::Iri(p) if p == &format!("{}notEqualTo", LOG_NS) => {
            if unify_term(&goal.s, &goal.o, subst).is_some() {
                // They *can* be equal → notEqualTo must fail.
                vec![]
            } else {
                // No way to make them equal → notEqualTo holds, no new bindings.
                vec![subst.clone()]
            }
        }

        // -----------------------------------------------------------------
        // log:collectAllIn
        // -----------------------------------------------------------------
        // (?V { clause } ?List) log:collectAllIn ?Scope.
        //
        // We:
        //  - evaluate `clause` against the current reasoning context
        //    (facts + back_rules),
        //  - for each solution σ, instantiate ?Vσ,
        //  - collect these into a list, and
        //  - unify that list with ?List.
        //
        // The ?Scope argument is ignored for now; we always use the full
        // current closure as scope, which is enough for the Dijkstra example.
        Term::Iri(p) if p == &format!("{}collectAllIn", LOG_NS) => {
            let args = match &g.s {
                Term::List(xs) if xs.len() == 3 => xs,
                _ => return vec![],
            };
            let value_templ = &args[0];
            let clause_term = &args[1];
            let list_term = &args[2];

            let body: Vec<Triple> = match clause_term {
                Term::Formula(ts) => ts.clone(),
                _ => return vec![],
            };

            if depth >= MAX_BACKWARD_DEPTH {
                return vec![];
            }

            let mut visited2: Vec<Triple> = Vec::new();
            let mut cache2: GoalCache = GoalCache::new();

            // body is already instantiated with the outer substitution,
            // because `goal` came from prove_goals(...) which applied it.
            let sols = prove_goals(
                &body[..],
                &Subst::new(),
                facts,
                back_rules,
                depth + 1,
                &mut visited2,
                var_gen,
                &mut cache2,
            );

            // Collect instantiated values, preserving order and removing
            // simple duplicates.
            let mut collected: Vec<Term> = Vec::new();
            for s_body in sols {
                let v = apply_subst_term(value_templ, &s_body);
                if !collected.contains(&v) {
                    collected.push(v);
                }
            }
            let collected_list = Term::List(collected);

            let mut out = Vec::new();
            // Bind / check the 3rd component (the ?Neighbors in Dijkstra).
            match list_term {
                Term::Var(_) | Term::List(_) | Term::OpenList(_, _) => {
                    if let Some(s2) = unify_term(list_term, &collected_list, subst) {
                        out.push(s2);
                    }
                }
                _ => {
                    if unify_term(list_term, &collected_list, subst).is_some() {
                        out.push(subst.clone());
                    }
                }
            }
            out
        }

        // ---------------------------------------------------------------------
        // list:append  -- relational, like in the N3 spec and  Prolog append/2
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}append", LIST_NS) => {
            // Subject must be a list-of-lists
            let parts = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };

            match &g.o {
                // Relational mode: object is a (possibly non-ground) list.
                // Matches N3 spec examples such as:
                //   ( (1 2) ?what ) list:append (1 2 3 4)
                //   ( ?what (3 4) ) list:append (1 2 3 4)
                Term::List(res_elems) => {
                    list_append_split(parts, res_elems, subst)
                }

                // Functional mode: subject is list-of-lists, object is anything
                // (typically a variable). Here we just concatenate all subject lists.
                //
                // This covers:
                //   ( (1) (2 3) (4) ) list:append (1 2 3 4)
                //   ( (1 2) (3 4) ) list:append ?list
                _ => {
                    let mut out_elems = Vec::<Term>::new();

                    // All s.i must be rdf:List (per N3 spec), so we require inner lists here.
                    for part in parts {
                        match part {
                            Term::List(es) => {
                                // No need for "ground" checks; variables inside the lists
                                // are fine, we just keep them structurally.
                                out_elems.extend(es.clone());
                            }
                            _ => return vec![],
                        }
                    }

                    let result = Term::List(out_elems);

                    match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), result);
                            vec![s2]
                        }
                        // Ground check: just ordinary equality.
                        _ if g.o == result => vec![subst.clone()],
                        _ => vec![],
                    }
                }
            }
        }

        // ---------------------------------------------------------------------
        // list:firstRest  (experimental, bidirectional, open tail support)
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}firstRest", LIST_NS) => {
            // Forward split of a concrete list.
            if let Term::List(xs) = &g.s {
                if xs.is_empty() { return vec![]; }
                let first = xs[0].clone();
                let rest = Term::List(xs[1..].to_vec());
                let pair = Term::List(vec![first, rest]);
                return unify_term(&g.o, &pair, subst).into_iter().collect();
            }

            // Inverse construction from (first rest).
            if let Term::List(pair) = &g.o {
                if pair.len() != 2 { return vec![]; }
                let first = &pair[0];
                let rest = &pair[1];

                match rest {
                    Term::List(rs) => {
                        let mut xs = Vec::with_capacity(1 + rs.len());
                        xs.push(first.clone());
                        xs.extend(rs.clone());
                        let constructed = Term::List(xs);
                        return unify_term(&g.s, &constructed, subst).into_iter().collect();
                    }
                    Term::Var(rv) => {
                        let constructed = Term::OpenList(vec![first.clone()], rv.clone());
                        return unify_term(&g.s, &constructed, subst).into_iter().collect();
                    }
                    Term::OpenList(rprefix, rtailv) => {
                        let mut new_prefix = Vec::with_capacity(1 + rprefix.len());
                        new_prefix.push(first.clone());
                        new_prefix.extend(rprefix.clone());
                        let constructed = Term::OpenList(new_prefix, rtailv.clone());
                        return unify_term(&g.s, &constructed, subst).into_iter().collect();
                    }
                    _ => return vec![],
                }
            }

            vec![]
        }

        // ---------------------------------------------------------------------
        // list:member / list:in / list:length / list:map
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}member", LIST_NS) => {
            let xs = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };
            let mut outs = Vec::new();
            for x in xs {
                if let Some(s2) = unify_term(&g.o, x, subst) {
                    outs.push(s2);
                }
            }
            outs
        }

        Term::Iri(p) if p == &format!("{}in", LIST_NS) => {
            let xs = match &g.o {
                Term::List(xs) => xs,
                _ => return vec![],
            };
            let mut outs = Vec::new();
            for x in xs {
                if let Some(s2) = unify_term(&g.s, x, subst) {
                    outs.push(s2);
                }
            }
            outs
        }

        Term::Iri(p) if p == &format!("{}length", LIST_NS) => {
            let xs = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };
            let n_term = Term::Literal((xs.len() as i64).to_string());
            if let Some(s2) = unify_term(&g.o, &n_term, subst) {
                vec![s2]
            } else {
                vec![]
            }
        }

        // -----------------------------------------------------------------
        // list:notMember  (Eye-style)
        // -----------------------------------------------------------------
        // ?List list:notMember ?X.
        // Succeeds iff ?X cannot be unified with any element of ?List under
        // the current substitution. Used in the Dijkstra example to ensure
        // neighbors are not already in the visited set.
        Term::Iri(p) if p == &format!("{}notMember", LIST_NS) => {
            let xs = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };
            for el in xs {
                if unify_term(&g.o, el, subst).is_some() {
                    // There *is* a way to make ?X equal to an element → fail.
                    return vec![];
                }
            }
            vec![subst.clone()]
        }

        // -----------------------------------------------------------------
        // list:reverse  (relational)
        // -----------------------------------------------------------------
        // ?L list:reverse ?R.
        // One side must be a closed list; the other side is that list reversed.
        Term::Iri(p) if p == &format!("{}reverse", LIST_NS) => {
            match (&g.s, &g.o) {
                (Term::List(xs), _) => {
                    let mut rev = xs.clone();
                    rev.reverse();
                    let rterm = Term::List(rev);
                    unify_term(&g.o, &rterm, subst).into_iter().collect()
                }
                (_, Term::List(xs)) => {
                    let mut rev = xs.clone();
                    rev.reverse();
                    let rterm = Term::List(rev);
                    unify_term(&g.s, &rterm, subst).into_iter().collect()
                }
                _ => vec![],
            }
        }

        // -----------------------------------------------------------------
        // list:sort  (Eye-style, pragmatic ordering)
        // -----------------------------------------------------------------
        // ?List list:sort ?Sorted.
        // We sort using:
        //  - numeric comparison for literal numbers
        //  - lexicographic comparison for everything else
        //  - lexicographic on sublists
        Term::Iri(p) if p == &format!("{}sort", LIST_NS) => {
            use std::cmp::Ordering;

            fn cmp_term_for_sort(a: &Term, b: &Term) -> Ordering {
                match (a, b) {
                    (Term::Literal(sa), Term::Literal(sb)) => {
                        let (lex_a, _) = literal_parts(sa);
                        let (lex_b, _) = literal_parts(sb);
                        let na = strip_quotes(&lex_a).parse::<f64>();
                        let nb = strip_quotes(&lex_b).parse::<f64>();
                        match (na.ok(), nb.ok()) {
                            (Some(va), Some(vb)) => va
                                .partial_cmp(&vb)
                                .unwrap_or(Ordering::Equal),
                            _ => lex_a.cmp(&lex_b),
                        }
                    }
                    (Term::List(xs), Term::List(ys)) => {
                        // Lexicographic on sublists.
                        let mut i = 0;
                        loop {
                            match (xs.get(i), ys.get(i)) {
                                (Some(xi), Some(yi)) => {
                                    let ord = cmp_term_for_sort(xi, yi);
                                    if ord != Ordering::Equal {
                                        return ord;
                                    }
                                    i += 1;
                                }
                                (None, Some(_)) => return Ordering::Less,
                                (Some(_), None) => return Ordering::Greater,
                                (None, None) => return Ordering::Equal,
                            }
                        }
                    }
                    (Term::Iri(ia), Term::Iri(ib)) => ia.cmp(ib),

                    // Lists before non-lists so Dijkstra queues (lists of tuples)
                    // behave as expected.
                    (Term::List(_), _) => Ordering::Less,
                    (_, Term::List(_)) => Ordering::Greater,

                    _ => format!("{:?}", a).cmp(&format!("{:?}", b)),
                }
            }

            // One side must be the input list.
            let input = match (&g.s, &g.o) {
                (Term::List(xs), _) => xs.clone(),
                (_, Term::List(xs)) => xs.clone(),
                _ => return vec![],
            };

            // Be conservative: only sort ground lists.
            if !input.iter().all(is_ground_term) {
                return vec![];
            }

            let mut sorted = input;
            sorted.sort_by(|a, b| cmp_term_for_sort(a, b));
            let sorted_term = Term::List(sorted);

            match (&g.s, &g.o) {
                (Term::List(_), _) => {
                    unify_term(&g.o, &sorted_term, subst).into_iter().collect()
                }
                (_, Term::List(_)) => {
                    unify_term(&g.s, &sorted_term, subst).into_iter().collect()
                }
                _ => vec![],
            }
        }

        // Pragmatic eyeling subset of list:map:
        //   ((inputList) predicateIRI) list:map outputList
        Term::Iri(p) if p == &format!("{}map", LIST_NS) => {
            let args = match &g.s {
                Term::List(xs) if xs.len() == 2 => xs,
                _ => return vec![],
            };

            let input = match &args[0] {
                Term::List(xs) => xs,
                _ => return vec![],
            };

            let pred = match &args[1] {
                Term::Iri(i) => Term::Iri(i.clone()),
                _ => return vec![],
            };
            if !is_builtin_pred(&pred) { return vec![]; }
            if !input.iter().all(is_ground_term) { return vec![]; }

            let mut results: Vec<Term> = Vec::with_capacity(input.len());
            for el in input {
                let yvar = Term::Var("_mapY".to_string());
                let goal = Triple { s: el.clone(), p: pred.clone(), o: yvar.clone() };
                let sols = eval_builtin(&goal, subst, facts, back_rules, depth + 1, var_gen);
                if sols.is_empty() { return vec![]; }
                let yval = apply_subst_term(&yvar, &sols[0]);
                if matches!(yval, Term::Var(_)) { return vec![]; }
                results.push(yval);
            }

            let out_list = Term::List(results);
            unify_term(&g.o, &out_list, subst).into_iter().collect()
        }

        _ => vec![],
    }
}

// =====================================================================================
// Backward proof (SLD-style)
// =====================================================================================
//
// This is Prolog-ish search:
//
// prove_goals([g1,g2,...], subst) returns all substitutions that satisfy all goals.
//
// We also:
// - standardize rules apart (fresh vars per use)
// - consult facts + backward rules + builtins
// - keep a visited stack to avoid trivial loops

fn standardize_rule(rule: &Rule, gen: &mut usize) -> Rule {
    fn rename_term(
        t: &Term,
        vmap: &mut HashMap<String, String>,
        gen: &mut usize,
    ) -> Term {
        match t {
            Term::Var(v) => {
                let nv = vmap.entry(v.clone()).or_insert_with(|| {
                    let name = format!("{}__{}", v, *gen);
                    *gen += 1;
                    name
                }).clone();
                Term::Var(nv)
            }

            Term::List(xs) => {
                Term::List(xs.iter().map(|e| rename_term(e, vmap, gen)).collect())
            }

            Term::OpenList(xs, tailv) => {
                let new_xs: Vec<Term> =
                    xs.iter().map(|e| rename_term(e, vmap, gen)).collect();
                let new_tail = vmap.entry(tailv.clone()).or_insert_with(|| {
                    let name = format!("{}__{}", tailv, *gen);
                    *gen += 1;
                    name
                }).clone();
                Term::OpenList(new_xs, new_tail)
            }

            Term::Formula(ts) => Term::Formula(
                ts.iter().map(|tr| Triple {
                    s: rename_term(&tr.s, vmap, gen),
                    p: rename_term(&tr.p, vmap, gen),
                    o: rename_term(&tr.o, vmap, gen),
                }).collect()
            ),

            _ => t.clone(),
        }
    }

    let mut vmap2 = HashMap::new();
    let premise = rule.premise.iter().map(|tr| Triple {
        s: rename_term(&tr.s, &mut vmap2, gen),
        p: rename_term(&tr.p, &mut vmap2, gen),
        o: rename_term(&tr.o, &mut vmap2, gen),
    }).collect();

    let conclusion = rule.conclusion.iter().map(|tr| Triple {
        s: rename_term(&tr.s, &mut vmap2, gen),
        p: rename_term(&tr.p, &mut vmap2, gen),
        o: rename_term(&tr.o, &mut vmap2, gen),
    }).collect();

    Rule {
        premise,
        conclusion,
        is_forward: rule.is_forward,
        is_fuse: rule.is_fuse,
    }
}

/// Solve a single goal triple under an *empty* substitution, possibly
/// using a tiny memo table. The goal we get here is already instantiated
/// with the outer substitution.
fn solve_single_goal(
    goal: &Triple,
    facts: &[Triple],
    back_rules: &[Rule],
    depth: usize,
    visited: &mut Vec<Triple>,
    var_gen: &mut usize,
    cache: &mut GoalCache,
) -> Vec<Subst> {
    // Builtins are pure (no side effects). We still evaluate them
    // directly, starting from an empty substitution, but we also pass
    // the current fact base and backward rules for things like
    // log:collectAllIn.
    if is_builtin_pred(&goal.p) {
        return eval_builtin(goal, &Subst::new(), facts, back_rules, depth, var_gen);
    }

    if depth > MAX_BACKWARD_DEPTH {
        return vec![];
    }

    // Memoization: if we've already solved this goal under the current
    // (facts, back_rules) snapshot, reuse the delta substitutions.
    if let Some(cached) = cache.get(goal) {
        return cached.clone();
    }

    // Loop check to avoid trivial cycles like ?X :p ?Y <= {?X :p ?Y}
    if visited.contains(goal) {
        return vec![];
    }
    visited.push(goal.clone());

    let mut results: Vec<Subst> = Vec::new();

    // 1) Try matching known facts, starting from an empty substitution.
    for f in facts {
        if let Some(s2) = unify_triple(goal, f, &Subst::new()) {
            results.push(s2);
        }
    }

    // 2) Try backward rules (Horn head must be one triple).
    for r in back_rules {
        if r.conclusion.len() != 1 {
            continue;
        }

        let r_std = standardize_rule(r, var_gen);
        let head = &r_std.conclusion[0];

        if let Some(s2) = unify_triple(head, goal, &Subst::new()) {
            // Instantiate the body under the head substitution s2.
            let body: Vec<Triple> = r_std
                .premise
                .iter()
                .map(|b| apply_subst_triple(b, &s2))
                .collect();

            // Prove the body starting from s2. Any solution is a delta
            // substitution for this goal (w.r.t. an empty outer subst).
            let body_solutions =
                prove_goals(&body, &s2, facts, back_rules, depth + 1, visited, var_gen, cache);

            results.extend(body_solutions);
        }
    }

    visited.pop();

    // Store (possibly empty) results in the cache so we don't recompute
    // this goal again during this forward-rule proof.
    cache.insert(goal.clone(), results.clone());
    results
}

/// Prove a conjunction of goals under an *outer* substitution, using
/// solve_single_goal for the first goal and then recursing on the rest.
fn prove_goals(
    goals: &[Triple],
    subst: &Subst,
    facts: &[Triple],
    back_rules: &[Rule],
    depth: usize,
    visited: &mut Vec<Triple>,
    var_gen: &mut usize,
    cache: &mut GoalCache,
) -> Vec<Subst> {
    if goals.is_empty() {
        return vec![subst.clone()];
    }
    if depth > MAX_BACKWARD_DEPTH {
        return vec![];
    }

    // Apply the current substitution to the first goal; from this point on
    // we can solve it starting from an empty substitution and treat the
    // result as a "delta" to compose with `subst`.
    let goal0 = apply_subst_triple(&goals[0], subst);
    let rest = &goals[1..];

    let mut results: Vec<Subst> = Vec::new();

    // Solve the first goal (with memoization for non-builtins).
    let deltas = solve_single_goal(
        &goal0,
        facts,
        back_rules,
        depth,
        visited,
        var_gen,
        cache,
    );

    for delta in deltas {
        if let Some(composed) = compose_subst(subst, &delta) {
            if rest.is_empty() {
                results.push(composed);
            } else {
                let mut tail_solutions = prove_goals(
                    rest,
                    &composed,
                    facts,
                    back_rules,
                    depth + 1,
                    visited,
                    var_gen,
                    cache,
                );
                results.append(&mut tail_solutions);
            }
        }
    }

    results
}

/// Forward chaining to fixpoint.
///
/// This is classic data-driven reasoning:
/// - We keep a database of ground facts.
/// - We repeatedly fire forward rules whose premises are provable
///   (using facts + backward rules + builtins).
/// - We collect all newly derived forward facts together with a
///   short justification (which rule fired with which premises).
fn forward_chain(
    mut facts: Vec<Triple>,
    forward_rules: &mut Vec<Rule>,
    back_rules: &mut Vec<Rule>,
) -> Vec<DerivedFact> {
    let mut fact_set: HashSet<Triple> = facts.iter().cloned().collect();
    let mut derived_forward: Vec<DerivedFact> = vec![];
    let mut var_gen = 0usize;
    let mut skolem_counter = 0usize; // global counter for _:sk_N

    loop {
        let mut changed = false;

        // We may add new forward/backward rules while looping, so iterate by index.
        let mut i = 0usize;
        while i < forward_rules.len() {
            let r = forward_rules[i].clone();
            i += 1;

            let empty = Subst::new();
            let mut visited = vec![];
            // Tiny memo table for this one forward rule application.
            let mut goal_cache: GoalCache = GoalCache::new();

            // NOTE: pass current backward rules as a slice
            let sols = prove_goals(
                &r.premise,
                &empty,
                &facts,
                &back_rules[..],
                0,
                &mut visited,
                &mut var_gen,
                &mut goal_cache,
            );

            // --- inference fuse handling ---
            if r.is_fuse && !sols.is_empty() {
                eprintln!("# Inference fuse triggered: a {{ ... }} => false.  rule fired.");
                std::process::exit(2);
            }

            for s in sols {
                // For explanation: body instantiated under this solution.
                let instantiated_premises: Vec<Triple> = r
                    .premise
                    .iter()
                    .map(|b| apply_subst_triple(b, &s))
                    .collect();

                // New head existentials per rule application:
                let mut blank_map: HashMap<String, String> = HashMap::new();

                for cpat in &r.conclusion {
                    let instantiated = apply_subst_triple(cpat, &s);

                    // --- rule-producing conclusions ---------------------------------
                    // Handle both:
                    //   { ... } log:implies { ... } → new forward rule
                    //   { ... } log:impliedBy { ... } → new backward rule
                    let is_fw_rule_triple =
                        is_log_implies(&instantiated.p)
                            && matches!(instantiated.s, Term::Formula(_))
                            && matches!(instantiated.o, Term::Formula(_));
                    let is_bw_rule_triple =
                        is_log_implied_by(&instantiated.p)
                            && matches!(instantiated.s, Term::Formula(_))
                            && matches!(instantiated.o, Term::Formula(_));

                    if is_fw_rule_triple || is_bw_rule_triple {
                        // 1) Keep the triple itself as derived output, even if non-ground,
                        //    so it shows up in the final printing.
                        if !fact_set.contains(&instantiated)
                            && !has_alpha_equiv(&fact_set, &instantiated)
                        {
                            fact_set.insert(instantiated.clone());
                            facts.push(instantiated.clone());
                            derived_forward.push(DerivedFact {
                                fact: instantiated.clone(),
                                rule: r.clone(),
                                premises: instantiated_premises.clone(),
                                subst: s.clone(),
                            });
                            changed = true;
                        }

                        // 2) Turn it into a *live* rule (forward or backward).
                        if let (Term::Formula(left), Term::Formula(right)) =
                            (&instantiated.s, &instantiated.o)
                        {
                            if is_fw_rule_triple {
                                // { left } log:implies { right } ≅ { left } => { right }
                                let (premise, conclusion) =
                                    lift_blank_rule_vars(left.clone(), right.clone());
                                let new_rule = Rule {
                                    premise,
                                    conclusion,
                                    is_forward: true,
                                    is_fuse: false,
                                };

                                let already_there = forward_rules.iter().any(|rr| {
                                    rr.is_forward == new_rule.is_forward
                                        && rr.is_fuse == new_rule.is_fuse
                                        && rr.premise == new_rule.premise
                                        && rr.conclusion == new_rule.conclusion
                                });
                                if !already_there {
                                    forward_rules.push(new_rule);
                                }
                            } else if is_bw_rule_triple {
                                // { left } log:impliedBy { right }
                                // means: { left } <= { right }
                                // Backward Rule: head = left, body = right
                                // Internally: premise = body, conclusion = head
                                let (premise, conclusion) =
                                    lift_blank_rule_vars(right.clone(), left.clone());
                                let new_rule = Rule {
                                    premise,
                                    conclusion,
                                    is_forward: false,
                                    is_fuse: false,
                                };

                                let already_there = back_rules.iter().any(|rr| {
                                    rr.is_forward == new_rule.is_forward
                                        && rr.is_fuse == new_rule.is_fuse
                                        && rr.premise == new_rule.premise
                                        && rr.conclusion == new_rule.conclusion
                                });
                                if !already_there {
                                    back_rules.push(new_rule);
                                }
                            }
                        }

                        // Skip normal fact handling for rule triples.
                        continue;
                    }

                    // --- normal fact conclusion -----------------------------------
                    // Normal fact conclusion: skolemize blanks into _:sk_N
                    let inst = skolemize_triple(&instantiated, &mut blank_map, &mut skolem_counter);

                    // Only add fully ground facts (no variables/OpenList)
                    if !is_ground_triple(&inst) {
                        continue;
                    }

                    // Avoid duplicates up to blank renaming.
                    if fact_set.contains(&inst) || has_alpha_equiv(&fact_set, &inst) {
                        continue;
                    }

                    fact_set.insert(inst.clone());
                    facts.push(inst.clone());
                    derived_forward.push(DerivedFact {
                        fact: inst.clone(),
                        rule: r.clone(),
                        premises: instantiated_premises.clone(),
                        subst: s.clone(),
                    });
                    changed = true;
                }
            }
        }

        if !changed {
            break;
        }
    }

    derived_forward
}

// =====================================================================================
// Pretty printing as N3/Turtle
// =====================================================================================

fn term_to_n3(t: &Term, pref: &PrefixEnv) -> String {
    match t {
        Term::Iri(i) => {
            if let Some(q) = pref.shrink_iri(i) {
                q
            } else if i.starts_with("_:") {
                i.clone()
            } else {
                format!("<{}>", i)
            }
        }

        Term::Literal(l) => l.clone(),
        Term::Var(v) => format!("?{}", v),
        Term::Blank(b) => b.clone(),

        Term::List(xs) => {
            let inside: Vec<String> = xs.iter().map(|e| term_to_n3(e, pref)).collect();
            format!("({})", inside.join(" "))
        }

        Term::OpenList(prefix, tailv) => {
            let mut inside: Vec<String> =
                prefix.iter().map(|e| term_to_n3(e, pref)).collect();
            inside.push(format!("?{}", tailv));
            format!("({})", inside.join(" "))
        }

        // pretty-print formulas with indentation
        Term::Formula(ts) => {
            let mut s = String::from("{\n");
            for tr in ts {
                let line = triple_to_n3(tr, pref);
                // indent each triple inside the graph term
                s.push_str("    ");
                s.push_str(line.trim_end());
                s.push('\n');
            }
            s.push('}');
            s
        }
    }
}

fn triple_to_n3(tr: &Triple, prefixes: &PrefixEnv) -> String {
    // Pretty-print rule triples of the form:
    //   { ... } log:implies { ... }   as   { ... } => { ... } .
    if is_log_implies(&tr.p) {
        if let (Term::Formula(prem), Term::Formula(concl)) = (&tr.s, &tr.o) {
            let prem_s = term_to_n3(&Term::Formula(prem.clone()), prefixes);
            let concl_s = term_to_n3(&Term::Formula(concl.clone()), prefixes);
            return format!("{} => {} .", prem_s, concl_s);
        }
    }

    // And similarly:
    //   { ... } log:impliedBy { ... }  as   { ... } <= { ... } .
    if is_log_implied_by(&tr.p) {
        if let (Term::Formula(head), Term::Formula(body)) = (&tr.s, &tr.o) {
            let head_s = term_to_n3(&Term::Formula(head.clone()), prefixes);
            let body_s = term_to_n3(&Term::Formula(body.clone()), prefixes);
            return format!("{} <= {} .", head_s, body_s);
        }
    }

    let s = term_to_n3(&tr.s, prefixes);
    // rdf:type prints as `a` in Turtle/N3.
    let p = if is_rdf_type_pred(&tr.p) {
        "a".to_string()
    } else {
        term_to_n3(&tr.p, prefixes)
    };
    let o = term_to_n3(&tr.o, prefixes);
    format!("{} {} {} .", s, p, o)
}

/// Pretty-print a derived fact together with a small mathematical-English proof
/// as N3 comments. The triple itself is **not** printed here; caller prints it.
fn print_explanation(df: &DerivedFact, prefixes: &PrefixEnv) {
    // Header
    println!("# ----------------------------------------------------------------------");
    println!("# Proof for derived triple:");
    for line in triple_to_n3(&df.fact, prefixes).lines() {
        let trimmed = line.trim_end();
        if !trimmed.is_empty() {
            println!("#   {}", trimmed);
        }
    }

    if df.premises.is_empty() {
        println!(
            "# This triple is the head of a forward rule with an empty premise,")
        ;
        println!("# so it holds unconditionally whenever the program is loaded.");
    } else {
        println!(
            "# It holds because the following instantiated premises are all satisfied:"
        );
        for prem in &df.premises {
            for line in triple_to_n3(prem, prefixes).lines() {
                let trimmed = line.trim_end();
                if !trimmed.is_empty() {
                    println!("#   {}", trimmed);
                }
            }
        }
    }

    println!("# via the schematic forward rule:");
    println!("#   {{");
    for tr in &df.rule.premise {
        for line in triple_to_n3(tr, prefixes).lines() {
            let trimmed = line.trim_end();
            if !trimmed.is_empty() {
                println!("#     {}", trimmed);
            }
        }
    }
    println!("#   }} => {{");
    for tr in &df.rule.conclusion {
        for line in triple_to_n3(tr, prefixes).lines() {
            let trimmed = line.trim_end();
            if !trimmed.is_empty() {
                println!("#     {}", trimmed);
            }
        }
    }
    println!("#   }}");

    // Only show bindings for variables that actually occur in *this* rule.
    // The backward prover may introduce many internal variables (A__1234, ...)
    // that are irrelevant for understanding this inference step.
    let rule_vars = vars_in_rule(&df.rule);

    let mut visible: Vec<_> = df
        .subst
        .iter()
        .filter(|(name, _)| rule_vars.contains(*name))
        .collect();

    if !visible.is_empty() {
        println!("# with substitution (on rule variables):");
        // Sort by variable name for stable, deterministic output
        visible.sort_by(|(a, _), (b, _)| a.cmp(b));
        for (v, term) in visible {
            println!("#   ?{} = {}", v, term_to_n3(term, prefixes));
        }
    }

    println!("# Therefore the derived triple above is entailed by the rules and facts.");
    println!("# ----------------------------------------------------------------------");
}

// =====================================================================================
// CLI entry point
// =====================================================================================
fn main() {
    // `env::args()` gives an iterator of CLI args.
    // Collecting into Vec is fine here (tiny inputs).
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: eyeling <file.n3>");
        std::process::exit(1);
    }
    let text = fs::read_to_string(&args[1]).expect("read file");
    let toks = lex(&text);
    let mut p = Parser::new(toks);
    let (prefixes, triples, mut frules, mut brules) = p.parse_document();
    // Keep only ground input facts for the forward database.
    let facts: Vec<Triple> = triples.into_iter().filter(is_ground_triple).collect();

    // Run the engine!
    let derived = forward_chain(facts, &mut frules, &mut brules);

    // Collect just the triples for prefix analysis.
    let derived_triples: Vec<Triple> = derived.iter().map(|df| df.fact.clone()).collect();

    // Print only prefixes needed by derived output.
    let used_prefixes = prefixes.prefixes_used_for_output(&derived_triples);
    for (pfx, base) in &used_prefixes {
        if pfx.is_empty() {
            println!("@prefix : <{}> .", base);
        } else {
            println!("@prefix {}: <{}> .", pfx, base);
        }
    }
    if !derived.is_empty() && !used_prefixes.is_empty() {
        println!();
    }

    // Print derived triples interlaced with comment proofs.
    for df in derived {
        print_explanation(&df, &prefixes);
        println!("{}", triple_to_n3(&df.fact, &prefixes));
        println!();
    }
}

