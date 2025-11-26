// =====================================================================================
// eyelite — a minimal Notation3 (N3) reasoner in Rust
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
const MAX_BACKWARD_DEPTH: usize = 2000;

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
}

/// Substitution mapping variable name -> term.
/// Rust tip: `type Foo = ...` makes a readable alias.
type Subst = HashMap<String, Term>;

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
}

impl Parser {
    fn new(toks: Vec<Token>) -> Self {
        Parser {
            toks,
            pos: 0,
            prefixes: PrefixEnv::new(),
            blank_counter: 0,
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

            TokenKind::Ident(s) => {
                if s == "a" {
                    Term::Iri(format!("{}type", RDF_NS))
                } else if s.contains(':') {
                    Term::Iri(self.prefixes.expand_qname(&s))
                } else {
                    // Bareword treated as IRI-ish for simplicity.
                    Term::Iri(s)
                }
            }

            TokenKind::Literal(mut s) => {
                // Typed literal: "..."^^xsd:date
                if *self.peek() == TokenKind::HatHat {
                    self.next(); // consume ^^
                    let dt_iri = match self.next() {
                        TokenKind::IriRef(i) => i,
                        TokenKind::Ident(qn) => {
                            if qn.contains(':') { self.prefixes.expand_qname(&qn) }
                            else { qn }
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

    /// Parse blank node `[]`.
    ///
    /// We currently ignore property lists like `[ :p 1 ]` and just create a blank.
    fn parse_blank(&mut self) -> Term {
        if *self.peek() == TokenKind::RBracket {
            self.next();
            self.blank_counter += 1;
            return Term::Blank(format!("_:b{}", self.blank_counter));
        }

        while *self.peek() != TokenKind::RBracket { self.next(); }
        self.next();
        self.blank_counter += 1;
        Term::Blank(format!("_:b{}", self.blank_counter))
    }

    /// Parse `{ ... }` formula.
    ///
    /// Inside formulas the last '.' can be omitted, so we accept either '.' or '}'.
    fn parse_formula(&mut self) -> Term {
        let mut triples = vec![];

        while *self.peek() != TokenKind::RBrace {
            let first = self.parse_term();

            match self.peek() {
                TokenKind::OpImplies | TokenKind::OpImpliedBy => {
                    // Nested rules are ignored in this subset.
                    self.next();
                    self.parse_term();

                    match self.peek() {
                        TokenKind::Dot => { self.next(); }
                        TokenKind::RBrace => {}
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                }
                _ => {
                    triples.append(&mut self.parse_predicate_object_list(first));

                    match self.peek() {
                        TokenKind::Dot => { self.next(); }
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
                if *self.peek() == TokenKind::Dot { break; }
                continue;
            }

            break;
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
        // For <= rules, swap to keep premise/body on left in Rule.
        let (premise_term, concl_term) =
            if is_forward { (left, right) } else { (right, left) };

        let premise = match premise_term {
            Term::Formula(ts) => ts,
            Term::Literal(lit) if lit == "true" => vec![],
            _ => vec![],
        };

        let conclusion = match concl_term {
            Term::Formula(ts) => ts,
            _ => vec![],
        };

        Rule { premise, conclusion, is_forward }
    }
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
    if let Term::Literal(s) = t { s.parse::<f64>().ok() } else { None }
}

fn format_num(n: f64) -> String {
    if n.fract() == 0.0 { format!("{}", n as i64) } else { format!("{}", n) }
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

/// Evaluate a builtin triple under current substitution.
/// Returns zero or more new substitutions (for backtracking).
fn eval_builtin(goal: &Triple, subst: &Subst) -> Vec<Subst> {
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

        // ---------------------------------------------------------------------
        // math: arithmetic
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}sum", MATH_NS) => {
            // (a b c) math:sum ?z
            if let Term::List(xs) = &g.s {
                if xs.len() >= 2 && xs.iter().all(|t| parse_num(t).is_some()) {
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
                    // Numeric difference
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

                    // Date(dateTime) difference -> duration
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
        Term::Iri(p) if p == &format!("{}equalTo", LOG_NS) => {
            if g.s == g.o { vec![subst.clone()] } else { vec![] }
        }

        Term::Iri(p) if p == &format!("{}notEqualTo", LOG_NS) => {
            if g.s != g.o { vec![subst.clone()] } else { vec![] }
        }

        // ---------------------------------------------------------------------
        // list:append  (concatenate list-of-lists)
        // ---------------------------------------------------------------------
        Term::Iri(p) if p == &format!("{}append", LIST_NS) => {
            let parts = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };

            let mut out_elems = Vec::new();
            for part in parts {
                match part {
                    Term::List(es) => {
                        if !es.iter().all(is_ground_term) { return vec![]; }
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
                Term::List(_) if g.o == result => vec![subst.clone()],
                _ => vec![],
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

        // Pragmatic eyelite subset of list:map:
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
                let sols = eval_builtin(&goal, subst);
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

    Rule { premise, conclusion, is_forward: rule.is_forward }
}

fn prove_goals(
    goals: &[Triple],
    subst: &Subst,
    facts: &[Triple],
    back_rules: &[Rule],
    depth: usize,
    visited: &mut Vec<Triple>,
    var_gen: &mut usize,
) -> Vec<Subst> {
    if goals.is_empty() {
        return vec![subst.clone()];
    }
    if depth > MAX_BACKWARD_DEPTH {
        return vec![];
    }

    let goal0 = apply_subst_triple(&goals[0], subst);
    let rest = &goals[1..];

    // Builtins get evaluated directly.
    if is_builtin_pred(&goal0.p) {
        let subs = eval_builtin(&goal0, subst);
        let mut out = vec![];
        for s2 in subs {
            out.extend(prove_goals(rest, &s2, facts, back_rules, depth + 1, visited, var_gen));
        }
        return out;
    }

    // Loop check
    if visited.contains(&goal0) {
        return vec![];
    }
    visited.push(goal0.clone());

    let mut results = vec![];

    // 1) Try matching known facts.
    for f in facts {
        if let Some(s2) = unify_triple(&goal0, f, subst) {
            results.extend(prove_goals(rest, &s2, facts, back_rules, depth + 1, visited, var_gen));
        }
    }

    // 2) Try backward rules (Horn head must be one triple).
    for r in back_rules {
        if r.conclusion.len() != 1 {
            continue;
        }
        let r_std = standardize_rule(r, var_gen);
        let head = &r_std.conclusion[0];

        if let Some(s2) = unify_triple(head, &goal0, subst) {
            let body: Vec<Triple> = r_std.premise.iter()
                .map(|b| apply_subst_triple(b, &s2))
                .collect();

            let body_solutions =
                prove_goals(&body, &s2, facts, back_rules, depth + 1, visited, var_gen);

            for sb in body_solutions {
                results.extend(prove_goals(rest, &sb, facts, back_rules, depth + 1, visited, var_gen));
            }
        }
    }

    visited.pop();
    results
}

// =====================================================================================
// Forward chaining to fixpoint
// =====================================================================================
//
// This is classic data-driven reasoning.
// Loop until no new facts are derived.
//
// Each forward rule is applied by proving its premise (with backward rules/builtins),
// then instantiating the conclusion with the resulting substitutions.

fn forward_chain(
    mut facts: Vec<Triple>,
    forward_rules: &[Rule],
    back_rules: &[Rule],
) -> Vec<Triple> {
    let mut fact_set: HashSet<Triple> = facts.iter().cloned().collect();
    let mut derived_forward: Vec<Triple> = vec![];
    let mut var_gen = 0usize;

    loop {
        let mut changed = false;

        for r in forward_rules {
            let empty = Subst::new();
            let mut visited = vec![];

            let sols = prove_goals(
                &r.premise,
                &empty,
                &facts,
                back_rules,
                0,
                &mut visited,
                &mut var_gen,
            );

            for s in sols {
                for cpat in &r.conclusion {
                    let inst = apply_subst_triple(cpat, &s);

                    // Only add fully ground derived facts.
                    if !is_ground_triple(&inst) {
                        continue;
                    }

                    if !fact_set.contains(&inst) {
                        fact_set.insert(inst.clone());
                        facts.push(inst.clone());
                        derived_forward.push(inst);
                        changed = true;
                    }
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

        Term::Formula(ts) => {
            let mut s = String::from("{ ");
            for tr in ts {
                s.push_str(&format!(
                    "{} {} {} .\n",
                    term_to_n3(&tr.s, pref),
                    term_to_n3(&tr.p, pref),
                    term_to_n3(&tr.o, pref),
                ));
            }
            s.push_str("}");
            s
        }
    }
}

fn triple_to_n3(tr: &Triple, prefixes: &PrefixEnv) -> String {
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

// =====================================================================================
// CLI entry point
// =====================================================================================

fn main() {
    // `env::args()` gives an iterator of CLI args.
    // Collecting into Vec<String> is fine here (tiny inputs).
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("Usage: eyelite <file.n3>");
        std::process::exit(1);
    }

    let text = fs::read_to_string(&args[1]).expect("read file");

    let toks = lex(&text);
    let mut p = Parser::new(toks);
    let (prefixes, triples, frules, brules) = p.parse_document();

    // Keep only ground input facts for the forward database.
    let facts: Vec<Triple> = triples.into_iter().filter(is_ground_triple).collect();

    // Run the engine!
    let derived = forward_chain(facts, &frules, &brules);

    // Print only prefixes needed by derived output.
    let used_prefixes = prefixes.prefixes_used_for_output(&derived);
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

    // Print derived triples.
    for t in derived {
        println!("{}", triple_to_n3(&t, &prefixes));
    }
}

