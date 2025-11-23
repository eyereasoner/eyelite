// Minimal N3 forward + backward chainer (practical subset).
//
// Behavior:
// - Parses a pragmatic N3 subset.
// - Uses backward rules (<=) as goal-directed "user builtins"
//   during matching of forward rule premises.
// - Runs forward chaining to fixpoint.
// - Prints ONLY newly forward-derived triples, as N3.

use std::collections::{HashMap, HashSet};
use std::env;
use std::fs;

use chrono::{DateTime, Local, NaiveDate, TimeZone, Utc};

const RDF_NS: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
const RDFS_NS: &str = "http://www.w3.org/2000/01/rdf-schema#";
const XSD_NS: &str = "http://www.w3.org/2001/XMLSchema#";
const LOG_NS: &str = "http://www.w3.org/2000/10/swap/log#";
const MATH_NS: &str = "http://www.w3.org/2000/10/swap/math#";
const STRING_NS: &str = "http://www.w3.org/2000/10/swap/string#";
const LIST_NS: &str = "http://www.w3.org/2000/10/swap/list#";
const TIME_NS: &str = "http://www.w3.org/2000/10/swap/time#";

const MAX_BACKWARD_DEPTH: usize = 2000;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
enum Term {
    Iri(String),
    Literal(String), // numbers, booleans, or quoted strings (kept raw, may include ^^<dt>)
    Var(String),
    Blank(String),
    List(Vec<Term>),
    OpenList(Vec<Term>, String),
    Formula(Vec<Triple>), // conjunction of triple patterns
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
struct Triple {
    s: Term,
    p: Term,
    o: Term,
}

#[derive(Clone, Debug)]
struct Rule {
    premise: Vec<Triple>,
    conclusion: Vec<Triple>,
    is_forward: bool,
}

type Subst = HashMap<String, Term>;

#[derive(Clone, Debug, PartialEq)]
enum TokenKind {
    AtPrefix,
    AtBase,
    OpImplies,
    OpImpliedBy,
    LBrace,
    RBrace,
    LParen,
    RParen,
    LBracket,
    RBracket,
    Semicolon,
    Comma,
    Dot,
    Ident(String),
    IriRef(String),
    Var(String),
    Literal(String),
    HatHat,
    EOF,
}

#[derive(Clone, Debug)]
struct Token {
    kind: TokenKind,
}

fn is_ws(c: char) -> bool {
    c.is_whitespace()
}

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '-' || c == ':'
}

fn lex(input: &str) -> Vec<Token> {
    let mut chars = input.chars().peekable();
    let mut tokens = Vec::new();

    while let Some(&c) = chars.peek() {
        if is_ws(c) {
            chars.next();
            continue;
        }

        if c == '#' {
            // comment to end of line
            while let Some(cc) = chars.next() {
                if cc == '\n' || cc == '\r' {
                    break;
                }
            }
            continue;
        }

        // two-char operators
        if c == '=' {
            chars.next();
            if let Some('>') = chars.peek() {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::OpImplies,
                });
                continue;
            } else {
                panic!("Unexpected '='");
            }
        }

        if c == '<' {
            chars.next();
            if let Some('=') = chars.peek() {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::OpImpliedBy,
                });
                continue;
            }
            // IRIREF: <...>
            let mut iri = String::new();
            while let Some(cc) = chars.next() {
                if cc == '>' {
                    break;
                }
                iri.push(cc);
            }
            tokens.push(Token {
                kind: TokenKind::IriRef(iri),
            });
            continue;
        }

        // datatype operator ^^
        if c == '^' {
            chars.next();
            if let Some('^') = chars.peek() {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::HatHat,
                });
                continue;
            } else {
                panic!("Unexpected '^' (did you mean ^^?)");
            }
        }

        // punctuation
        match c {
            '{' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::LBrace,
                });
                continue;
            }
            '}' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::RBrace,
                });
                continue;
            }
            '(' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::LParen,
                });
                continue;
            }
            ')' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::RParen,
                });
                continue;
            }
            '[' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::LBracket,
                });
                continue;
            }
            ']' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::RBracket,
                });
                continue;
            }
            ';' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::Semicolon,
                });
                continue;
            }
            ',' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::Comma,
                });
                continue;
            }
            '.' => {
                chars.next();
                tokens.push(Token {
                    kind: TokenKind::Dot,
                });
                continue;
            }
            '"' => {
                // string literal
                chars.next();
                let mut s = String::new();
                while let Some(cc) = chars.next() {
                    if cc == '\\' {
                        if let Some(esc) = chars.next() {
                            s.push('\\');
                            s.push(esc);
                        }
                        continue;
                    }
                    if cc == '"' {
                        break;
                    }
                    s.push(cc);
                }
                tokens.push(Token {
                    kind: TokenKind::Literal(format!("\"{}\"", s)),
                });
                continue;
            }
            '?' => {
                chars.next();
                let mut name = String::new();
                while let Some(&cc) = chars.peek() {
                    if is_name_char(cc) {
                        name.push(cc);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token {
                    kind: TokenKind::Var(name),
                });
                continue;
            }
            '@' => {
                chars.next();
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
                    "prefix" => tokens.push(Token {
                        kind: TokenKind::AtPrefix,
                    }),
                    "base" => tokens.push(Token {
                        kind: TokenKind::AtBase,
                    }),
                    _ => panic!("Unknown directive @{}", word),
                }
                continue;
            }
            _ => {}
        }

        // numeric literal (so we can remove '.' from identifiers but still support floats)
        if c.is_ascii_digit()
            || (c == '-' && {
                let mut it = chars.clone();
                it.next(); // skip '-'
                matches!(it.peek(), Some(d) if d.is_ascii_digit())
            })
        {
            let mut num = String::new();
            num.push(chars.next().unwrap());
            while let Some(&cc) = chars.peek() {
                if cc.is_ascii_digit() {
                    num.push(cc);
                    chars.next();
                    continue;
                }
                if cc == '.' {
                    // only keep '.' if it's a decimal point (followed by digit)
                    let mut it = chars.clone();
                    it.next(); // skip '.'
                    if matches!(it.peek(), Some(d) if d.is_ascii_digit()) {
                        num.push('.');
                        chars.next();
                        continue;
                    } else {
                        break; // '.' is statement terminator
                    }
                }
                break;
            }
            tokens.push(Token {
                kind: TokenKind::Literal(num),
            });
            continue;
        }

        // ident / keyword
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

        if word == "true" || word == "false" {
            tokens.push(Token {
                kind: TokenKind::Literal(word),
            });
        } else if word.chars().all(|ch| ch.is_ascii_digit() || ch == '.' || ch == '-') {
            tokens.push(Token {
                kind: TokenKind::Literal(word),
            });
        } else {
            tokens.push(Token {
                kind: TokenKind::Ident(word),
            });
        }
    }

    tokens.push(Token {
        kind: TokenKind::EOF,
    });
    tokens
}

#[derive(Clone, Debug)]
struct PrefixEnv {
    map: HashMap<String, String>, // prefix -> base IRI
}

impl PrefixEnv {
    fn new() -> Self {
        let mut map = HashMap::new();
        map.insert("rdf".to_string(), RDF_NS.to_string());
        map.insert("rdfs".to_string(), RDFS_NS.to_string());
        map.insert("xsd".to_string(), XSD_NS.to_string());
        map.insert("log".to_string(), LOG_NS.to_string());
        map.insert("math".to_string(), MATH_NS.to_string());
        map.insert("string".to_string(), STRING_NS.to_string());
        map.insert("list".to_string(), LIST_NS.to_string());
        map.insert("time".to_string(), TIME_NS.to_string());
        map.insert("".to_string(), "".to_string()); // default : prefix
        PrefixEnv { map }
    }

    fn set(&mut self, pref: &str, base: &str) {
        self.map.insert(pref.to_string(), base.to_string());
    }

    fn expand_qname(&self, q: &str) -> String {
        if let Some(idx) = q.find(':') {
            let (p, local) = q.split_at(idx);
            let local = &local[1..]; // skip ':'
            let base = self
                .map
                .get(p)
                .cloned()
                .unwrap_or_else(|| "".to_string());
            if !base.is_empty() {
                return format!("{}{}", base, local);
            }
        }
        q.to_string()
    }

    fn shrink_iri(&self, iri: &str) -> Option<String> {
        let mut best: Option<(String, String)> = None; // (prefix, local)
        for (p, base) in &self.map {
            if base.is_empty() {
                continue;
            }
            if iri.starts_with(base) {
                let local = &iri[base.len()..];
                if local.is_empty() {
                    continue;
                }
                let cand = (p.clone(), local.to_string());
                if best.is_none() || cand.1.len() < best.as_ref().unwrap().1.len() {
                    best = Some(cand);
                }
            }
        }
        best.map(|(p, local)| {
            if p.is_empty() {
                format!(":{}", local)
            } else {
                format!("{}:{}", p, local)
            }
        })
    }

    fn prefixes_used_for_output(&self, triples: &[Triple]) -> Vec<(String, String)> {
        let mut used = HashSet::new();
        for t in triples {
            // Collect IRIs from subject + object always.
            // Collect IRIs from predicate only if it won't be printed as `a`.
            let mut iris = Vec::new();
            iris.extend(collect_iris_in_term(&t.s));
            if !is_rdf_type_pred(&t.p) {
                iris.extend(collect_iris_in_term(&t.p));
            }
            iris.extend(collect_iris_in_term(&t.o));

            for iri in iris {
                for (p, base) in &self.map {
                    if base.is_empty() {
                        continue;
                    }
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

fn collect_iris_in_term(t: &Term) -> Vec<String> {
    let mut out = Vec::new();
    match t {
        Term::Iri(i) => out.push(i.clone()),
        Term::List(vs) => {
            for x in vs {
                out.extend(collect_iris_in_term(x));
            }
        }
        Term::OpenList(vs, _) => {
            for x in vs {
                out.extend(collect_iris_in_term(x));
            }
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

    fn peek(&self) -> &TokenKind {
        &self.toks[self.pos].kind
    }

    fn next(&mut self) -> TokenKind {
        let k = self.toks[self.pos].kind.clone();
        self.pos += 1;
        k
    }

    fn expect_dot(&mut self) {
        match self.next() {
            TokenKind::Dot => {}
            other => panic!("Expected '.', got {:?}", other),
        }
    }

    fn parse_document(
        &mut self,
    ) -> (PrefixEnv, Vec<Triple>, Vec<Rule>, Vec<Rule>) {
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
                    // statement: term (=>|<= term)? OR triples
                    let first = self.parse_term();
                    match self.peek() {
                        TokenKind::OpImplies => {
                            self.next();
                            let second = self.parse_term();
                            self.expect_dot();
                            let r = self.make_rule(first, second, true);
                            forward_rules.push(r);
                        }
                        TokenKind::OpImpliedBy => {
                            self.next();
                            let second = self.parse_term();
                            self.expect_dot();
                            let r = self.make_rule(first, second, false);
                            backward_rules.push(r);
                        }
                        _ => {
                            // triples with ; and ,
                            let mut more = self.parse_predicate_object_list(first);
                            self.expect_dot();

                            // normalize explicit log:implies / log:impliedBy at top-level
                            for tr in more.drain(..) {
                                if is_log_implies(&tr.p)
                                    && matches!(tr.s, Term::Formula(_))
                                    && matches!(tr.o, Term::Formula(_))
                                {
                                    let r = self.make_rule(tr.s.clone(), tr.o.clone(), true);
                                    forward_rules.push(r);
                                } else if is_log_implied_by(&tr.p)
                                    && matches!(tr.s, Term::Formula(_))
                                    && matches!(tr.o, Term::Formula(_))
                                {
                                    let r = self.make_rule(tr.s.clone(), tr.o.clone(), false);
                                    backward_rules.push(r);
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

    fn parse_prefix_directive(&mut self) {
        // @prefix p: <...> .
        // OR @prefix p: .
        let pref = match self.next() {
            TokenKind::Ident(s) => s,
            other => panic!("Expected prefix name, got {:?}", other),
        };

        let pref_name = if pref.ends_with(':') {
            pref[..pref.len() - 1].to_string()
        } else {
            pref
        };

        // allow optional ':' token already included, so tolerate if next is Ident(":") etc
        // Now parse iri or empty before '.'
        match self.peek() {
            TokenKind::Dot => {
                self.next(); // consume dot
                // empty IRI => keep default if known else empty
                if !self.prefixes.map.contains_key(&pref_name) {
                    self.prefixes.set(&pref_name, "");
                }
                return;
            }
            _ => {}
        }

        let iri = match self.next() {
            TokenKind::IriRef(s) => s,
            TokenKind::Ident(s) => {
                // tolerate bareword IRI
                self.prefixes.expand_qname(&s)
            }
            other => panic!("Expected IRI after @prefix, got {:?}", other),
        };

        self.expect_dot();
        self.prefixes.set(&pref_name, &iri);
    }

    fn parse_base_directive(&mut self) {
        // @base <...> .
        let iri = match self.next() {
            TokenKind::IriRef(s) => s,
            TokenKind::Ident(s) => s,
            other => panic!("Expected IRI after @base, got {:?}", other),
        };
        self.expect_dot();
        self.prefixes.set("", &iri);
    }

    fn parse_term(&mut self) -> Term {
        match self.next() {
            TokenKind::IriRef(iri) => Term::Iri(iri),
            TokenKind::Ident(s) => {
                if s == "a" {
                    Term::Iri(format!("{}type", RDF_NS))
                } else if s.contains(':') {
                    Term::Iri(self.prefixes.expand_qname(&s))
                } else {
                    // bareword treated as IRI-ish
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

    fn parse_list(&mut self) -> Term {
        let mut elems = vec![];
        while *self.peek() != TokenKind::RParen {
            let t = self.parse_term();
            elems.push(t);
        }
        self.next(); // RParen
        Term::List(elems)
    }

    fn parse_blank(&mut self) -> Term {
        // support [] only (ignore property lists for now)
        if *self.peek() == TokenKind::RBracket {
            self.next();
            self.blank_counter += 1;
            return Term::Blank(format!("_:b{}", self.blank_counter));
        }

        // property list: read and discard until ']'
        while *self.peek() != TokenKind::RBracket {
            self.next();
        }
        self.next(); // RBracket
        self.blank_counter += 1;
        Term::Blank(format!("_:b{}", self.blank_counter))
    }

    fn parse_formula(&mut self) -> Term {
        let mut triples = vec![];

        while *self.peek() != TokenKind::RBrace {
            let first = self.parse_term();

            match self.peek() {
                TokenKind::OpImplies | TokenKind::OpImpliedBy => {
                    // nested rules ignored in this tiny subset
                    // consume op, rhs, dot
                    self.next();
                    self.parse_term();

                    // In N3, the last '.' inside {...} may be omitted.
                    match self.peek() {
                        TokenKind::Dot => {
                            self.next();
                        }
                        TokenKind::RBrace => { /* ok, implicit end */ }
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                }
                _ => {
                    let mut inner = self.parse_predicate_object_list(first);

                    // In N3, the last '.' inside {...} may be omitted.
                    match self.peek() {
                        TokenKind::Dot => {
                            self.next();
                        }
                        TokenKind::RBrace => { /* ok, implicit end */ }
                        other => panic!("Expected '.' or '}}', got {:?}", other),
                    }
                    triples.append(&mut inner);
                }
            }
        }

        self.next(); // RBrace
        Term::Formula(triples)
    }

    fn parse_predicate_object_list(&mut self, subject: Term) -> Vec<Triple> {
        let mut out = vec![];

        loop {
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

            match self.peek() {
                TokenKind::Semicolon => {
                    self.next();
                    if *self.peek() == TokenKind::Dot {
                        break;
                    }
                    continue;
                }
                _ => break,
            }
        }

        out
    }

    fn parse_object_list(&mut self) -> Vec<Term> {
        let mut objs = vec![self.parse_term()];
        while *self.peek() == TokenKind::Comma {
            self.next();
            objs.push(self.parse_term());
        }
        objs
    }

    fn make_rule(&self, left: Term, right: Term, is_forward: bool) -> Rule {
        let (premise_term, concl_term) = if is_forward {
            (left, right)
        } else {
            (right, left)
        };

        let premise = match premise_term {
            Term::Formula(ts) => ts,
            Term::Literal(lit) if lit == "true" => vec![],
            _ => vec![], // treat non-formula as empty in subset
        };

        let conclusion = match concl_term {
            Term::Formula(ts) => ts,
            _ => vec![],
        };

        Rule {
            premise,
            conclusion,
            is_forward,
        }
    }
}

fn is_rdf_type_pred(p: &Term) -> bool {
    let iri = format!("{}type", RDF_NS);
    matches!(p, Term::Iri(i) if i == &iri)
}

fn is_log_implies(p: &Term) -> bool {
    matches!(p, Term::Iri(i) if i.as_str() == format!("{}implies", LOG_NS))
}

fn is_log_implied_by(p: &Term) -> bool {
    matches!(p, Term::Iri(i) if i.as_str() == format!("{}impliedBy", LOG_NS))
}

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

fn apply_subst_term(t: &Term, s: &Subst) -> Term {
    match t {
        Term::Var(v) => {
            // Chase var -> var -> ... chains
            let mut cur = Term::Var(v.clone());
            let mut seen: HashSet<String> = HashSet::new();
            loop {
                match &cur {
                    Term::Var(name) => {
                        // break cycles like ?X -> ?Y, ?Y -> ?X
                        if !seen.insert(name.clone()) {
                            break;
                        }
                        if let Some(next) = s.get(name) {
                            cur = next.clone();
                            continue;
                        }
                    }
                    _ => {}
                }
                break;
            }
            // After chasing, still substitute inside composite terms
            match cur {
                Term::Var(name) => Term::Var(name),
                other => apply_subst_term(&other, s),
            }
        }
        Term::List(xs) => Term::List(xs.iter().map(|e| apply_subst_term(e, s)).collect()),
        Term::OpenList(prefix, tailv) => {
            let new_prefix: Vec<Term> =
                prefix.iter().map(|e| apply_subst_term(e, s)).collect();

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

fn unify_open_with_list(
    prefix: &[Term],
    tailv: &str,
    ys: &[Term],
    subst: &Subst,
) -> Option<Subst> {
    if ys.len() < prefix.len() {
        return None;
    }
    let mut s2 = subst.clone();
    for (x, y) in prefix.iter().zip(ys.iter()) {
        s2 = unify_term(x, y, &s2)?;
    }
    let rest = Term::List(ys[prefix.len()..].to_vec());
    s2 = unify_term(&Term::Var(tailv.to_string()), &rest, &s2)?;
    Some(s2)
}

fn unify_term(a: &Term, b: &Term, subst: &Subst) -> Option<Subst> {
    let a = apply_subst_term(a, subst);
    let b = apply_subst_term(b, subst);

    match (a, b) {
        (Term::Var(v), t) | (t, Term::Var(v)) => {
            // If it's the same variable, it's already unified.
            if let Term::Var(v2) = &t {
                if v2 == &v {
                    return Some(subst.clone());
                }
            }
            // occurs check (light)
            if contains_var_term(&t, &v) {
                return None;
            }
            let mut s2 = subst.clone();
            s2.insert(v, t);
            Some(s2)
        }
        (Term::Iri(x), Term::Iri(y)) if x == y => Some(subst.clone()),
        (Term::Literal(x), Term::Literal(y)) if x == y => Some(subst.clone()),
        (Term::Blank(x), Term::Blank(y)) if x == y => Some(subst.clone()),
        // Open list unification (like [H|T])
        (Term::OpenList(pref, tailv), Term::List(ys)) => {
            unify_open_with_list(&pref, &tailv, &ys, subst)
        }
        (Term::List(xs), Term::OpenList(pref, tailv)) => {
            unify_open_with_list(&pref, &tailv, &xs, subst)
        }
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
        (Term::List(xs), Term::List(ys)) => {
            if xs.len() != ys.len() {
                return None;
            }
            let mut s2 = subst.clone();
            for (x, y) in xs.iter().zip(ys.iter()) {
                if let Some(s3) = unify_term(x, y, &s2) {
                    s2 = s3;
                } else {
                    return None;
                }
            }
            Some(s2)
        }
        // formulas: structural equality only in this subset
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

// -------- Builtins --------

fn parse_num(t: &Term) -> Option<f64> {
    match t {
        Term::Literal(s) => s.parse::<f64>().ok(),
        _ => None,
    }
}

fn format_num(n: f64) -> String {
    if n.fract() == 0.0 {
        format!("{}", n as i64)
    } else {
        format!("{}", n)
    }
}

fn is_builtin_pred(p: &Term) -> bool {
    matches!(p, Term::Iri(i)
        if i.starts_with(MATH_NS)
        || i.starts_with(LOG_NS)
        || i.starts_with(STRING_NS)
        || i.starts_with(TIME_NS)
        || i.starts_with(LIST_NS))
}

// ----- typed literal / date / duration helpers -----

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

fn parse_iso8601_duration_to_seconds(s: &str) -> Option<f64> {
    let mut it = s.chars().peekable();
    if it.next()? != 'P' {
        return None;
    }

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
        if c == 'T' {
            in_time = true;
            continue;
        }
        if c.is_ascii_digit() || c == '.' {
            num.push(c);
            continue;
        }

        if num.is_empty() {
            return None;
        }
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

    // Approximate conversions for comparisons.
    let total_days = years * 365.2425
        + months * 30.436875
        + weeks * 7.0
        + days
        + hours / 24.0
        + minutes / (24.0 * 60.0)
        + seconds / (24.0 * 3600.0);

    Some(total_days * 86400.0)
}

fn parse_num_or_duration(t: &Term) -> Option<f64> {
    if let Some(n) = parse_num(t) {
        return Some(n);
    }

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
    let lex = if neg {
        format!("\"-P{}D\"", days)
    } else {
        format!("\"P{}D\"", days)
    };
    Term::Literal(format!("{}^^<{}duration>", lex, XSD_NS))
}

// Evaluate builtin triple under current subst, returning possible new substitutions.
fn eval_builtin(goal: &Triple, subst: &Subst) -> Vec<Subst> {
    let g = apply_subst_triple(goal, subst);

    match &g.p {
        // list:append
        // Subject must be a list of lists: (L1 L2 ... Ln) list:append L
        // Object L is the concatenation of all Li.  Requires all Li to be bound lists.
        Term::Iri(p) if p == &format!("{}append", LIST_NS) => {
            // Subject must be a list
            let parts = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };

            // Each part must itself be a fully bound list
            let mut out_elems: Vec<Term> = Vec::new();
            for part in parts {
                match part {
                    Term::List(es) => {
                        // Spec requires all constituent members bound
                        if !es.iter().all(is_ground_term) {
                            return vec![];
                        }
                        out_elems.extend(es.clone());
                    }
                    _ => {
                        // If any element isn't a list, fail (no guessing)
                        return vec![];
                    }
                }
            }

            let result = Term::List(out_elems);

            match &g.o {
                // bind result
                Term::Var(v) => {
                    let mut s2 = subst.clone();
                    s2.insert(v.clone(), result);
                    vec![s2]
                }
                // verify equality
                Term::List(_) => {
                    if g.o == result {
                        vec![subst.clone()]
                    } else {
                        vec![]
                    }
                }
                _ => vec![],
            }
        }

        // list:firstRest  (experimental, bidirectional, supports open tail)
        //
        // Forward:
        //   (a b c ...) list:firstRest (?F ?R)
        //   => ?F = a, ?R = (b c ...)
        //
        // Inverse:
        //   ?L list:firstRest (?F ?R)
        //   => ?L = open list with head ?F and tail ?R
        Term::Iri(p) if p == &format!("{}firstRest", LIST_NS) => {
            // --- Forward: split a concrete non-empty list ---
            if let Term::List(xs) = &g.s {
                if xs.is_empty() {
                    return vec![];
                }
                let first = xs[0].clone();
                let rest = Term::List(xs[1..].to_vec());
                let pair = Term::List(vec![first, rest]);

                return unify_term(&g.o, &pair, subst).into_iter().collect();
            }

            // --- Inverse: build list from (first rest) ---
            if let Term::List(pair) = &g.o {
                if pair.len() != 2 {
                    return vec![];
                }
                let first = &pair[0];
                let rest = &pair[1];

                match rest {
                    // rest is concrete list => construct full concrete list
                    Term::List(rs) => {
                        let mut xs = Vec::with_capacity(1 + rs.len());
                        xs.push(first.clone());
                        xs.extend(rs.clone());
                        let constructed = Term::List(xs);
                        return unify_term(&g.s, &constructed, subst).into_iter().collect();
                    }

                    // rest is a variable => construct OPEN list [first | rest]
                    Term::Var(rv) => {
                        let constructed = Term::OpenList(vec![first.clone()], rv.clone());
                        return unify_term(&g.s, &constructed, subst).into_iter().collect();
                    }

                    // rest is already open => extend its prefix
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

        // ----------------
        // list:member
        // ----------------
        // CWM/EYE semantics:
        //   Subject is a list, object is an element of that list. :contentReference[oaicite:2]{index=2}
        // Bidirectional in the useful direction:
        //   - if subject is a ground list and object is var => enumerate members
        //   - if subject is a ground list and object is ground => membership test
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

        // --------------
        // list:in
        // --------------
        // Dual of member:
        //   Subject is an element, object is a list, and subject is in object. :contentReference[oaicite:3]{index=3}
        // Useful direction:
        //   - if object is ground list:
        //       * subject var => enumerate
        //       * subject ground => test
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

        // -----------------
        // list:length
        // -----------------
        // EYE builtin name; same intent as math:memberCount. :contentReference[oaicite:4]{index=4}
        //   L list:length N  iff N is the number of members in L.
        // Only computes/checks when L is a ground list.
        Term::Iri(p) if p == &format!("{}length", LIST_NS) => {
            let xs = match &g.s {
                Term::List(xs) => xs,
                _ => return vec![],
            };

            // length is always an integer literal in eyelite
            let n = xs.len() as i64;
            let n_term = Term::Literal(n.to_string());

            match &g.o {
                Term::Var(_) | Term::Literal(_) => {
                    if let Some(s2) = unify_term(&g.o, &n_term, subst) {
                        vec![s2]
                    } else {
                        vec![]
                    }
                }
                _ => vec![],
            }
        }

        // -------------
        // list:map
        // -------------
        // Pragmatic eyelite-only version:
        //
        //   (InputList Predicate) list:map OutputList.
        //
        // Where Predicate MUST be a builtin predicate (math:/string:/list:/time:/log:).
        // Each element e in InputList is mapped by evaluating:
        //   e Predicate ?y
        // OutputList is the list of all y's.
        //
        // Limitations:
        // - only unary builtin predicates via binary form (e P ?y)
        // - InputList must be ground to run forward
        // - no inverse generation
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

            if !is_builtin_pred(&pred) {
                // eyelite can't map non-builtin predicates yet
                return vec![];
            }

            // Ensure input is ground; map doesn't invent list content
            if !input.iter().all(is_ground_term) {
                return vec![];
            }

            let mut results: Vec<Term> = Vec::with_capacity(input.len());
            let mut cur_substs: Vec<Subst> = vec![subst.clone()];

            for el in input {
                let mut next_substs = Vec::new();

                for s_in in cur_substs {
                    let yvar = Term::Var("_mapY".to_string());
                    let goal = Triple {
                        s: el.clone(),
                        p: pred.clone(),
                        o: yvar.clone(),
                    };

                    let sols = eval_builtin(&goal, &s_in);
                    for s_out in sols {
                        let yval = apply_subst_term(&yvar, &s_out);
                        // if yval still a var, skip (builtin didn't bind)
                        if matches!(yval, Term::Var(_)) {
                            continue;
                        }
                        let s_keep = s_out.clone();
                        // stash value by pushing to results only once per solution track
                        next_substs.push((s_keep, yval));
                    }
                }

                // If builtin is deterministic, we will have exactly one per track.
                if next_substs.is_empty() {
                    return vec![];
                }

                // Flatten solution tracks:
                cur_substs = Vec::new();
                let mut new_results_per_track: Vec<Vec<Term>> = Vec::new();
                for (s_next, yval) in next_substs {
                    cur_substs.push(s_next);
                    new_results_per_track.push(vec![yval]);
                }

                // We only support deterministic builtins per element:
                // take first track if multiple
                results.push(new_results_per_track[0][0].clone());
            }

            let out_list = Term::List(results);
            if let Some(s2) = unify_term(&g.o, &out_list, subst) {
                vec![s2]
            } else {
                vec![]
            }
        }

        // time:localTime
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
                    if strip_quotes(&lex_o) == now {
                        vec![subst.clone()]
                    } else {
                        vec![]
                    }
                }
                _ => vec![],
            }
        }

        // -------- numeric/duration comparisons --------

        Term::Iri(p) if p == &format!("{}greaterThan", MATH_NS) => {
            // Binary form: 5 math:greaterThan 3.
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o))
            {
                return if a > b { vec![subst.clone()] } else { vec![] };
            }
            // List form: (5 3) math:greaterThan true.
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a > b {
                            return vec![subst.clone()];
                        }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}lessThan", MATH_NS) => {
            // Binary form: 3 math:lessThan 5.
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o))
            {
                return if a < b { vec![subst.clone()] } else { vec![] };
            }
            // List form: (3 5) math:lessThan true.
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a < b {
                            return vec![subst.clone()];
                        }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}notLessThan", MATH_NS) => {
            // Binary: X notLessThan Y meaning X >= Y
            if let (Some(a), Some(b)) = (parse_num_or_duration(&g.s), parse_num_or_duration(&g.o))
            {
                return if a >= b { vec![subst.clone()] } else { vec![] };
            }
            // List form: (X Y) notLessThan true
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) =
                        (parse_num_or_duration(&xs[0]), parse_num_or_duration(&xs[1]))
                    {
                        if a >= b {
                            return vec![subst.clone()];
                        }
                    }
                }
            }
            vec![]
        }

        // -------- numeric math --------

        Term::Iri(p) if p == &format!("{}sum", MATH_NS) => {
            // Variadic list form: (a b c ...) math:sum ?z meaning z = a + b + c + ...
            if let Term::List(xs) = &g.s {
                if xs.len() >= 2 && xs.iter().all(|t| parse_num(t).is_some()) {
                    let total: f64 = xs.iter().map(|t| parse_num(t).unwrap()).sum();
                    match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(total)));
                            return vec![s2];
                        }
                        Term::Literal(o) => {
                            if o == &format_num(total) {
                                return vec![subst.clone()];
                            }
                        }
                        _ => {}
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}product", MATH_NS) => {
            // Variadic list form: (a b c ...) math:product ?z meaning z = a*b*c*...
            if let Term::List(xs) = &g.s {
                if xs.len() >= 2 && xs.iter().all(|t| parse_num(t).is_some()) {
                    let prod: f64 = xs.iter().map(|t| parse_num(t).unwrap()).product();
                    match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(prod)));
                            return vec![s2];
                        }
                        Term::Literal(o) => {
                            if o == &format_num(prod) {
                                return vec![subst.clone()];
                            }
                        }
                        _ => {}
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}difference", MATH_NS) => {
            // List form only: (?A ?B) math:difference ?C meaning C = A - B
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    // numeric diff
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        let c = a - b;
                        match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                return vec![s2];
                            }
                            Term::Literal(o) => {
                                if o == &format_num(c) {
                                    return vec![subst.clone()];
                                }
                            }
                            _ => {}
                        }
                    }

                    // date/dateTime diff => xsd:duration
                    if let (Some(a_dt), Some(b_dt)) =
                        (parse_datetime_like(&xs[0]), parse_datetime_like(&xs[1]))
                    {
                        let diff = a_dt - b_dt;
                        let secs = diff.num_seconds() as f64;
                        let dur_term = format_duration_literal_from_seconds(secs);

                        match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), dur_term);
                                return vec![s2];
                            }
                            Term::Literal(o) => {
                                if Term::Literal(o.clone()) == dur_term {
                                    return vec![subst.clone()];
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}quotient", MATH_NS) => {
            // List form: (?A ?B) math:quotient ?C meaning C = A / B
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        if b == 0.0 {
                            return vec![];
                        }
                        let c = a / b;
                        match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                return vec![s2];
                            }
                            Term::Literal(o) => {
                                if o == &format_num(c) {
                                    return vec![subst.clone()];
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}exponentiation", MATH_NS) => {
            // List form: (?A ?B) math:exponentiation ?C meaning C = A ^ B
            if let Term::List(xs) = &g.s {
                if xs.len() == 2 {
                    // Forward direction: A,B known -> C
                    if let (Some(a), Some(b)) = (parse_num(&xs[0]), parse_num(&xs[1])) {
                        let c = a.powf(b);
                        match &g.o {
                            Term::Var(v) => {
                                let mut s2 = subst.clone();
                                s2.insert(v.clone(), Term::Literal(format_num(c)));
                                return vec![s2];
                            }
                            Term::Literal(o) => {
                                if o == &format_num(c) {
                                    return vec![subst.clone()];
                                }
                            }
                            _ => {}
                        }
                    }

                    // Inverse direction (solve exponent):
                    // (A ?B) exponentiation C => ?B = ln(C)/ln(A)
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
                    // (optional) solve base not implemented
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}negation", MATH_NS) => {
            // Unary: ?X math:negation ?Y meaning Y = -X
            if let (Some(a), Term::Var(v)) = (parse_num(&g.s), &g.o) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(-a)));
                return vec![s2];
            }
            // Inverse: ?X math:negation 3 => X = -3
            if let (Term::Var(v), Some(b)) = (&g.s, parse_num(&g.o)) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(-b)));
                return vec![s2];
            }
            // Ground check
            if let (Some(a), Some(b)) = (parse_num(&g.s), parse_num(&g.o)) {
                if (-a - b).abs() < 1e-9 {
                    return vec![subst.clone()];
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}absoluteValue", MATH_NS) => {
            // Unary abs: ?X math:absoluteValue ?Y
            if let (Some(a), Term::Var(v)) = (parse_num(&g.s), &g.o) {
                let mut s2 = subst.clone();
                s2.insert(v.clone(), Term::Literal(format_num(a.abs())));
                return vec![s2];
            }
            if let (Some(a), Some(b)) = (parse_num(&g.s), parse_num(&g.o)) {
                if (a.abs() - b).abs() < 1e-9 {
                    return vec![subst.clone()];
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}cos", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.cos();
                match &g.o {
                    Term::Var(v) => {
                        let mut s2 = subst.clone();
                        s2.insert(v.clone(), Term::Literal(format_num(c)));
                        return vec![s2];
                    }
                    Term::Literal(o) => {
                        if o == &format_num(c) {
                            return vec![subst.clone()];
                        }
                    }
                    _ => {}
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}sin", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.sin();
                match &g.o {
                    Term::Var(v) => {
                        let mut s2 = subst.clone();
                        s2.insert(v.clone(), Term::Literal(format_num(c)));
                        return vec![s2];
                    }
                    Term::Literal(o) => {
                        if o == &format_num(c) {
                            return vec![subst.clone()];
                        }
                    }
                    _ => {}
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}acos", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.acos();
                if c.is_finite() {
                    match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(c)));
                            return vec![s2];
                        }
                        Term::Literal(o) => {
                            if o == &format_num(c) {
                                return vec![subst.clone()];
                            }
                        }
                        _ => {}
                    }
                }
            }
            vec![]
        }

        Term::Iri(p) if p == &format!("{}asin", MATH_NS) => {
            if let Some(a) = parse_num(&g.s) {
                let c = a.asin();
                if c.is_finite() {
                    match &g.o {
                        Term::Var(v) => {
                            let mut s2 = subst.clone();
                            s2.insert(v.clone(), Term::Literal(format_num(c)));
                            return vec![s2];
                        }
                        Term::Literal(o) => {
                            if o == &format_num(c) {
                                return vec![subst.clone()];
                            }
                        }
                        _ => {}
                    }
                }
            }
            vec![]
        }

        // -------- log builtins --------

        Term::Iri(p) if p == &format!("{}equalTo", LOG_NS) => {
            if g.s == g.o {
                vec![subst.clone()]
            } else {
                vec![]
            }
        }

        Term::Iri(p) if p == &format!("{}notEqualTo", LOG_NS) => {
            if g.s != g.o {
                vec![subst.clone()]
            } else {
                vec![]
            }
        }

        _ => vec![],
    }
}

// -------- Backward proof & forward chaining --------

fn standardize_rule(rule: &Rule, gen: &mut usize) -> Rule {
    fn rename_term(
        t: &Term,
        vmap: &mut HashMap<String, String>,
        gen: &mut usize,
    ) -> Term {
        match t {
            Term::Var(v) => {
                let nv = vmap
                    .entry(v.clone())
                    .or_insert_with(|| {
                        let name = format!("{}__{}", v, *gen);
                        *gen += 1;
                        name
                    })
                    .clone();
                Term::Var(nv)
            }
            Term::List(xs) => Term::List(xs.iter().map(|e| rename_term(e, vmap, gen)).collect()),
            Term::OpenList(xs, tailv) => {
                let new_xs: Vec<Term> =
                    xs.iter().map(|e| rename_term(e, vmap, gen)).collect();
                let new_tail = vmap
                    .entry(tailv.clone())
                    .or_insert_with(|| {
                        let name = format!("{}__{}", tailv, *gen);
                        *gen += 1;
                        name
                    })
                    .clone();
                Term::OpenList(new_xs, new_tail)
            }
            Term::Formula(ts) => Term::Formula(
                ts.iter()
                    .map(|tr| Triple {
                        s: rename_term(&tr.s, vmap, gen),
                        p: rename_term(&tr.p, vmap, gen),
                        o: rename_term(&tr.o, vmap, gen),
                    })
                    .collect(),
            ),
            _ => t.clone(),
        }
    }

    let mut vmap2 = HashMap::new();
    let premise = rule
        .premise
        .iter()
        .map(|tr| Triple {
            s: rename_term(&tr.s, &mut vmap2, gen),
            p: rename_term(&tr.p, &mut vmap2, gen),
            o: rename_term(&tr.o, &mut vmap2, gen),
        })
        .collect();

    let conclusion = rule
        .conclusion
        .iter()
        .map(|tr| Triple {
            s: rename_term(&tr.s, &mut vmap2, gen),
            p: rename_term(&tr.p, &mut vmap2, gen),
            o: rename_term(&tr.o, &mut vmap2, gen),
        })
        .collect();

    Rule {
        premise,
        conclusion,
        is_forward: rule.is_forward,
    }
}

// Prove a conjunction of goals using facts + backward rules (+ builtins).
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

    // Builtin?
    if is_builtin_pred(&goal0.p) {
        let subs = eval_builtin(&goal0, subst);
        let mut out = vec![];
        for s2 in subs {
            out.extend(prove_goals(
                rest, &s2, facts, back_rules, depth + 1, visited, var_gen,
            ));
        }
        return out;
    }

    if visited.contains(&goal0) {
        return vec![];
    }
    visited.push(goal0.clone());

    let mut results = vec![];

    // Match existing facts
    for f in facts {
        if let Some(s2) = unify_triple(&goal0, f, subst) {
            results.extend(prove_goals(
                rest, &s2, facts, back_rules, depth + 1, visited, var_gen,
            ));
        }
    }

    // Use backward rules (Horn-style: 1 head triple)
    for r in back_rules {
        if r.conclusion.len() != 1 {
            continue;
        }
        // fresh variables for this rule application
        let r_std = standardize_rule(r, var_gen);
        let head = &r_std.conclusion[0];

        if let Some(s2) = unify_triple(head, &goal0, subst) {
            let mut body: Vec<Triple> = vec![];
            for b in &r_std.premise {
                body.push(apply_subst_triple(b, &s2));
            }
            let body_solutions =
                prove_goals(&body, &s2, facts, back_rules, depth + 1, visited, var_gen);

            for sb in body_solutions {
                results.extend(prove_goals(
                    rest, &sb, facts, back_rules, depth + 1, visited, var_gen,
                ));
            }
        }
    }

    visited.pop();
    results
}

fn forward_chain(mut facts: Vec<Triple>, forward_rules: &[Rule], back_rules: &[Rule]) -> Vec<Triple> {
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
                    if !is_ground_triple(&inst) {
                        continue; // skip unbound
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

// -------- Pretty printing --------

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
    let p = if is_rdf_type_pred(&tr.p) {
        "a".to_string()
    } else {
        term_to_n3(&tr.p, prefixes)
    };
    let o = term_to_n3(&tr.o, prefixes);
    format!("{} {} {} .", s, p, o)
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: eyelite <file.n3>");
        std::process::exit(1);
    }

    let text = fs::read_to_string(&args[1]).expect("read file");
    let toks = lex(&text);
    let mut p = Parser::new(toks);
    let (prefixes, triples, frules, brules) = p.parse_document();

    // keep only ground input facts
    let facts: Vec<Triple> = triples.into_iter().filter(is_ground_triple).collect();

    let derived = forward_chain(facts, &frules, &brules);

    // Print prefixes needed for derived output
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

    // Print derived triples
    for t in derived {
        println!("{}", triple_to_n3(&t, &prefixes));
    }
}

