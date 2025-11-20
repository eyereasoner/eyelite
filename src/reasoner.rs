use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::resolve::RDF_TYPE;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    Iri(String),
    Blank(String),
    Literal(String), // <- was Literal(Literal)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GTriple {
    pub s: Atom,
    pub p: Atom,
    pub o: Atom,
}

#[derive(Debug, Clone)]
enum PT {
    Var(String),
    Const(Atom),
}

#[derive(Debug, Clone)]
pub struct RulePat {
    premise: Vec<(PT, PT, PT)>,
    conclusion: Vec<(PT, PT, PT)>,
}

/// Extract ground triples + simple Horn-like rules from a resolved Document.
pub fn extract(doc: &Document) -> (HashSet<GTriple>, Vec<RulePat>) {
    let mut facts = HashSet::new();
    let mut rules = vec![];

    for st in &doc.statements {
        match st {
            Statement::Triple(tr) => {
                if let Some(gt) = to_ground(tr) {
                    facts.insert(gt);
                }
            }
            Statement::Implication { premise, conclusion, direction } => {
                // Only forward rules (=>) for this toy chainer
                if *direction != ImplicationDir::Forward { continue; }

                let prem = formula_to_patterns(premise);
                let concl = formula_to_patterns(conclusion);

                if !prem.is_empty() && !concl.is_empty() {
                    rules.push(RulePat { premise: prem, conclusion: concl });
                }
            }
        }
    }

    (facts, rules)
}

fn to_ground(tr: &Triple) -> Option<GTriple> {
    let s = term_to_atom(&tr.subject)?;
    let o = term_to_atom(&tr.object)?;

    let p = match &tr.predicate {
        Predicate::KeywordA => Atom::Iri(RDF_TYPE.into()),
        Predicate::Normal(t) => term_to_atom(t)?,
        Predicate::Inverse(t) => term_to_atom(t)?, // ignore inverse semantics here
        Predicate::Has(t) => term_to_atom(t)?,
        _ => return None,
    };

    Some(GTriple { s, p, o })
}

fn term_to_atom(t: &Term) -> Option<Atom> {
    match t {
        Term::Iri(i) => Some(Atom::Iri(i.clone())),
        Term::BlankNode(b) => Some(Atom::Blank(b.clone())),
        Term::Literal(l) => Some(Atom::Literal(canon_lit(l))),
        _ => None,
    }
}

fn term_to_pt(t: &Term) -> Option<PT> {
    match t {
        Term::Variable(v) => Some(PT::Var(v.clone())),
        Term::Iri(i) => Some(PT::Const(Atom::Iri(i.clone()))),
        Term::BlankNode(b) => Some(PT::Const(Atom::Blank(b.clone()))),
        Term::Literal(l) => Some(PT::Const(Atom::Literal(canon_lit(l)))),
        _ => None,
    }
}

fn pred_to_pt(p: &Predicate) -> Option<PT> {
    match p {
        Predicate::KeywordA => Some(PT::Const(Atom::Iri(RDF_TYPE.into()))),
        Predicate::Normal(t) => term_to_pt(t),
        _ => None,
    }
}

fn formula_to_patterns(f: &Formula) -> Vec<(PT, PT, PT)> {
    let mut out = vec![];
    for st in &f.statements {
        if let Statement::Triple(tr) = st {
            let s = term_to_pt(&tr.subject);
            let p = pred_to_pt(&tr.predicate);
            let o = term_to_pt(&tr.object);
            if let (Some(s), Some(p), Some(o)) = (s, p, o) {
                out.push((s, p, o));
            }
        }
    }
    out
}

/// Naive forward chaining to saturation.
pub fn forward_chain(mut facts: HashSet<GTriple>, rules: &[RulePat]) -> HashSet<GTriple> {
    loop {
        let mut added_any = false;

        for rule in rules {
            let bindings = match_premise(&rule.premise, &facts);
            for b in bindings {
                for (ps, pp, po) in &rule.conclusion {
                    if let Some(gt) = instantiate(ps, pp, po, &b) {
                        if facts.insert(gt) {
                            added_any = true;
                        }
                    }
                }
            }
        }

        if !added_any {
            break;
        }
    }

    facts
}

fn match_premise(
    pats: &[(PT, PT, PT)],
    facts: &HashSet<GTriple>,
) -> Vec<HashMap<String, Atom>> {
    let mut envs: Vec<HashMap<String, Atom>> = vec![HashMap::new()];

    for (ps, pp, po) in pats {
        let mut next_envs = vec![];
        for env in &envs {
            for f in facts {
                if let Some(e2) = unify(ps, pp, po, f, env) {
                    next_envs.push(e2);
                }
            }
        }
        envs = next_envs;
        if envs.is_empty() {
            break;
        }
    }

    envs
}

fn unify(
    ps: &PT, pp: &PT, po: &PT,
    f: &GTriple,
    env: &HashMap<String, Atom>,
) -> Option<HashMap<String, Atom>> {
    let mut e = env.clone();
    unify_term(ps, &f.s, &mut e)?;
    unify_term(pp, &f.p, &mut e)?;
    unify_term(po, &f.o, &mut e)?;
    Some(e)
}

fn unify_term(pt: &PT, atom: &Atom, env: &mut HashMap<String, Atom>) -> Option<()> {
    match pt {
        PT::Const(c) => if c == atom { Some(()) } else { None },
        PT::Var(v) => {
            if let Some(bound) = env.get(v) {
                if bound == atom { Some(()) } else { None }
            } else {
                env.insert(v.clone(), atom.clone());
                Some(())
            }
        }
    }
}

fn instantiate(
    ps: &PT, pp: &PT, po: &PT,
    env: &HashMap<String, Atom>
) -> Option<GTriple> {
    Some(GTriple {
        s: inst_term(ps, env)?,
        p: inst_term(pp, env)?,
        o: inst_term(po, env)?,
    })
}

fn inst_term(pt: &PT, env: &HashMap<String, Atom>) -> Option<Atom> {
    match pt {
        PT::Const(c) => Some(c.clone()),
        PT::Var(v) => env.get(v).cloned(),
    }
}

fn canon_lit(l: &Literal) -> String {
    // Good enough for a toy reasoner; makes literals hashable.
    match l {
        Literal::RdfString { lex, lang, datatype } => {
            let mut s = format!("\"{lex}\"");
            if let Some(lg) = lang {
                s.push('@');
                s.push_str(lg);
            }
            if let Some(dt) = datatype {
                s.push_str("^^");
                s.push_str(&format!("{dt:?}"));
            }
            s
        }
        Literal::Integer(x) => x.clone(),
        Literal::Decimal(x) => x.clone(),
        Literal::Double(x) => x.clone(),
        Literal::Boolean(b) => b.to_string(),
    }
}

