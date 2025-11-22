use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::resolve::RDF_TYPE;

/// Ground atom for reasoning.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    Iri(String),
    Blank(String),
    Literal(String),
    List(Vec<Atom>),
}

/// Ground triple used in fact sets.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GTriple {
    pub s: Atom,
    pub p: Atom,
    pub o: Atom,
}

/// Pattern term used in rules/goals.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PT {
    Var(String),
    Const(Atom),
    List(Vec<PT>),
}

/// Rule pattern: conjunction of triple patterns => conjunction of triple patterns.
#[derive(Debug, Clone)]
pub struct RulePat {
    pub premise: Vec<(PT, PT, PT)>,
    pub conclusion: Vec<(PT, PT, PT)>,
}

/// Extract ground facts and rules from a document.
/// (Direction is preserved on the Statement for the CLI to split rules.)
pub fn extract(doc: &Document) -> (HashSet<GTriple>, Vec<RulePat>) {
    let mut facts = HashSet::new();
    let mut rules = Vec::new();

    for st in &doc.statements {
        match st {
            Statement::Triple(tr) => {
                if let Some(gt) = to_ground(tr) {
                    facts.insert(gt);
                }
            }
            Statement::Implication { premise, conclusion, .. } => {
                let prem_pats = formula_to_patterns(premise);
                let concl_pats = formula_to_patterns(conclusion);

                if prem_pats.is_empty() && concl_pats.is_empty() {
                    continue;
                }

                rules.push(RulePat {
                    premise: prem_pats,
                    conclusion: concl_pats,
                });
            }
        }
    }

    (facts, rules)
}

/// Extract query patterns of the form `{Q} => {Q}.`
pub fn extract_queries(doc: &Document) -> Vec<Vec<(PT, PT, PT)>> {
    let mut queries = vec![];

    for st in &doc.statements {
        if let Statement::Implication { premise, conclusion, direction } = st {
            if *direction != ImplicationDir::Forward {
                continue;
            }

            let prem = formula_to_patterns(premise);
            let concl = formula_to_patterns(conclusion);

            if !prem.is_empty() && prem == concl {
                queries.push(prem);
            }
        }
    }

    queries
}

/// Naive forward-chaining to fixpoint over RulePat rules.
pub fn forward_chain(mut facts: HashSet<GTriple>, rules: &[RulePat]) -> HashSet<GTriple> {
    loop {
        let mut changed = false;

        for rule in rules {
            let sols = match_premise(&rule.premise, &facts, &HashMap::new());
            for env in sols {
                for pat in &rule.conclusion {
                    if let Some(gt) = instantiate_pat(pat, &env) {
                        if facts.insert(gt) {
                            changed = true;
                        }
                    }
                }
            }
        }

        if !changed {
            break;
        }
    }

    facts
}

//
// ------------------------- Backward chaining -------------------------
// Backward env stores PT terms, so vars can bind to lists.
//

#[derive(Debug, Clone, PartialEq, Eq)]
enum Bind {
    Term(PT),
    Alias(String),
}

type BEnv = HashMap<String, Bind>;

fn resolve_root(v: &str, env: &BEnv) -> String {
    match env.get(v) {
        Some(Bind::Alias(u)) => resolve_root(u, env),
        _ => v.to_string(),
    }
}

fn resolve_term(v: &str, env: &BEnv) -> Option<PT> {
    match env.get(v)? {
        Bind::Term(t) => Some(t.clone()),
        Bind::Alias(u) => resolve_term(u, env),
    }
}

fn bind_var_term_bwd(v: &str, val: PT, env: &mut BEnv) -> Option<()> {
    let rv = resolve_root(v, env);
    if let Some(existing) = resolve_term(&rv, env) {
        // must be consistent with existing binding
        unify_pt_pt_bwd(&existing, &val, env)
    } else {
        env.insert(rv, Bind::Term(val));
        Some(())
    }
}

fn unify_var_var_bwd(va: &str, vb: &str, env: &mut BEnv) -> Option<()> {
    let ra = resolve_root(va, env);
    let rb = resolve_root(vb, env);
    if ra == rb {
        return Some(());
    }

    let aval = resolve_term(&ra, env);
    let bval = resolve_term(&rb, env);

    match (aval, bval) {
        (Some(a), Some(b)) => unify_pt_pt_bwd(&a, &b, env),
        (Some(a), None) => { env.insert(rb, Bind::Term(a)); Some(()) }
        (None, Some(b)) => { env.insert(ra, Bind::Term(b)); Some(()) }
        (None, None) => {
            env.insert(rb, Bind::Alias(ra));
            Some(())
        }
    }
}

fn pt_to_atom_bwd(pt: &PT, env: &BEnv) -> Option<Atom> {
    match pt {
        PT::Const(a) => Some(a.clone()),
        PT::Var(v) => {
            let t = resolve_term(v, env)?;
            pt_to_atom_bwd(&t, env)
        }
        PT::List(ps) => {
            let mut v = Vec::with_capacity(ps.len());
            for p in ps {
                v.push(pt_to_atom_bwd(p, env)?);
            }
            Some(Atom::List(v))
        }
    }
}

fn strip_benv(env: BEnv) -> HashMap<String, Atom> {
    let mut out = HashMap::new();
    for k in env.keys() {
        if let Some(t) = resolve_term(k, &env) {
            if let Some(a) = pt_to_atom_bwd(&t, &env) {
                out.insert(k.clone(), a);
            }
        }
    }
    out
}

/// Backward chaining (goal-directed).
/// Rules passed here are in forward orientation already:
/// premise(body) => conclusion(head). The solver matches goals against heads.
pub fn backward_solve(
    goals: &[(PT, PT, PT)],
    facts: &HashSet<GTriple>,
    rules: &[RulePat],
) -> Vec<HashMap<String, Atom>> {
    const MAX_DEPTH: usize = 512;
    let mut seen = Vec::new();
    let sols = solve_goals_bwd(goals, facts, rules, &BEnv::new(), 0, MAX_DEPTH, &mut seen);
    sols.into_iter().map(strip_benv).collect()
}

fn solve_goals_bwd(
    goals: &[(PT, PT, PT)],
    facts: &HashSet<GTriple>,
    rules: &[RulePat],
    env: &BEnv,
    depth: usize,
    max_depth: usize,
    seen: &mut Vec<(PT, PT, PT)>,
) -> Vec<BEnv> {
    if depth > max_depth {
        return vec![];
    }
    if goals.is_empty() {
        return vec![env.clone()];
    }

    let (g0, rest) = goals.split_first().unwrap();

    // exact-goal-on-stack guard
    if seen.contains(g0) {
        return vec![];
    }
    seen.push(g0.clone());

    let mut out = vec![];

    // Builtin goal?
    if is_builtin_pat(g0) {
        let mut env2 = env.clone();
        if eval_builtin_pat_bwd(g0, &mut env2).is_some() {
            out.extend(solve_goals_bwd(
                rest, facts, rules, &env2, depth + 1, max_depth, seen,
            ));
        }
        seen.pop();
        return out;
    }

    // 1) Match facts
    for f in facts {
        let mut env2 = env.clone();
        if unify_pat_atom_bwd(g0, f, &mut env2).is_some() {
            out.extend(solve_goals_bwd(
                rest, facts, rules, &env2, depth + 1, max_depth, seen,
            ));
        }
    }

    // 2) Match rule heads
    for (i, r) in rules.iter().enumerate() {
        let fr = fresh_rule(r, i + depth * 997);
        for head_pat in &fr.conclusion {
            let mut env2 = env.clone();
            if unify_pat_pat_bwd(head_pat, g0, &mut env2).is_some() {
                let mut new_goals = fr.premise.clone();
                new_goals.extend_from_slice(rest);

                out.extend(solve_goals_bwd(
                    &new_goals, facts, rules, &env2, depth + 1, max_depth, seen,
                ));
            }
        }
    }

    seen.pop();
    out
}

//
// ------------------------- Forward matching helpers -------------------------
//

fn match_premise(
    premise: &[(PT, PT, PT)],
    facts: &HashSet<GTriple>,
    env: &HashMap<String, Atom>,
) -> Vec<HashMap<String, Atom>> {
    if premise.is_empty() {
        return vec![env.clone()];
    }

    let (p0, rest) = premise.split_first().unwrap();
    let mut out = vec![];

    if is_builtin_pat(p0) {
        let mut env2 = env.clone();
        if eval_builtin_pat(p0, &mut env2).is_some() {
            out.extend(match_premise(rest, facts, &env2));
        }
        return out;
    }

    for f in facts {
        let mut env2 = env.clone();
        if unify_pat_atom(p0, f, &mut env2).is_some() {
            out.extend(match_premise(rest, facts, &env2));
        }
    }

    out
}

//
// ------------------------- Unification (forward) -------------------------
//

fn unify_pat_atom(
    pat: &(PT, PT, PT),
    tr: &GTriple,
    env: &mut HashMap<String, Atom>,
) -> Option<()> {
    unify_term(&pat.0, &tr.s, env)?;
    unify_term(&pat.1, &tr.p, env)?;
    unify_term(&pat.2, &tr.o, env)?;
    Some(())
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

        PT::List(ps) => match atom {
            Atom::List(as_) if ps.len() == as_.len() => {
                for (p, a) in ps.iter().zip(as_) {
                    unify_term(p, a, env)?;
                }
                Some(())
            }
            _ => None,
        },
    }
}

//
// ------------------------- Unification (backward) -------------------------
//

fn unify_pat_atom_bwd(
    pat: &(PT, PT, PT),
    tr: &GTriple,
    env: &mut BEnv,
) -> Option<()> {
    unify_term_bwd(&pat.0, &tr.s, env)?;
    unify_term_bwd(&pat.1, &tr.p, env)?;
    unify_term_bwd(&pat.2, &tr.o, env)?;
    Some(())
}

fn unify_pat_pat_bwd(
    a: &(PT, PT, PT),
    b: &(PT, PT, PT),
    env: &mut BEnv,
) -> Option<()> {
    unify_pt_pt_bwd(&a.0, &b.0, env)?;
    unify_pt_pt_bwd(&a.1, &b.1, env)?;
    unify_pt_pt_bwd(&a.2, &b.2, env)?;
    Some(())
}

fn unify_term_bwd(pt: &PT, atom: &Atom, env: &mut BEnv) -> Option<()> {
    unify_pt_pt_bwd(pt, &PT::Const(atom.clone()), env)
}

fn unify_pt_pt_bwd(a: &PT, b: &PT, env: &mut BEnv) -> Option<()> {
    match (a, b) {
        (PT::Const(ca), PT::Const(cb)) => if ca == cb { Some(()) } else { None },

        (PT::Var(va), PT::Var(vb)) => unify_var_var_bwd(va, vb, env),

        (PT::Var(va), t) => bind_var_term_bwd(va, t.clone(), env),
        (t, PT::Var(vb)) => bind_var_term_bwd(vb, t.clone(), env),

        (PT::List(ae), PT::List(be)) => {
            if ae.len() != be.len() { return None; }
            for (x, y) in ae.iter().zip(be) {
                unify_pt_pt_bwd(x, y, env)?;
            }
            Some(())
        }

        _ => None,
    }
}

//
// ------------------------- Instantiation -------------------------
//

pub fn instantiate_pat(
    pat: &(PT, PT, PT),
    env: &HashMap<String, Atom>,
) -> Option<GTriple> {
    let s = inst_term(&pat.0, env)?;
    let p = inst_term(&pat.1, env)?;
    let o = inst_term(&pat.2, env)?;
    Some(GTriple { s, p, o })
}

fn inst_term(pt: &PT, env: &HashMap<String, Atom>) -> Option<Atom> {
    match pt {
        PT::Const(c) => Some(c.clone()),
        PT::Var(v) => env.get(v).cloned(),
        PT::List(ps) => {
            let mut v = Vec::with_capacity(ps.len());
            for p in ps {
                v.push(inst_term(p, env)?);
            }
            Some(Atom::List(v))
        }
    }
}

//
// ------------------------- Freshening -------------------------
//

fn fresh_rule(rule: &RulePat, salt: usize) -> RulePat {
    let mut map: HashMap<String, String> = HashMap::new();
    RulePat {
        premise: rule.premise.iter().map(|p| fresh_pat(p, salt, &mut map)).collect(),
        conclusion: rule.conclusion.iter().map(|p| fresh_pat(p, salt, &mut map)).collect(),
    }
}

fn fresh_pat(
    pat: &(PT, PT, PT),
    salt: usize,
    map: &mut HashMap<String, String>,
) -> (PT, PT, PT) {
    (
        fresh_pt(&pat.0, salt, map),
        fresh_pt(&pat.1, salt, map),
        fresh_pt(&pat.2, salt, map),
    )
}

fn fresh_pt(pt: &PT, salt: usize, map: &mut HashMap<String, String>) -> PT {
    match pt {
        PT::Const(c) => PT::Const(c.clone()),
        PT::Var(v) => {
            let nv = map.entry(v.clone()).or_insert_with(|| format!("{v}__{salt}")).clone();
            PT::Var(nv)
        }
        PT::List(xs) => PT::List(xs.iter().map(|p| fresh_pt(p, salt, map)).collect()),
    }
}

//
// ------------------------- AST -> patterns / grounding -------------------------
//

fn to_ground(tr: &Triple) -> Option<GTriple> {
    let s = term_to_atom(&tr.subject)?;
    let o = term_to_atom(&tr.object)?;
    let p = match &tr.predicate {
        Predicate::KeywordA => Atom::Iri(RDF_TYPE.into()),
        Predicate::Normal(t) => term_to_atom(t)?,
        Predicate::Inverse(t) => term_to_atom(t)?,
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
        Term::Collection(items) => {
            let mut v = Vec::with_capacity(items.len());
            for it in items {
                v.push(term_to_atom(it)?);
            }
            Some(Atom::List(v))
        }
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

fn term_to_pt(t: &Term) -> Option<PT> {
    match t {
        Term::Variable(v) => Some(PT::Var(v.clone())),
        Term::Iri(i) => Some(PT::Const(Atom::Iri(i.clone()))),
        Term::BlankNode(b) => Some(PT::Const(Atom::Blank(b.clone()))),
        Term::Literal(l) => Some(PT::Const(Atom::Literal(canon_lit(l)))),
        Term::Collection(items) => {
            let mut v = Vec::with_capacity(items.len());
            for it in items {
                v.push(term_to_pt(it)?);
            }
            Some(PT::List(v))
        }
        _ => None,
    }
}

fn pred_to_pt(p: &Predicate) -> Option<PT> {
    match p {
        Predicate::KeywordA => Some(PT::Const(Atom::Iri(RDF_TYPE.into()))),
        Predicate::Normal(t) => term_to_pt(t),
        Predicate::Inverse(t) => term_to_pt(t),
        Predicate::Has(t) => term_to_pt(t),
        _ => None,
    }
}

//
// ------------------------- Builtins (forward + backward) -------------------------
//

fn is_builtin_pat(p: &(PT, PT, PT)) -> bool {
    matches!(
        &p.1,
        PT::Const(Atom::Iri(i))
            if i == "http://www.w3.org/2000/10/swap/math#greaterThan"
    )
}

fn eval_builtin_pat(p: &(PT, PT, PT), env: &mut HashMap<String, Atom>) -> Option<()> {
    let pred = match &p.1 {
        PT::Const(Atom::Iri(i)) => i.as_str(),
        _ => return None,
    };

    match pred {
        "http://www.w3.org/2000/10/swap/math#greaterThan" => {
            let a = inst_term(&p.0, env)?;
            let b = inst_term(&p.2, env)?;
            let av = atom_to_num(&a)?;
            let bv = atom_to_num(&b)?;
            if av > bv { Some(()) } else { None }
        }
        _ => None,
    }
}

fn eval_builtin_pat_bwd(p: &(PT, PT, PT), env: &mut BEnv) -> Option<()> {
    let pred = match &p.1 {
        PT::Const(Atom::Iri(i)) => i.as_str(),
        _ => return None,
    };

    match pred {
        "http://www.w3.org/2000/10/swap/math#greaterThan" => {
            let a = pt_to_atom_bwd(&p.0, env)?;
            let b = pt_to_atom_bwd(&p.2, env)?;
            let av = atom_to_num(&a)?;
            let bv = atom_to_num(&b)?;
            if av > bv { Some(()) } else { None }
        }
        _ => None,
    }
}

fn atom_to_num(a: &Atom) -> Option<f64> {
    match a {
        Atom::Literal(s) => s.parse::<f64>().ok(),
        _ => None,
    }
}

//
// ------------------------- Literal canonicalization -------------------------
//

fn canon_lit(l: &Literal) -> String {
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

