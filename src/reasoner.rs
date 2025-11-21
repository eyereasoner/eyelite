use std::collections::{HashMap, HashSet};

use crate::ast::*;
use crate::resolve::RDF_TYPE;

/// Full IRI for math:greaterThan
/// math: namespace is http://www.w3.org/2000/10/swap/math# :contentReference[oaicite:2]{index=2}
const MATH_GREATER_THAN: &str = "http://www.w3.org/2000/10/swap/math#greaterThan";

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Atom {
    Iri(String),
    Blank(String),
    Literal(String), // canonical string form
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct GTriple {
    pub s: Atom,
    pub p: Atom,
    pub o: Atom,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PT {
    Var(String),
    Const(Atom),
}

#[derive(Debug, Clone)]
pub struct RulePat {
    premise: Vec<(PT, PT, PT)>,
    conclusion: Vec<(PT, PT, PT)>,
}

/// Extract ground triples + Horn-like rules from a resolved Document.
///
/// - Forward rules `{P} => {C}.` are kept as-is.
/// - Backward rules `{C} <= {P}.` are converted to forward orientation `P => C`,
///   so we can use them in both forward and backward reasoning.
/// - Query rules `{Q} => {Q}.` are *not* added to rules; they are detected separately.
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
                let prem_pats = formula_to_patterns(premise);
                let concl_pats = formula_to_patterns(conclusion);

                // Detect query rules {Q} => {Q}. and skip them as rules.
                if *direction == ImplicationDir::Forward && prem_pats == concl_pats {
                    continue;
                }

                match direction {
                    ImplicationDir::Forward => {
                        if !prem_pats.is_empty() && !concl_pats.is_empty() {
                            rules.push(RulePat {
                                premise: prem_pats,
                                conclusion: concl_pats,
                            });
                        }
                    }
                    ImplicationDir::Backward => {
                        // C <= P  ==>  P => C
                        if !prem_pats.is_empty() && !concl_pats.is_empty() {
                            rules.push(RulePat {
                                premise: concl_pats,
                                conclusion: prem_pats,
                            });
                        }
                    }
                }
            }
        }
    }

    (facts, rules)
}

/// Find query goals embedded as `{ Q } => { Q } .`
/// Returns a list of conjunctions (each conjunction is a Vec of triple patterns).
pub fn extract_queries(doc: &Document) -> Vec<Vec<(PT, PT, PT)>> {
    let mut qs = vec![];
    for st in &doc.statements {
        if let Statement::Implication { premise, conclusion, direction } = st {
            if *direction != ImplicationDir::Forward {
                continue;
            }
            let prem = formula_to_patterns(premise);
            let concl = formula_to_patterns(conclusion);
            if prem == concl && !prem.is_empty() {
                qs.push(prem);
            }
        }
    }
    qs
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

/// -------------------------
/// Forward chaining (fixpoint)
/// -------------------------

pub fn forward_chain(mut facts: HashSet<GTriple>, rules: &[RulePat]) -> HashSet<GTriple> {
    loop {
        let mut added_any = false;

        for rule in rules {
            let bindings = match_premise(&rule.premise, &facts);
            for b in bindings {
                for pat in &rule.conclusion {
                    if let Some(gt) = instantiate_pat(pat, &b) {
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
        // Builtin premise: evaluate instead of matching to facts.
        if is_builtin_pattern(pp) {
            let mut next_envs = vec![];
            for env in &envs {
                if let Some(env2) = eval_builtin(ps, pp, po, env) {
                    next_envs.push(env2);
                }
            }
            envs = next_envs;
            continue;
        }

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

/// -------------------------
/// Backward chaining (goals)
/// -------------------------

/// Solve a conjunction of goal patterns against facts+rules.
/// Returns all satisfying bindings (toy SLD resolution).
pub fn backward_solve(
    goals: &[(PT, PT, PT)],
    facts: &HashSet<GTriple>,
    rules: &[RulePat],
) -> Vec<HashMap<String, Atom>> {
    solve_goals(goals.to_vec(), HashMap::new(), facts, rules, 0)
}

fn solve_goals(
    goals: Vec<(PT, PT, PT)>,
    env: HashMap<String, Atom>,
    facts: &HashSet<GTriple>,
    rules: &[RulePat],
    depth: usize,
) -> Vec<HashMap<String, Atom>> {
    if goals.is_empty() {
        return vec![env];
    }
    if depth > 50 {
        return vec![]; // recursion guard
    }

    let (g, rest) = goals.split_first().unwrap();
    let (ps, pp, po) = g;

    // Builtin goal: evaluate directly.
    if is_builtin_pattern(pp) {
        if let Some(env2) = eval_builtin(ps, pp, po, &env) {
            return solve_goals(rest.to_vec(), env2, facts, rules, depth + 1);
        } else {
            return vec![];
        }
    }

    let mut out = vec![];

    // 1) Try matching a fact.
    for f in facts {
        if let Some(env2) = unify(ps, pp, po, f, &env) {
            out.extend(solve_goals(rest.to_vec(), env2, facts, rules, depth + 1));
        }
    }

    // 2) Try matching a rule conclusion, then prove its premise.
    for (ri, rule) in rules.iter().enumerate() {
        let frule = freshen_rule(rule, depth * 10_000 + ri);

        for concl_pat in &frule.conclusion {
            let mut env2 = env.clone();
            if unify_pat_pat(g, concl_pat, &mut env2).is_some() {
                let mut new_goals = frule.premise.clone();
                new_goals.extend_from_slice(rest);
                out.extend(solve_goals(new_goals, env2, facts, rules, depth + 1));
            }
        }
    }

    out
}

/// Unify goal pattern with rule conclusion pattern (symmetric, toy unification).
/// If both sides are unbound vars, we leave them unbound (fine for your examples).
fn unify_pat_pat(
    g: &(PT, PT, PT),
    c: &(PT, PT, PT),
    env: &mut HashMap<String, Atom>,
) -> Option<()> {
    let (gs, gp, go) = g;
    let (cs, cp, co) = c;
    unify_pt_pt(gs, cs, env)?;
    unify_pt_pt(gp, cp, env)?;
    unify_pt_pt(go, co, env)?;
    Some(())
}

fn unify_pt_pt(a: &PT, b: &PT, env: &mut HashMap<String, Atom>) -> Option<()> {
    match (a, b) {
        (PT::Const(ca), PT::Const(cb)) => if ca == cb { Some(()) } else { None },

        (PT::Var(va), PT::Const(cb)) => bind_var(va, cb.clone(), env),
        (PT::Const(ca), PT::Var(vb)) => bind_var(vb, ca.clone(), env),

        (PT::Var(va), PT::Var(vb)) => {
            let va_val = env.get(va).cloned();
            let vb_val = env.get(vb).cloned();
            match (va_val, vb_val) {
                (Some(x), Some(y)) => if x == y { Some(()) } else { None },
                (Some(x), None) => { env.insert(vb.clone(), x); Some(()) }
                (None, Some(y)) => { env.insert(va.clone(), y); Some(()) }
                (None, None) => Some(()),
            }
        }
    }
}

fn bind_var(v: &str, val: Atom, env: &mut HashMap<String, Atom>) -> Option<()> {
    if let Some(bound) = env.get(v) {
        if *bound == val { Some(()) } else { None }
    } else {
        env.insert(v.to_string(), val);
        Some(())
    }
}

/// Rename rule variables to avoid collisions (freshening).
fn freshen_rule(rule: &RulePat, salt: usize) -> RulePat {
    let map: HashMap<String, String> = HashMap::new();

    fn fresh_pt(pt: &PT, salt: usize, map: &mut HashMap<String, String>) -> PT {
        match pt {
            PT::Const(c) => PT::Const(c.clone()),
            PT::Var(v) => {
                let nv = map
                    .entry(v.clone())
                    .or_insert_with(|| format!("{v}__{salt}"))
                    .clone();
                PT::Var(nv)
            }
        }
    }

    let fresh_triple = |(s,p,o): &(PT,PT,PT), salt, map: &mut HashMap<String,String>| {
        (
            fresh_pt(s, salt, map),
            fresh_pt(p, salt, map),
            fresh_pt(o, salt, map),
        )
    };

    let mut m = map;
    let premise = rule.premise.iter().map(|t| fresh_triple(t, salt, &mut m)).collect();
    let conclusion = rule.conclusion.iter().map(|t| fresh_triple(t, salt, &mut m)).collect();
    RulePat { premise, conclusion }
}

/// Instantiate a pattern triple under bindings into a ground triple.
pub fn instantiate_pat(
    pat: &(PT, PT, PT),
    env: &HashMap<String, Atom>
) -> Option<GTriple> {
    let (ps, pp, po) = pat;
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

/// -------------------------
/// Builtins (toy subset)
/// -------------------------

fn is_builtin_pattern(pp: &PT) -> bool {
    matches!(pp, PT::Const(Atom::Iri(iri)) if iri == MATH_GREATER_THAN)
}

fn eval_builtin(
    ps: &PT, pp: &PT, po: &PT,
    env: &HashMap<String, Atom>
) -> Option<HashMap<String, Atom>> {
    // Only math:greaterThan right now.
    if !is_builtin_pattern(pp) {
        return None;
    }

    let s_val = pt_value(ps, env)?;
    let o_val = pt_value(po, env)?;

    let s_num = parse_number(&s_val)?;
    let o_num = parse_number(&o_val)?;

    if s_num > o_num {
        Some(env.clone())
    } else {
        None
    }
}

/// Get bound value of a PT (must be ground after bindings).
fn pt_value(pt: &PT, env: &HashMap<String, Atom>) -> Option<Atom> {
    match pt {
        PT::Const(c) => Some(c.clone()),
        PT::Var(v) => env.get(v).cloned(),
    }
}

/// Parse numeric atoms for math builtins.
/// Spec expects numeric literals. We accept anything f64-parsable. :contentReference[oaicite:3]{index=3}
fn parse_number(a: &Atom) -> Option<f64> {
    match a {
        Atom::Literal(s) => s.parse::<f64>().ok(),
        _ => None,
    }
}

/// Canonical literal string for hashing.
/// (Same one you added earlier.)
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

