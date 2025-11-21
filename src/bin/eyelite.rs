use std::{collections::HashSet, env, fs};

use eyelite::{
    parse_document, PrefixEnv, Document,
    extract, backward_solve, forward_chain, instantiate_pat,
    Atom, GTriple, RulePat, PT,
    Statement, ImplicationDir, Formula,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = env::args().nth(1).expect("usage: eyelite <file.n3>");
    let input = fs::read_to_string(path)?;

    let doc = parse_document(&input)?;

    // Resolve prefixes/IRIs strictly (no builtin prefix injection).
    let envp = PrefixEnv::from_document(&doc);
    let doc_resolved = envp.apply(&doc);

    // normalize log:implies/log:impliedBy triples into Implication statements
    let doc_norm = eyelite::normalize_implications(&doc_resolved);

    // Ground facts from the file
    let base_facts = ground_facts(&doc_norm);

    // All rules in forward orientation (backward rules flipped)
    let (_facts0, all_rules) = extract(&doc_norm);

    // Forward-only rules (=> in the source, excluding query {Q}=>{Q})
    let forward_rules = extract_forward_only_rules(&doc_norm);

    // Seed: prove any *ground* forward premises using backward solver
    let seeded_facts = seed_ground_forward_premises(
        base_facts.clone(),
        &forward_rules,
        &all_rules,
    );

    // Run forward chaining using ONLY forward rules
    let forward_result = forward_chain(seeded_facts.clone(), &forward_rules);

    // Forward-derived = forward_result minus seeded_facts
    let forward_derived: HashSet<GTriple> =
        forward_result.difference(&seeded_facts).cloned().collect();

    // Output as N3
    print_output(&forward_derived, &envp);

    Ok(())
}

/// Collect ground triples from the resolved document.
fn ground_facts(doc: &Document) -> HashSet<GTriple> {
    let mut facts = HashSet::new();
    for st in &doc.statements {
        if let Statement::Triple(tr) = st {
            if let Some(gt) = triple_to_ground(tr) {
                facts.insert(gt);
            }
        }
    }
    facts
}

/// Convert a Triple to a ground GTriple if it has no variables.
fn triple_to_ground(tr: &eyelite::Triple) -> Option<GTriple> {
    let s = term_to_atom(&tr.subject)?;
    let o = term_to_atom(&tr.object)?;

    let p = match &tr.predicate {
        eyelite::Predicate::KeywordA => Atom::Iri(eyelite::RDF_TYPE.into()),
        eyelite::Predicate::Normal(t) => term_to_atom(t)?,
        eyelite::Predicate::Inverse(t) => term_to_atom(t)?,
        eyelite::Predicate::Has(t) => term_to_atom(t)?,
        _ => return None,
    };

    Some(GTriple { s, p, o })
}

fn term_to_atom(t: &eyelite::Term) -> Option<Atom> {
    match t {
        eyelite::Term::Iri(i) => Some(Atom::Iri(i.clone())),
        eyelite::Term::BlankNode(b) => Some(Atom::Blank(b.clone())),
        eyelite::Term::Literal(l) => Some(Atom::Literal(canon_lit(l))),
        _ => None, // variables / formulas / paths etc.
    }
}

/// Extract only forward (=>) rules from the document, skipping query rules {Q}=>{Q}.
fn extract_forward_only_rules(doc: &Document) -> Vec<RulePat> {
    let mut rules = vec![];

    for st in &doc.statements {
        if let Statement::Implication { premise, conclusion, direction } = st {
            if *direction != ImplicationDir::Forward {
                continue;
            }

            let prem = formula_to_patterns(premise);
            let concl = formula_to_patterns(conclusion);

            // Skip query rules {Q} => {Q}
            if prem == concl {
                continue;
            }

            if !prem.is_empty() && !concl.is_empty() {
                rules.push(RulePat { premise: prem, conclusion: concl });
            }
        }
    }

    rules
}

/// Turn a formula into triple patterns PT,PT,PT
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

fn term_to_pt(t: &eyelite::Term) -> Option<PT> {
    match t {
        eyelite::Term::Variable(v) => Some(PT::Var(v.clone())),
        eyelite::Term::Iri(i) => Some(PT::Const(Atom::Iri(i.clone()))),
        eyelite::Term::BlankNode(b) => Some(PT::Const(Atom::Blank(b.clone()))),
        eyelite::Term::Literal(l) => Some(PT::Const(Atom::Literal(canon_lit(l)))),
        _ => None,
    }
}

fn pred_to_pt(p: &eyelite::Predicate) -> Option<PT> {
    match p {
        eyelite::Predicate::KeywordA => Some(PT::Const(Atom::Iri(eyelite::RDF_TYPE.into()))),
        eyelite::Predicate::Normal(t) => term_to_pt(t),
        _ => None,
    }
}

/// Add ground premises of forward rules that can be proven by backward reasoning.
fn seed_ground_forward_premises(
    base_facts: HashSet<GTriple>,
    forward_rules: &[RulePat],
    all_rules: &[RulePat],
) -> HashSet<GTriple> {
    let mut facts = base_facts;

    for rule in forward_rules {
        for pat in &rule.premise {
            if is_ground_pat(pat) {
                let sols = backward_solve(std::slice::from_ref(pat), &facts, all_rules);
                for b in sols {
                    if let Some(gt) = instantiate_pat(pat, &b) {
                        facts.insert(gt);
                    }
                }
            }
        }
    }

    facts
}

fn is_ground_pat(p: &(PT, PT, PT)) -> bool {
    let (s, p2, o) = p;
    !matches!(s, PT::Var(_)) && !matches!(p2, PT::Var(_)) && !matches!(o, PT::Var(_))
}

/// Print derived triples as N3 using only default ":" if available.
fn print_output(triples: &HashSet<GTriple>, envp: &PrefixEnv) {
    if triples.is_empty() {
        return;
    }

    if let Some(ns) = envp.prefixes.get("") {
        println!("@prefix : <{}>.\n", ns);
    }

    // Collect + sort for deterministic output
    let mut v: Vec<&GTriple> = triples.iter().collect();
    v.sort_by(|a, b| triple_key(a).cmp(&triple_key(b)));

    for t in v {
        let s = render_atom(&t.s, envp);
        let p = render_predicate(&t.p, envp);
        let o = render_atom(&t.o, envp);
        println!("{s} {p} {o} .");
    }
}

fn triple_key(t: &GTriple) -> (String, String, String) {
    (atom_key(&t.s), atom_key(&t.p), atom_key(&t.o))
}

fn atom_key(a: &Atom) -> String {
    match a {
        Atom::Iri(i) => i.clone(),
        Atom::Blank(b) => format!("_:{b}"),
        Atom::Literal(l) => l.clone(),
    }
}

fn render_atom(a: &Atom, envp: &PrefixEnv) -> String {
    match a {
        Atom::Iri(i) => {
            if let Some(ns) = envp.prefixes.get("") {
                if i.starts_with(ns) {
                    return format!(":{}", &i[ns.len()..]);
                }
            }
            format!("<{}>", i)
        }
        Atom::Blank(b) => format!("_:{b}"),
        Atom::Literal(l) => l.clone(),
    }
}

fn render_predicate(a: &Atom, envp: &PrefixEnv) -> String {
    match a {
        Atom::Iri(i) if i == eyelite::RDF_TYPE => "a".to_string(),
        _ => render_atom(a, envp),
    }
}

fn canon_lit(l: &eyelite::Literal) -> String {
    match l {
        eyelite::Literal::RdfString { lex, lang, datatype } => {
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
        eyelite::Literal::Integer(x) => x.clone(),
        eyelite::Literal::Decimal(x) => x.clone(),
        eyelite::Literal::Double(x) => x.clone(),
        eyelite::Literal::Boolean(b) => b.to_string(),
    }
}

