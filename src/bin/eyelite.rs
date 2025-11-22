use std::{collections::HashSet, env, fs};

use eyelite::{
    parse_document, normalize_implications, forward_chain, backward_solve, instantiate_pat,
    PrefixEnv, Document, Statement, Formula, ImplicationDir, RulePat, PT, Atom, GTriple,
    Predicate, Term, Literal, RDF_TYPE,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = env::args().nth(1).expect("usage: eyelite <file.n3>");
    let input = fs::read_to_string(path)?;

    let doc = parse_document(&input)?;

    // Strict prefix env (no auto-filling missing IRIs)
    let envp = PrefixEnv::from_document(&doc);
    let doc_resolved = envp.apply(&doc);

    // Rewrite log:implies / log:impliedBy triples into Implication statements
    let doc_norm = normalize_implications(&doc_resolved);

    // Ground facts from file
    let base_facts = ground_facts(&doc_norm);

    // Split rules by original direction
    let backward_rules = extract_backward_only_rules(&doc_norm); // <= / log:impliedBy
    let forward_rules  = extract_forward_only_rules(&doc_norm);  // => / log:implies

    // Phase 1: saturate using backward rules only (plus builtins)
    let facts_after_backward = forward_chain(base_facts.clone(), &backward_rules);

    // Phase 1.5: for each forward rule, prove its premise by backward solving
    // (using ONLY backward rules, not forward rules) and seed its conclusions.
    let seeded_from_forward = seed_forward_rules_via_backward(
        &facts_after_backward,
        &forward_rules,
        &backward_rules,
    );

    let mut facts_seeded = facts_after_backward.clone();
    facts_seeded.extend(seeded_from_forward.iter().cloned());

    // Phase 2: saturate using forward rules only
    let facts_after_forward = forward_chain(facts_seeded, &forward_rules);

    // Forward-derived = Phase2 \ Phase1
    let forward_derived: HashSet<GTriple> =
        facts_after_forward
            .difference(&facts_after_backward)
            .cloned()
            .collect();

    // Output deterministically
    print_output(&forward_derived, &envp);

    Ok(())
}

/// Backward-solve each forward rule’s premise to seed its conclusions.
/// Uses ONLY backward rules + builtins against current facts.
fn seed_forward_rules_via_backward(
    facts: &HashSet<GTriple>,
    forward_rules: &[RulePat],
    backward_rules: &[RulePat],
) -> HashSet<GTriple> {
    let mut out = HashSet::new();

    for rule in forward_rules {
        let sols = backward_solve(&rule.premise, facts, backward_rules);
        for b in sols {
            for pat in &rule.conclusion {
                if let Some(gt) = instantiate_pat(pat, &b) {
                    out.insert(gt);
                }
            }
        }
    }

    out
}

/// Collect ground triples from the resolved+normalized document.
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

/// Extract only backward (<=) rules (including <= true. axioms).
fn extract_backward_only_rules(doc: &Document) -> Vec<RulePat> {
    let mut rules = vec![];

    for st in &doc.statements {
        if let Statement::Implication { premise, conclusion, direction } = st {
            if *direction != ImplicationDir::Backward {
                continue;
            }

            let prem = formula_to_patterns(premise);
            let concl = formula_to_patterns(conclusion);

            if !concl.is_empty() {
                rules.push(RulePat { premise: prem, conclusion: concl });
            }
        }
    }

    rules
}

/// Turn a formula into triple patterns (PT,PT,PT)
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
        _ => None,
    }
}

/// Print derived triples as N3 using only default ":" if available, deterministically.
fn print_output(triples: &HashSet<GTriple>, envp: &PrefixEnv) {
    if triples.is_empty() {
        return;
    }

    if let Some(ns) = envp.prefixes.get("") {
        println!("@prefix : <{}>.\n", ns);
    }

    let mut v: Vec<&GTriple> = triples.iter().collect();
    v.sort_by(|a, b| triple_key(a).cmp(&triple_key(b)));

    for t in v {
        let s = render_atom(&t.s, envp);
        let p = render_predicate(&t.p, envp);
        let o = render_atom(&t.o, envp);
        println!("{s} {p} {o} .");
    }
}

fn render_predicate(a: &Atom, envp: &PrefixEnv) -> String {
    match a {
        Atom::Iri(i) if i == RDF_TYPE => "a".to_string(),
        _ => render_atom(a, envp),
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
        Atom::List(items) => {
            let inside = items
                .iter()
                .map(|x| render_atom(x, envp))
                .collect::<Vec<_>>()
                .join(" ");
            format!("({inside})")
        }
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
        Atom::List(xs) => {
            let inside = xs.iter().map(atom_key).collect::<Vec<_>>().join(" ");
            format!("({inside})")
        }
    }
}

/// Canonical literal string (must match reasoner expectations).
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

