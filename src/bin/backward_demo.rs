use std::{env, fs, collections::HashSet};

use eyelite::{
    parse_document, PrefixEnv, Document,
    extract, extract_queries, backward_solve, instantiate_pat,
    Atom, GTriple
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let rules_path = env::args().nth(1)
        .expect("usage: backward_demo <rules.n3> <query.n3>");
    let query_path = env::args().nth(2)
        .expect("usage: backward_demo <rules.n3> <query.n3>");

    let rules_doc = parse_document(&fs::read_to_string(rules_path)?)?;
    let query_doc = parse_document(&fs::read_to_string(query_path)?)?;

    // Merge docs so prefixes/builtins are in one env.
    let merged = Document {
        directives: [rules_doc.directives.clone(), query_doc.directives.clone()].concat(),
        statements: [rules_doc.statements.clone(), query_doc.statements.clone()].concat(),
    };

    let envp = PrefixEnv::from_document(&merged);
    let merged_resolved = envp.apply(&merged);

    let queries = extract_queries(&merged_resolved);
    let (facts, rules) = extract(&merged_resolved);

    let mut answers: HashSet<GTriple> = HashSet::new();

    for q in queries {
        for b in backward_solve(&q, &facts, &rules) {
            for pat in &q {
                if let Some(gt) = instantiate_pat(pat, &b) {
                    answers.insert(gt);
                }
            }
        }
    }

    // Print in a simple N3-ish way, using only default ":" prefix.
    if let Some(ns) = envp.prefixes.get("") {
        println!("@prefix : <{}>.", ns);
        println!();
    }

    for t in &answers {
        println!(
            "{} {} {} .",
            render_atom(&t.s, &envp),
            render_atom(&t.p, &envp),
            render_atom(&t.o, &envp),
        );
    }

    Ok(())
}

fn render_atom(a: &Atom, env: &PrefixEnv) -> String {
    match a {
        Atom::Iri(i) => {
            if let Some(ns) = env.prefixes.get("") {
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

