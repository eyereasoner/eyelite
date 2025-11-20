use std::fs;

use n3lite::{parse_document, PrefixEnv, forward_chain, extract, Atom, GTriple};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = fs::read_to_string("socrates.n3")?;
    let doc = parse_document(&input)?;

    // 1) build prefix env + resolve terms
    let env = PrefixEnv::from_document(&doc);
    let doc_resolved = env.apply(&doc);

    // 2) extract facts + rules
    let (facts0, rules) = extract(&doc_resolved);

    // 3) forward chain
    let facts = forward_chain(facts0, &rules);

    // 4) check entailment
    let socrates = Atom::Iri("http://example.org/socrates#Socrates".into());
    let rdf_type = Atom::Iri("http://www.w3.org/1999/02/22-rdf-syntax-ns#type".into());
    let mortal   = Atom::Iri("http://example.org/socrates#Mortal".into());

    let goal = GTriple { s: socrates, p: rdf_type, o: mortal };

    println!("Derived {} facts total.", facts.len());
    println!("Entails Socrates mortal? {}", facts.contains(&goal));

    Ok(())
}

