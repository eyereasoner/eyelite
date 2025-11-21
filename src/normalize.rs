use crate::ast::*;
use crate::resolve::{LOG_IMPLIES, LOG_IMPLIED_BY};

/// Rewrite `{P} log:implies {C}.` and `{C} log:impliedBy {P}.`
/// into `Statement::Implication` nodes.
///
/// Call this **after** prefix resolution so predicates are full IRIs.
pub fn normalize_implications(doc: &Document) -> Document {
    let mut out = Vec::with_capacity(doc.statements.len());

    for st in &doc.statements {
        match st {
            Statement::Triple(tr) => {
                // Only triples where both subject and object are formulas
                if let (Term::Formula(prem), Term::Formula(concl)) =
                    (&tr.subject, &tr.object)
                {
                    // Predicate must be a normal IRI (already expanded)
                    let pred_iri = match &tr.predicate {
                        Predicate::Normal(Term::Iri(i)) => Some(i.as_str()),
                        _ => None,
                    };

                    if let Some(piri) = pred_iri {
                        if piri == LOG_IMPLIES {
                            out.push(Statement::Implication {
                                premise: prem.clone(),
                                conclusion: concl.clone(),
                                direction: ImplicationDir::Forward,
                            });
                            continue;
                        } else if piri == LOG_IMPLIED_BY {
                            out.push(Statement::Implication {
                                premise: prem.clone(),
                                conclusion: concl.clone(),
                                direction: ImplicationDir::Backward,
                            });
                            continue;
                        }
                    }
                }

                // Not an implication triple → keep as triple
                out.push(st.clone());
            }
            _ => out.push(st.clone()),
        }
    }

    Document {
        directives: doc.directives.clone(),
        statements: out,
    }
}

