use std::collections::HashMap;

use crate::ast::*;

pub const RDF_NS:  &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#";
pub const RDFS_NS: &str = "http://www.w3.org/2000/01/rdf-schema#";
pub const LOG_NS:  &str = "http://www.w3.org/2000/10/swap/log#";
pub const XSD_NS:  &str = "http://www.w3.org/2001/XMLSchema#";

pub const RDF_TYPE: &str = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";

#[derive(Debug, Clone)]
pub struct PrefixEnv {
    pub base: Option<String>,
    pub prefixes: HashMap<String, String>, // prefix -> namespace IRI (without local)
}

impl PrefixEnv {
    pub fn from_document(doc: &Document) -> Self {
        let mut prefixes = HashMap::new();

        // EYE-like builtins / common defaults
        prefixes.insert("rdf".into(),  RDF_NS.into());
        prefixes.insert("rdfs".into(), RDFS_NS.into());
        prefixes.insert("log".into(),  LOG_NS.into());
        prefixes.insert("xsd".into(),  XSD_NS.into());

        let mut base: Option<String> = None;

        // First pass: pick up explicit bases/prefixes
        for d in &doc.directives {
            match d {
                Directive::Base { iri } if !iri.is_empty() => {
                    base = Some(iri.clone());
                }
                Directive::Prefix { prefix, iri } => {
                    if !iri.is_empty() {
                        prefixes.insert(prefix.clone(), iri.clone());
                    }
                }
                _ => {}
            }
        }

        // Second pass: fill empty @prefix foo: . with builtins if known
        for d in &doc.directives {
            if let Directive::Prefix { prefix, iri } = d {
                if iri.is_empty() {
                    if let Some(builtin) = prefixes.get(prefix).cloned() {
                        prefixes.insert(prefix.clone(), builtin);
                    } else if prefix.is_empty() {
                        if let Some(b) = &base {
                            prefixes.insert(prefix.clone(), b.clone());
                        }
                    }
                }
            }
        }

        // If still no default prefix and no base, give a harmless fallback
        prefixes.entry("".into())
            .or_insert_with(|| base.clone().unwrap_or_else(|| "http://example.org/".into()));

        PrefixEnv { base, prefixes }
    }

    /// Expand prefixed names / relative IRIs through the env.
    pub fn expand_term(&self, t: &Term) -> Term {
        match t {
            Term::Iri(i) => Term::Iri(self.resolve_iri(i)),
            Term::PrefixedName { prefix, local } => {
                let pfx = prefix.clone().unwrap_or_default();
                let loc = local.clone().unwrap_or_default();
                if let Some(ns) = self.prefixes.get(&pfx) {
                    Term::Iri(format!("{ns}{loc}"))
                } else {
                    // unknown prefix: keep as-is
                    t.clone()
                }
            }
            Term::Collection(items) => {
                Term::Collection(items.iter().map(|x| self.expand_term(x)).collect())
            }
            Term::BlankNodePropertyList(props) => {
                let mut out = vec![];
                for (pred, objs) in props {
                    let ep = self.expand_predicate(pred);
                    let eobjs = objs.iter().map(|o| self.expand_term(o)).collect();
                    out.push((ep, eobjs));
                }
                Term::BlankNodePropertyList(out)
            }
            Term::Formula(f) => Term::Formula(self.expand_formula(f)),
            Term::Path(p) => {
                let head = Box::new(self.expand_term(&p.head));
                let steps = p.steps.iter()
                    .map(|(d, tm)| (d.clone(), self.expand_term(tm)))
                    .collect();
                Term::Path(Path { head, steps })
            }
            _ => t.clone(),
        }
    }

    pub fn expand_predicate(&self, p: &Predicate) -> Predicate {
        match p {
            Predicate::Normal(t)  => Predicate::Normal(self.expand_term(t)),
            Predicate::Inverse(t) => Predicate::Inverse(self.expand_term(t)),
            Predicate::Has(t)     => Predicate::Has(self.expand_term(t)),
            _ => p.clone(),
        }
    }

    pub fn expand_statement(&self, s: &Statement) -> Statement {
        match s {
            Statement::Triple(tr) => {
                Statement::Triple(Triple {
                    subject: self.expand_term(&tr.subject),
                    predicate: self.expand_predicate(&tr.predicate),
                    object: self.expand_term(&tr.object),
                })
            }
            Statement::Implication { premise, conclusion, direction } => {
                Statement::Implication {
                    premise: self.expand_formula(premise),
                    conclusion: self.expand_formula(conclusion),
                    direction: direction.clone(),
                }
            }
        }
    }

    pub fn expand_formula(&self, f: &Formula) -> Formula {
        Formula {
            statements: f.statements.iter().map(|s| self.expand_statement(s)).collect(),
        }
    }

    pub fn apply(&self, doc: &Document) -> Document {
        Document {
            directives: doc.directives.clone(), // keep original directives
            statements: doc.statements.iter().map(|s| self.expand_statement(s)).collect(),
        }
    }

    fn resolve_iri(&self, s: &str) -> String {
        if s.starts_with("http://") || s.starts_with("https://") || s.starts_with("urn:") {
            s.to_string()
        } else if let Some(base) = &self.base {
            format!("{base}{s}")
        } else {
            s.to_string()
        }
    }
}

