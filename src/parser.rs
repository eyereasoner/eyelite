use pest::iterators::Pair;
use pest::Parser as PestParser; // <- trait (gives N3Parser::parse)
use pest_derive::Parser;        // <- derive macro (generates Rule enum + impl)
use thiserror::Error;

use crate::ast::*;

#[derive(Parser)]
#[grammar = "n3.pest"]
struct N3Parser;

#[derive(Debug, Error)]
pub enum ParseError {
    #[error("parse error: {0}")]
    Pest(#[from] pest::error::Error<Rule>),
    #[error("unexpected rule: {0:?}")]
    Unexpected(Rule),
}

pub fn parse_document(input: &str) -> Result<Document, ParseError> {
    let mut pairs = N3Parser::parse(Rule::document, input)?;
    let doc_pair = pairs.next().unwrap();
    build_document(doc_pair)
}

fn build_document(pair: Pair<Rule>) -> Result<Document, ParseError> {
    let mut directives = vec![];
    let mut statements = vec![];

    for item in pair.into_inner() {
        match item.as_rule() {
            Rule::directive => directives.push(build_directive(item)?),
            Rule::statement => statements.extend(build_statement(item)?),
            Rule::statement_or_directive => {
                for inner in item.into_inner() {
                    match inner.as_rule() {
                        Rule::directive => directives.push(build_directive(inner)?),
                        Rule::statement => statements.extend(build_statement(inner)?),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }

    Ok(Document { directives, statements })
}

fn build_directive(pair: Pair<Rule>) -> Result<Directive, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::prefix_id | Rule::sparql_prefix => {
            let mut prefix: Option<String> = None;
            let mut iri: Option<String> = None;

            for p in inner.into_inner() {
                match p.as_rule() {
                    Rule::PNAME_NS => {
                        let pns = p.as_str(); // like "rdfs:" or ":"
                        prefix = Some(pns.trim_end_matches(':').to_string());
                    }
                    Rule::IRIREF => {
                        iri = Some(strip_iri(p.as_str()));
                    }
                    _ => {} // skip PREFIX_KW / dots / etc.
                }
            }

            Ok(Directive::Prefix {
                prefix: prefix.unwrap_or_default(),
                iri: iri.unwrap_or_default(), // empty if missing (EYE-style)
            })
        }

        Rule::base_id | Rule::sparql_base => {
            // base keyword may also appear as a normal rule, so scan similarly:
            let mut iri: Option<String> = None;
            for p in inner.clone().into_inner() {
                if p.as_rule() == Rule::IRIREF {
                    iri = Some(strip_iri(p.as_str()));
                }
            }
            Ok(Directive::Base { iri: iri.unwrap_or_default() })
        }

        r => Err(ParseError::Unexpected(r)),
    }
}

fn build_statement(pair: Pair<Rule>) -> Result<Vec<Statement>, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::triples => build_triples(inner),
        Rule::implication => Ok(vec![build_implication(inner)?]),
        r => Err(ParseError::Unexpected(r)),
    }
}

fn build_implication(pair: Pair<Rule>) -> Result<Statement, ParseError> {
    let mut it = pair.into_inner();
    let premise = build_formula(it.next().unwrap())?;
    let op = it.next().unwrap().as_str(); // now Rule::implication_op
    let conclusion = build_formula(it.next().unwrap())?;
    let direction = if op == "=>" {
        ImplicationDir::Forward
    } else {
        ImplicationDir::Backward
    };
    Ok(Statement::Implication { premise, conclusion, direction })
}

fn build_triples(pair: Pair<Rule>) -> Result<Vec<Statement>, ParseError> {
    let mut it = pair.into_inner();
    let subj = build_path(it.next().unwrap())?;
    let pol = it.next().unwrap();

    let mut out = vec![];

    for vol in pol.into_inner().filter(|p| p.as_rule() == Rule::verb_obj_list) {
        let mut vol_it = vol.into_inner();
        let verb = build_verb(vol_it.next().unwrap())?;
        let objs = build_object_list(vol_it.next().unwrap())?;

        for obj in objs {
            out.push(Statement::Triple(Triple {
                subject: subj.clone(),
                predicate: verb.clone(),
                object: obj,
            }));
        }
    }

    Ok(out)
}

fn build_verb(pair: Pair<Rule>) -> Result<Predicate, ParseError> {
    match pair.as_rule() {
        Rule::kw_a => Ok(Predicate::KeywordA),
        Rule::kw_eq => Ok(Predicate::KeywordEquals),
        Rule::inverse_predicate => {
            let term = build_path(pair.into_inner().next().unwrap())?;
            Ok(Predicate::Inverse(term))
        }
        Rule::has_predicate => {
            let term = build_path(pair.into_inner().next().unwrap())?;
            Ok(Predicate::Has(term))
        }
        Rule::path => {
            let term = build_path(pair)?;
            Ok(Predicate::Normal(term))
        }
        r => Err(ParseError::Unexpected(r)),
    }
}

fn build_object_list(pair: Pair<Rule>) -> Result<Vec<Term>, ParseError> {
    pair.into_inner()
        .filter(|p| p.as_rule() == Rule::object)
        .map(|o| build_path(o.into_inner().next().unwrap()))
        .collect()
}

fn build_formula(pair: Pair<Rule>) -> Result<Formula, ParseError> {
    let mut stmts = vec![];

    for s in pair.into_inner() {
        match s.as_rule() {
            // If formula_stmt is non-silent, we’ll see it:
            Rule::formula_stmt => {
                let inner = s.into_inner().next().unwrap();
                match inner.as_rule() {
                    Rule::implication => stmts.push(build_implication(inner)?),
                    Rule::triples_formula => stmts.extend(build_triples(inner)?),
                    _ => {}
                }
            }

            // If formula_stmt is silent (current grammar), we see these directly:
            Rule::implication => stmts.push(build_implication(s)?),
            Rule::triples_formula => stmts.extend(build_triples(s)?),

            // Harmless fallback:
            Rule::statement => stmts.extend(build_statement(s)?),

            _ => {}
        }
    }

    Ok(Formula { statements: stmts })
}

fn build_path(pair: Pair<Rule>) -> Result<Term, ParseError> {
    let mut it = pair.into_inner();

    let head_item = it.next().unwrap();
    let head = build_term(head_item)?;

    let mut steps = vec![];
    while let Some(dir_pair) = it.next() {
        let dir = match dir_pair.as_str() {
            "!" => PathDir::Forward,
            "^" => PathDir::Reverse,
            _ => return Err(ParseError::Unexpected(dir_pair.as_rule())),
        };
        let item_pair = it.next().unwrap();
        let item = build_term(item_pair)?;
        steps.push((dir, item));
    }

    if steps.is_empty() {
        Ok(head)
    } else {
        Ok(Term::Path(Path {
            head: Box::new(head),
            steps,
        }))
    }
}

fn build_term(pair: Pair<Rule>) -> Result<Term, ParseError> {
    match pair.as_rule() {
        Rule::term => build_term(pair.into_inner().next().unwrap()),
        Rule::formula => Ok(Term::Formula(build_formula(pair)?)),
        Rule::collection => {
            let items = pair.into_inner()
                .filter(|p| p.as_rule() == Rule::path)
                .map(build_path)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Term::Collection(items))
        }
        Rule::blank_node_property_list => {
            let mut props = vec![];
            for pol in pair.into_inner() {
                if pol.as_rule() == Rule::pred_obj_list {
                    for vol in pol.into_inner().filter(|p| p.as_rule() == Rule::verb_obj_list) {
                        let mut vol_it = vol.into_inner();
                        let verb = build_verb(vol_it.next().unwrap())?;
                        let objs = build_object_list(vol_it.next().unwrap())?;
                        props.push((verb, objs));
                    }
                }
            }
            Ok(Term::BlankNodePropertyList(props))
        }
        Rule::literal => build_literal(pair),
        Rule::numeric_literal => build_numeric(pair),
        Rule::boolean_literal => {
            let s = pair.as_str().to_ascii_lowercase();
            Ok(Term::Literal(Literal::Boolean(s.contains("true"))))
        }
        Rule::rdf_literal => {
            let mut it = pair.into_inner();
            let lex = unescape_string(it.next().unwrap().as_str());
            let mut lang = None;
            let mut datatype = None;

            for p in it {
                match p.as_rule() {
                    Rule::LANGTAG => lang = Some(p.as_str().to_string()),
                    Rule::iri | Rule::prefixed_name => {
                        datatype = Some(Box::new(build_term(p)?));
                    }
                    _ => {}
                }
            }

            Ok(Term::Literal(Literal::RdfString { lex, lang, datatype }))
        }
        Rule::iri => Ok(Term::Iri(strip_iri(pair.as_str()))),
        Rule::prefixed_name => {
            let s = pair.as_str();
            if s.ends_with(':') {
                Ok(Term::PrefixedName { prefix: Some(s[..s.len()-1].to_string()), local: None })
            } else if let Some((pfx, local)) = s.split_once(':') {
                Ok(Term::PrefixedName {
                    prefix: if pfx.is_empty() { None } else { Some(pfx.to_string()) },
                    local: Some(local.to_string()),
                })
            } else {
                Ok(Term::PrefixedName { prefix: None, local: Some(s.to_string()) })
            }
        }
        Rule::blank_node => Ok(Term::BlankNode(pair.into_inner().next().unwrap().as_str().to_string())),
        Rule::variable => Ok(Term::Variable(pair.into_inner().next().unwrap().as_str().to_string())),
        Rule::path => build_path(pair),
        r => Err(ParseError::Unexpected(r)),
    }
}

fn build_literal(pair: Pair<Rule>) -> Result<Term, ParseError> {
    let inner = pair.into_inner().next().unwrap();
    match inner.as_rule() {
        Rule::rdf_literal => build_term(inner),
        Rule::numeric_literal => build_numeric(inner),
        Rule::boolean_literal => build_term(inner),
        r => Err(ParseError::Unexpected(r)),
    }
}

fn build_numeric(pair: Pair<Rule>) -> Result<Term, ParseError> {
    match pair.as_rule() {
        Rule::numeric_literal => {
            // numeric_literal is a wrapper over INTEGER | DECIMAL | DOUBLE
            let inner = pair.into_inner().next().unwrap();
            build_numeric(inner)
        }
        Rule::INTEGER => Ok(Term::Literal(Literal::Integer(pair.as_str().to_string()))),
        Rule::DECIMAL => Ok(Term::Literal(Literal::Decimal(pair.as_str().to_string()))),
        Rule::DOUBLE  => Ok(Term::Literal(Literal::Double(pair.as_str().to_string()))),
        r => Err(ParseError::Unexpected(r)),
    }
}

fn strip_iri(s: &str) -> String {
    s.trim()
        .trim_start_matches('<')
        .trim_end_matches('>')
        .to_string()
}

fn unescape_string(s: &str) -> String {
    let raw = s.trim_matches('"').trim_matches('\'');
    raw.replace("\\n", "\n")
        .replace("\\t", "\t")
        .replace("\\r", "\r")
        .replace("\\\"", "\"")
        .replace("\\'", "'")
        .replace("\\\\", "\\")
}

