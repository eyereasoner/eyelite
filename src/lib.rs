mod ast;
mod parser;
mod resolve;
mod reasoner;
mod normalize;

pub use ast::*;
pub use parser::{parse_document, ParseError};
pub use resolve::{PrefixEnv, RDF_TYPE, LOG_IMPLIES, LOG_IMPLIED_BY}; // optional
pub use reasoner::{
    extract,
    extract_queries,
    forward_chain,
    backward_solve,
    instantiate_pat,
    Atom,
    GTriple,
    RulePat,
    PT,
};
pub use normalize::normalize_implications;

