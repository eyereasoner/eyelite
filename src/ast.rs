use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct Document {
    pub directives: Vec<Directive>,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Directive {
    Prefix { prefix: String, iri: String },
    Base { iri: String },
}

#[derive(Debug, Clone, PartialEq)]
pub enum Statement {
    Triple(Triple),
    Implication { premise: Formula, conclusion: Formula, direction: ImplicationDir },
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImplicationDir {
    Forward,  // =>
    Backward, // <=
}

#[derive(Debug, Clone, PartialEq)]
pub struct Triple {
    pub subject: Term,
    pub predicate: Predicate,
    pub object: Term,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Predicate {
    Normal(Term),
    Inverse(Term), // <- P
    Has(Term),     // has P
    KeywordA,
    KeywordEquals,
    KeywordImplies,
    KeywordImpliedBy,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    Iri(String),
    PrefixedName { prefix: Option<String>, local: Option<String> },
    BlankNode(String),
    Variable(String),
    Literal(Literal),
    Collection(Vec<Term>),
    BlankNodePropertyList(Vec<(Predicate, Vec<Term>)>),
    Formula(Formula),
    Path(Path),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Formula {
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Path {
    pub head: Box<Term>,
    pub steps: Vec<(PathDir, Term)>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PathDir {
    Forward, // !
    Reverse, // ^
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    RdfString {
        lex: String,
        lang: Option<String>,
        datatype: Option<Box<Term>>,
    },
    Integer(String),
    Decimal(String),
    Double(String),
    Boolean(bool),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

