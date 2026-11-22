//! Signatures, terms and quantifier-free formulas, with a parser.
//!
//! A structure interprets equality `=` and the relation and function symbols of
//! its signature; a function symbol with no arguments is a constant. A linear
//! order is an ordinary binary relation symbol named `<`, present in the
//! signatures of ordered structures. A formula is quantifier free, and it is used in two
//! ways:
//!
//! - an [`Axiom`] is a formula whose variables are universally quantified; a
//!   [`Theory`] is a signature with axioms;
//! - a [`Description`] is a formula whose variables are atoms; it describes
//!   the orbit of the tuple of these atoms.
//!
//! Syntax of formulas, from the loosest to the tightest binding:
//!
//! - `A <-> B`, `A -> B` (to the right);
//! - `A | B`;
//! - `A & B`;
//! - `!A`, `(A)`, `true`, `false`, and the atoms:
//!   `s = t`, `s != t`, `R(t1, ..., tk)` for a relation symbol R, and, when the
//!   signature has the relation `<`, `s < t`, `s > t`, `s <= t` (meaning
//!   `s < t | s = t`) and `s >= t`.
//!
//! A term is a variable (an identifier that is not a symbol of the signature),
//! a constant `c`, or `f(t1, ..., tk)` for a function symbol f with k >= 1
//! arguments.

use std::collections::BTreeMap;
use std::fmt;

/// The relation and function symbols of a structure, with their arities.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Signature {
    pub relations : Vec<(String, usize)>,
    pub functions : Vec<(String, usize)>,
}

impl Signature {
    pub fn relation(&self, name : &str) -> Option<usize> {
        self.relations.iter().position(|(n, _)| n == name)
    }

    pub fn function(&self, name : &str) -> Option<usize> {
        self.functions.iter().position(|(n, _)| n == name)
    }
}

/// A term: a variable (by index) or a function symbol applied to terms.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Var(usize),
    App(usize, Vec<Term>),
}

/// A quantifier-free formula.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Formula {
    True,
    False,
    Eq(Term, Term),
    Rel(usize, Vec<Term>),
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
}

impl Formula {
    pub fn negate(f : Formula) -> Formula {
        Formula::Not(Box::new(f))
    }

    pub fn implies(a : Formula, b : Formula) -> Formula {
        Formula::Or(vec![Formula::negate(a), b])
    }

    /// Applies `f` to every term that occurs as an argument of an atom.
    pub fn map_terms(&self, f : &mut impl FnMut(&Term) -> Term) -> Formula {
        match self {
            Formula::True => Formula::True,
            Formula::False => Formula::False,
            Formula::Eq(s, t) => Formula::Eq(f(s), f(t)),
            Formula::Rel(r, ts) => Formula::Rel(*r, ts.iter().map(&mut *f).collect()),
            Formula::Not(a) => Formula::negate(a.map_terms(f)),
            Formula::And(v) => Formula::And(v.iter().map(|a| a.map_terms(f)).collect()),
            Formula::Or(v) => Formula::Or(v.iter().map(|a| a.map_terms(f)).collect()),
        }
    }

    /// Calls `f` on every term that occurs as an argument of an atom.
    pub fn for_each_term(&self, f : &mut impl FnMut(&Term)) {
        match self {
            Formula::True | Formula::False => {}
            Formula::Eq(s, t) => {
                f(s);
                f(t);
            }
            Formula::Rel(_, ts) => ts.iter().for_each(&mut *f),
            Formula::Not(a) => a.for_each_term(f),
            Formula::And(v) | Formula::Or(v) => v.iter().for_each(|a| a.for_each_term(f)),
        }
    }
}

/// A formula whose variables are universally quantified, with their names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Axiom {
    pub variables : Vec<String>,
    pub formula : Formula,
}

/// A formula whose variables are atoms, with their names: it describes the
/// orbit of the tuple of these atoms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Description {
    pub variables : Vec<String>,
    pub formula : Formula,
}

/// A signature with axioms: the finite structures of the signature that
/// satisfy the axioms are the finite substructures of the structure of the
/// atoms.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Theory {
    pub signature : Signature,
    pub axioms : Vec<Axiom>,
}

/// The axioms of a strict linear order `<`.
pub const LINEAR_ORDER : [&str; 3] = ["!(x < x)", "x < y & y < z -> x < z", "x < y | x = y | y < x"];

/// The axioms of finite meet-trees with a lexicographic order, besides those of
/// the linear order `<`: `le` is a partial order whose elements below any
/// element form a chain, `meet` is the greatest lower bound, and `<` satisfies
/// (L1) and (L2) of `README.tex`.
pub const TREE_AXIOMS : [&str; 10] = [
    "le(x, x)",
    "le(x, y) & le(y, x) -> x = y",
    "le(x, y) & le(y, z) -> le(x, z)",
    "le(y, x) & le(z, x) -> le(y, z) | le(z, y)",
    "le(meet(x, y), x)",
    "le(meet(x, y), y)",
    "le(z, x) & le(z, y) -> le(z, meet(x, y))",
    "le(x, y) -> x <= y",
    "le(x, y) & le(x, z) & y < w & w < z -> le(x, w)",
    "meet(x, y) = meet(y, x)",
];

impl Theory {
    /// The theory with the given signature and axioms, written as text.
    pub fn new(signature : Signature, axioms : &[&str]) -> Result<Theory, ParseError> {
        let axioms = axioms.iter().map(|a| parse_axiom(a, &signature)).collect::<Result<Vec<_>, _>>()?;
        Ok(Theory { signature, axioms })
    }
}

impl Signature {
    /// The signature with the given relation and function symbols and arities.
    pub fn new(relations : &[(&str, usize)], functions : &[(&str, usize)]) -> Signature {
        Signature {
            relations : relations.iter().map(|(n, k)| (n.to_string(), *k)).collect(),
            functions : functions.iter().map(|(n, k)| (n.to_string(), *k)).collect(),
        }
    }
}

/// An error of the parser, with a message.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError(pub String);

impl fmt::Display for ParseError {
    fn fmt(&self, f : &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Ident(String),
    LParen,
    RParen,
    Comma,
    Less,
    Greater,
    LessEq,
    GreaterEq,
    Equal,
    NotEqual,
    Not,
    And,
    Or,
    Implies,
    Iff,
}

fn tokenize(src : &str) -> Result<Vec<Token>, ParseError> {
    let chars : Vec<char> = src.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let next = chars.get(i + 1).copied();
        let next2 = chars.get(i + 2).copied();
        if c.is_whitespace() {
            i += 1;
        } else if c.is_alphanumeric() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            tokens.push(Token::Ident(chars[start..i].iter().collect()));
        } else {
            let (token, len) = match (c, next, next2) {
                ('<', Some('-'), Some('>')) => (Token::Iff, 3),
                ('-', Some('>'), _) => (Token::Implies, 2),
                ('<', Some('='), _) => (Token::LessEq, 2),
                ('>', Some('='), _) => (Token::GreaterEq, 2),
                ('!', Some('='), _) => (Token::NotEqual, 2),
                ('<', _, _) => (Token::Less, 1),
                ('>', _, _) => (Token::Greater, 1),
                ('=', _, _) => (Token::Equal, 1),
                ('!', _, _) => (Token::Not, 1),
                ('&', _, _) => (Token::And, 1),
                ('|', _, _) => (Token::Or, 1),
                ('(', _, _) => (Token::LParen, 1),
                (')', _, _) => (Token::RParen, 1),
                (',', _, _) => (Token::Comma, 1),
                _ => return Err(ParseError(format!("unexpected character '{c}'"))),
            };
            tokens.push(token);
            i += len;
        }
    }
    Ok(tokens)
}

struct Parser<'a> {
    tokens : Vec<Token>,
    pos : usize,
    signature : &'a Signature,
    variables : Vec<String>,
}

impl Parser<'_> {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn expect(&mut self, t : Token) -> Result<(), ParseError> {
        if self.peek() == Some(&t) {
            self.pos += 1;
            Ok(())
        } else {
            Err(ParseError(format!("expected {t:?}, found {:?}", self.peek())))
        }
    }

    fn formula(&mut self) -> Result<Formula, ParseError> {
        let a = self.disjunction()?;
        match self.peek() {
            Some(Token::Implies) => {
                self.pos += 1;
                Ok(Formula::implies(a, self.formula()?))
            }
            Some(Token::Iff) => {
                self.pos += 1;
                let b = self.disjunction()?;
                Ok(Formula::And(vec![Formula::implies(a.clone(), b.clone()), Formula::implies(b, a)]))
            }
            _ => Ok(a),
        }
    }

    fn disjunction(&mut self) -> Result<Formula, ParseError> {
        let mut parts = vec![self.conjunction()?];
        while self.peek() == Some(&Token::Or) {
            self.pos += 1;
            parts.push(self.conjunction()?);
        }
        Ok(if parts.len() == 1 { parts.pop().unwrap() } else { Formula::Or(parts) })
    }

    fn conjunction(&mut self) -> Result<Formula, ParseError> {
        let mut parts = vec![self.unary()?];
        while self.peek() == Some(&Token::And) {
            self.pos += 1;
            parts.push(self.unary()?);
        }
        Ok(if parts.len() == 1 { parts.pop().unwrap() } else { Formula::And(parts) })
    }

    fn unary(&mut self) -> Result<Formula, ParseError> {
        match self.peek().cloned() {
            Some(Token::Not) => {
                self.pos += 1;
                Ok(Formula::negate(self.unary()?))
            }
            Some(Token::LParen) => {
                self.pos += 1;
                let f = self.formula()?;
                self.expect(Token::RParen)?;
                Ok(f)
            }
            Some(Token::Ident(name)) if name == "true" => {
                self.pos += 1;
                Ok(Formula::True)
            }
            Some(Token::Ident(name)) if name == "false" => {
                self.pos += 1;
                Ok(Formula::False)
            }
            Some(Token::Ident(name)) if self.signature.relation(&name).is_some() => {
                let r = self.signature.relation(&name).unwrap();
                self.pos += 1;
                let args = self.arguments()?;
                let arity = self.signature.relations[r].1;
                if args.len() != arity {
                    return Err(ParseError(format!("the relation {name} has {arity} arguments, not {}", args.len())));
                }
                Ok(Formula::Rel(r, args))
            }
            _ => {
                let s = self.term()?;
                let op = self.peek().cloned();
                self.pos += 1;
                let t = self.term()?;
                let less = |a : Term, b : Term| -> Result<Formula, ParseError> {
                    match self.signature.relation("<") {
                        Some(r) => Ok(Formula::Rel(r, vec![a, b])),
                        None => Err(ParseError("this signature has no order <".to_string())),
                    }
                };
                match op {
                    Some(Token::Less) => less(s, t),
                    Some(Token::Greater) => less(t, s),
                    Some(Token::LessEq) => Ok(Formula::Or(vec![less(s.clone(), t.clone())?, Formula::Eq(s, t)])),
                    Some(Token::GreaterEq) => Ok(Formula::Or(vec![less(t.clone(), s.clone())?, Formula::Eq(s, t)])),
                    Some(Token::Equal) => Ok(Formula::Eq(s, t)),
                    Some(Token::NotEqual) => Ok(Formula::negate(Formula::Eq(s, t))),
                    other => Err(ParseError(format!("expected a comparison, found {other:?}"))),
                }
            }
        }
    }

    fn arguments(&mut self) -> Result<Vec<Term>, ParseError> {
        self.expect(Token::LParen)?;
        let mut args = vec![self.term()?];
        while self.peek() == Some(&Token::Comma) {
            self.pos += 1;
            args.push(self.term()?);
        }
        self.expect(Token::RParen)?;
        Ok(args)
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        match self.peek().cloned() {
            Some(Token::Ident(name)) => {
                self.pos += 1;
                if let Some(f) = self.signature.function(&name) {
                    let arity = self.signature.functions[f].1;
                    if arity == 0 {
                        return Ok(Term::App(f, Vec::new()));
                    }
                    let args = self.arguments()?;
                    if args.len() != arity {
                        return Err(ParseError(format!("the function {name} has {arity} arguments, not {}", args.len())));
                    }
                    Ok(Term::App(f, args))
                } else if self.signature.relation(&name).is_some() {
                    Err(ParseError(format!("the relation {name} is used as a term")))
                } else {
                    let i = match self.variables.iter().position(|v| *v == name) {
                        Some(i) => i,
                        None => {
                            self.variables.push(name);
                            self.variables.len() - 1
                        }
                    };
                    Ok(Term::Var(i))
                }
            }
            other => Err(ParseError(format!("expected a term, found {other:?}"))),
        }
    }
}

/// Parses a formula over `signature`. The variables are numbered in the order
/// of their first occurrence, after the given `variables`.
fn parse(src : &str, signature : &Signature, variables : &[String]) -> Result<(Vec<String>, Formula), ParseError> {
    let mut parser = Parser { tokens : tokenize(src)?, pos : 0, signature, variables : variables.to_vec() };
    let formula = parser.formula()?;
    if parser.pos != parser.tokens.len() {
        return Err(ParseError(format!("unexpected {:?} after the formula", parser.tokens[parser.pos])));
    }
    Ok((parser.variables, formula))
}

/// Parses an axiom over `signature`. Its variables are numbered in the order of
/// their first occurrence.
pub fn parse_axiom(src : &str, signature : &Signature) -> Result<Axiom, ParseError> {
    let (variables, formula) = parse(src, signature, &[])?;
    Ok(Axiom { variables, formula })
}

/// Parses a description over `signature` whose variables are the given
/// `atoms`, numbered in this order. A variable that is not one of the `atoms`
/// is an error, so that a misspelt atom is not taken for a new one.
pub fn parse_description(src : &str, signature : &Signature, atoms : &[String]) -> Result<Description, ParseError> {
    let (variables, formula) = parse(src, signature, atoms)?;
    if let Some(unknown) = variables.get(atoms.len()) {
        return Err(ParseError(format!("{unknown} is not a declared atom")));
    }
    Ok(Description { variables, formula })
}

/// Writes a term with the names of the variables and symbols.
pub fn show_term(t : &Term, signature : &Signature, names : &[String]) -> String {
    match t {
        Term::Var(i) => names.get(*i).cloned().unwrap_or_else(|| format!("v{i}")),
        Term::App(f, args) if args.is_empty() => signature.functions[*f].0.clone(),
        Term::App(f, args) => {
            let args : Vec<String> = args.iter().map(|a| show_term(a, signature, names)).collect();
            format!("{}({})", signature.functions[*f].0, args.join(", "))
        }
    }
}

/// Writes a formula with the names of the variables and symbols.
pub fn show_formula(f : &Formula, signature : &Signature, names : &[String]) -> String {
    let t = |t : &Term| show_term(t, signature, names);
    match f {
        Formula::True => "true".to_string(),
        Formula::False => "false".to_string(),
        Formula::Eq(a, b) => format!("{} = {}", t(a), t(b)),
        Formula::Rel(r, args) if signature.relations[*r].0 == "<" => format!("{} < {}", t(&args[0]), t(&args[1])),
        Formula::Rel(r, args) => format!("{}({})", signature.relations[*r].0, args.iter().map(t).collect::<Vec<_>>().join(", ")),
        Formula::Not(a) => match a.as_ref() {
            Formula::Eq(x, y) => format!("{} != {}", t(x), t(y)),
            _ => format!("!{}", show_formula(a, signature, names)),
        },
        Formula::And(v) => format!("({})", v.iter().map(|a| show_formula(a, signature, names)).collect::<Vec<_>>().join(" & ")),
        Formula::Or(v) => format!("({})", v.iter().map(|a| show_formula(a, signature, names)).collect::<Vec<_>>().join(" | ")),
    }
}

/// The subterms of a term that are function applications, innermost first.
pub fn applications(t : &Term, out : &mut Vec<Term>) {
    if let Term::App(_, args) = t {
        for a in args {
            applications(a, out);
        }
        if !out.contains(t) {
            out.push(t.clone());
        }
    }
}

/// A map from the applications of a formula to new variables, numbered from
/// `first`, innermost first: the flattening used to ground axioms.
pub fn flatten(f : &Formula, first : usize) -> (Formula, Vec<(usize, Vec<usize>, usize)>) {
    let mut apps = Vec::new();
    f.for_each_term(&mut |t| applications(t, &mut apps));
    let mut index : BTreeMap<Term, usize> = BTreeMap::new();
    let mut definitions = Vec::new();
    for app in &apps {
        if let Term::App(g, args) = app {
            let args : Vec<usize> = args
                .iter()
                .map(|a| match a {
                    Term::Var(v) => *v,
                    app => index[app],
                })
                .collect();
            let v = first + definitions.len();
            definitions.push((*g, args, v));
            index.insert(app.clone(), v);
        }
    }
    let flat = f.map_terms(&mut |t| match t {
        Term::Var(v) => Term::Var(*v),
        app => Term::Var(index[app]),
    });
    (flat, definitions)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tree_signature() -> Signature {
        Signature { relations : vec![("<".to_string(), 2), ("le".to_string(), 2)], functions : vec![("meet".to_string(), 2)] }
    }

    #[test]
    fn parse_and_flatten() {
        let s = tree_signature();
        let a = parse_axiom("le(z, x) & le(z, y) -> le(z, meet(x, y))", &s).unwrap();
        assert_eq!(a.variables, vec!["z", "x", "y"]);
        let (flat, defs) = flatten(&a.formula, 3);
        assert_eq!(defs, vec![(0, vec![1, 2], 3)]);
        assert_eq!(show_formula(&flat, &s, &["z".into(), "x".into(), "y".into(), "u".into()]), "(!(le(z, x) & le(z, y)) | le(z, u))");
        let b = parse_axiom("meet(meet(x, y), z) <= x", &s).unwrap();
        let (_, defs) = flatten(&b.formula, 3);
        assert_eq!(defs, vec![(0, vec![0, 1], 3), (0, vec![3, 2], 4)]);
        assert!(parse_axiom("le(x)", &s).is_err());
        assert!(parse_axiom("x < ", &s).is_err());
        assert!(parse_axiom("x # y", &s).is_err());
    }

    #[test]
    fn descriptions_and_constants() {
        let s = tree_signature();
        let atoms : Vec<String> = ["a", "b", "m"].iter().map(|x| x.to_string()).collect();
        let d = parse_description("m = meet(a, b) & a < b & !le(a, b)", &s, &atoms).unwrap();
        assert_eq!(d.variables, atoms);
        assert_eq!(show_formula(&d.formula, &s, &atoms), "(m = meet(a, b) & a < b & !le(a, b))");
        // A misspelt atom is an error.
        assert!(parse_description("a < c", &s, &atoms).is_err());
        // Constants are written without parentheses.
        let c = Signature { relations : vec![("<".to_string(), 2)], functions : vec![("zero".to_string(), 0)] };
        let e = parse_axiom("zero <= x", &c).unwrap();
        assert_eq!(e.variables, vec!["x"]);
        assert_eq!(show_formula(&e.formula, &c, &e.variables), "(zero < x | zero = x)");
        // Without the relation <, the order cannot be used.
        let unordered = Signature { relations : vec![("E".to_string(), 2)], functions : vec![] };
        assert!(parse_axiom("x < y", &unordered).is_err());
        assert!(parse_axiom("E(x, y) -> E(y, x)", &unordered).is_ok());
    }
}
