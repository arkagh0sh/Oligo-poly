//! Generators of equivariant ideals written as text.
//!
//! A generator is a line `description : polynomial`, such as
//! `x < y & y < z : x*y - z`. Its atoms are the variables of the line, in the
//! order of their first occurrence: first in the description, then in the
//! polynomial. The line stands for the orbit of the polynomial, where the tuple
//! of its atoms ranges over the orbit that the description defines. A line
//! without `:` is a polynomial with the description `true`.
//!
//! A variable that the description does not constrain makes the description
//! ambiguous, since such an atom may or may not be equal to another one. So a
//! misspelt variable is reported, as an ambiguous description.

use std::fmt::{self, Display, Formatter};
use crate::equivariant::PolynomialOrbit;
use crate::logic::{parse_description_implicit, show_formula, Description, Formula, ParseError, Signature};
use crate::mon::Polynomial;
use crate::parse::{parse_polynomial_in, polynomial_names, show_polynomial, Coefficient};
use crate::symbolic::{diagram, orbit_of, simplify, DescriptionError, SymbolicAtom, SymbolicOrbit, SymbolicTheory};

/// Why a line is not a generator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneratorError {
    /// The description cannot be parsed.
    Description(ParseError),
    /// The polynomial cannot be parsed.
    Polynomial(ParseError),
    /// No tuple of atoms satisfies the description.
    Inconsistent,
    /// The description allows several orbits; two of them, written as
    /// descriptions.
    Ambiguous(String, String),
}

impl Display for GeneratorError {
    fn fmt(&self, f : &mut Formatter<'_>) -> fmt::Result {
        match self {
            GeneratorError::Description(e) => write!(f, "in the description: {e}"),
            GeneratorError::Polynomial(e) => write!(f, "in the polynomial: {e}"),
            GeneratorError::Inconsistent => write!(f, "no atoms satisfy the description"),
            GeneratorError::Ambiguous(a, b) => {
                write!(f, "the description allows several orbits, for example `{a}` and `{b}`; add the missing relations")
            }
        }
    }
}

/// A conjunction written without outer parentheses.
fn show_conjunction(formula : &Formula, signature : &Signature, names : &[String]) -> String {
    match formula {
        Formula::And(v) if !v.is_empty() => {
            v.iter().map(|a| show_formula(a, signature, names)).collect::<Vec<_>>().join(" & ")
        }
        _ => show_formula(formula, signature, names),
    }
}

/// Parses a generator over the atoms of the theory `T`.
pub fn parse_generator<T : SymbolicTheory, F : Coefficient>(line : &str)
    -> Result<SymbolicOrbit<T, Polynomial<F, SymbolicAtom<T>>>, GeneratorError> {
    let signature = &T::theory().signature;
    let (description, polynomial) = match line.split_once(':') {
        Some((d, p)) if d.trim().is_empty() => ("true", p),
        Some((d, p)) => (d, p),
        None => ("true", line),
    };
    // Pad the polynomial, so that the positions of its errors count from the
    // start of the line.
    let offset = line.chars().count() - polynomial.chars().count();
    let polynomial = &format!("{}{polynomial}", " ".repeat(offset));
    let mut description = parse_description_implicit(description, signature).map_err(GeneratorError::Description)?;
    for name in polynomial_names(polynomial).map_err(GeneratorError::Polynomial)? {
        if signature.relation(&name).is_some() || signature.function(&name).is_some() {
            return Err(GeneratorError::Polynomial(ParseError(format!("{name} is a symbol of the theory, not a variable"))));
        }
        if !description.variables.contains(&name) {
            description.variables.push(name);
        }
    }
    let template = parse_polynomial_in::<F>(polynomial, &description.variables).map_err(GeneratorError::Polynomial)?;
    let show = |d : &Description| show_conjunction(&d.formula, signature, &d.variables);
    match orbit_of::<T>(&description) {
        Ok(orbit) => Ok(orbit.map(|t| template.map_variables(|&i| t[i].clone()))),
        Err(DescriptionError::InconsistentFormula) => Err(GeneratorError::Inconsistent),
        Err(DescriptionError::AmbiguousFormula(examples)) => {
            Err(GeneratorError::Ambiguous(show(&simplify::<T>(&examples.0)), show(&simplify::<T>(&examples.1))))
        }
    }
}

/// Writes an orbit of polynomials as a generator. Its atoms are the support of
/// the polynomial, named x1 < x2 < ... in increasing order, and its
/// description is the simplified diagram of this tuple. The result only
/// depends on the orbit.
pub fn show_generator<T : SymbolicTheory, F : Coefficient>(orbit : &PolynomialOrbit<F, SymbolicAtom<T>>) -> String {
    let signature = &T::theory().signature;
    orbit.evaluate(|p| {
        let support : Vec<SymbolicAtom<T>> = p.domain().into_iter().collect();
        let names : Vec<String> = (1..=support.len()).map(|i| format!("x{i}")).collect();
        let description = simplify::<T>(&Description { variables : names.clone(), formula : diagram(&support) });
        let name = |a : &SymbolicAtom<T>| names[support.iter().position(|b| b == a).unwrap()].clone();
        format!("{} : {}", show_conjunction(&description.formula, signature, &names), show_polynomial(p, name))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::equivariant::{equivariant_groebner_basis, minimal_basis, reduce_tails};
    use crate::symbolic::{DenseOrder, MeetTree};
    use num_rational::BigRational;

    type Q = BigRational;

    fn dense(line : &str) -> Result<PolynomialOrbit<Q, SymbolicAtom<DenseOrder>>, GeneratorError> {
        parse_generator::<DenseOrder, Q>(line)
    }

    fn tree(line : &str) -> Result<PolynomialOrbit<Q, SymbolicAtom<MeetTree>>, GeneratorError> {
        parse_generator::<MeetTree, Q>(line)
    }

    #[test]
    fn generators_and_their_orbits() {
        let g = dense("x < y & y < z : x*y - z").unwrap();
        assert!(dense("z > y & x < y : x y - z").unwrap() == g);
        assert!(dense("x < y & y < z : x*z - y").unwrap() != g);
        // Without a description, the polynomial must have one atom.
        assert!(dense("x^2 - x").is_ok());
        assert!(dense(": x^2 - x").unwrap() == dense("x^2 - x").unwrap());
        assert_eq!(show_generator(&dense("x^2 - x").unwrap()), "true : x1^2 - x1");
        // A constant has no atoms.
        assert_eq!(show_generator(&dense("3/2").unwrap()), "true : 3/2");
    }

    #[test]
    fn errors() {
        // z is not constrained: it may be equal to x or y, or lie elsewhere.
        assert!(matches!(dense("x < y : x*y - z"), Err(GeneratorError::Ambiguous(..))));
        assert!(matches!(dense("x*y"), Err(GeneratorError::Ambiguous(..))));
        assert_eq!(dense("x < y & y < x : x"), Err(GeneratorError::Inconsistent));
        assert!(matches!(dense("x << y : x"), Err(GeneratorError::Description(_))));
        assert!(matches!(dense("x < 2 : x"), Err(GeneratorError::Description(_))));
        let e = dense("x < y : x +").unwrap_err();
        assert_eq!(e.to_string(), "in the polynomial: at character 12: unexpected end of the polynomial");
        let e = tree("le(x, y) : x*meet").unwrap_err();
        assert_eq!(e.to_string(), "in the polynomial: meet is a symbol of the theory, not a variable");
        // The two examples of an ambiguous description are simplified.
        let GeneratorError::Ambiguous(a, b) = dense("x != y : x - y").unwrap_err() else { panic!() };
        let mut examples = [a, b];
        examples.sort();
        assert_eq!(examples, ["x < y", "y < x"]);
    }

    #[test]
    fn showing_and_parsing_agree() {
        for line in ["x < y & y < z : x*y - z", "y < x : 2x^2 - 1/3 y", "x < y & y < z : x - z"] {
            let o = dense(line).unwrap();
            assert!(dense(&show_generator(&o)).unwrap() == o, "{line}");
        }
        for line in ["le(x, y) & x != y : y - x", "x < y & !le(x, y) : x*y", "x < y & y < z & meet(y, z) = x : y*z - x"] {
            let o = tree(line).unwrap();
            let shown = show_generator(&o);
            assert!(tree(&shown).unwrap() == o, "{line} was shown as {shown}");
        }
        assert_eq!(show_generator(&dense("x < y & y < z : x*y - z").unwrap()), "x1 < x2 & x2 < x3 : -x3 + x1*x2");
    }

    /// The bases of the tests of `equivariant.rs`, written as generators.
    #[test]
    fn bases_as_text() {
        let show = |basis : &[PolynomialOrbit<Q, SymbolicAtom<DenseOrder>>]| -> Vec<String> {
            minimal_basis(basis.to_vec()).iter().map(show_generator).collect()
        };
        let basis = equivariant_groebner_basis(vec![dense("x < y & y < z : x*y - z").unwrap()], 50).ok().unwrap();
        let mut shown = show(&basis);
        shown.sort();
        assert_eq!(shown, ["true : x1^2 - x1", "x1 < x2 : x2 - x1"]);
        // For the squares, the generator x2 - x1^2 stays in the minimal basis;
        // its tail reduces to x1 by x1^2 - x1.
        let basis = minimal_basis(equivariant_groebner_basis(vec![dense("x < y : x^2 - y").unwrap()], 50).ok().unwrap());
        let mut shown : Vec<String> = basis.iter().map(show_generator).collect();
        shown.sort();
        assert_eq!(shown, ["true : x1^2 - x1", "x1 < x2 : x2 - x1^2"]);
        let mut shown : Vec<String> = reduce_tails(basis).iter().map(show_generator).collect();
        shown.sort();
        assert_eq!(shown, ["true : x1^2 - x1", "x1 < x2 : x2 - x1"]);
        let basis = equivariant_groebner_basis(vec![tree("le(x, y) & x != y : y - x").unwrap()], 50).ok().unwrap();
        let mut shown : Vec<String> = minimal_basis(basis).iter().map(show_generator).collect();
        shown.sort();
        // The second orbit is that of incomparable points: their meet is below x1.
        assert_eq!(shown, ["x1 < x2 & le(x1, x2) : x2 - x1", "x1 < x2 & meet(x1, x2) < x1 : x2 - x1"]);
    }
}
