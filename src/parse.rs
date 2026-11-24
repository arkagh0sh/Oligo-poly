//! A parser and a printer for polynomials.
//!
//! Syntax, from the loosest to the tightest binding:
//!
//! - `p + q`, `p - q`;
//! - `p * q`, `p / c`, and `p q` (implicit multiplication) when q starts with a
//!   variable or a parenthesis, as in `2x`, `x y` and `2(x + 1)`;
//! - `-p` and `+p`;
//! - `p^n` for a natural number n;
//! - numbers such as `3` and `0.25`, variables, and `(p)`.
//!
//! A divisor must be a non-zero constant, so `x / 2` is allowed but not
//! `1 / x`. A fraction is written as a division: `3/2 x` is (3/2) x.

use std::fmt::Display;
use std::hash::Hash;
use std::ops::{AddAssign, Div, Mul, Neg};
use num_rational::{BigRational, Rational64};
use num_traits::{ConstOne, One, Pow, Zero};
use crate::logic::ParseError;
use crate::mon::{Exponent, Monomial, Polynomial};

/// The coefficients that polynomials may have when they are parsed.
pub trait Coefficient :
    AddAssign + Clone + ConstOne + Default + Zero + Eq + Ord + Display
    + Mul<Output = Self> + Div<Output = Self> + Neg<Output = Self>
{
    /// The number written with the digits `integer`, a point, and the digits
    /// `fraction`, if it is an element of the field.
    fn from_decimal(integer : &str, fraction : &str) -> Option<Self>;
}

/// Rationals: the decimal d.f is the fraction df / 10^|f|. A literal that does
/// not fit in the type gives `None`.
macro_rules! rational_coefficient {
    ($t : ty) => {
        impl Coefficient for $t {
            fn from_decimal(integer : &str, fraction : &str) -> Option<Self> {
                format!("{integer}{fraction}/1{}", "0".repeat(fraction.len())).parse().ok()
            }
        }
    };
}

rational_coefficient!(BigRational);
rational_coefficient!(Rational64);

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Number(String, String),
    Ident(String),
    Plus,
    Minus,
    Times,
    Divide,
    Power,
    LParen,
    RParen,
}

/// The tokens of `src`, each with the position (counted in characters, from 1)
/// of its first character.
fn tokenize(src : &str) -> Result<Vec<(Token, usize)>, ParseError> {
    let chars : Vec<char> = src.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        let start = i;
        let digits = |i : &mut usize| -> String {
            let begin = *i;
            while *i < chars.len() && chars[*i].is_ascii_digit() {
                *i += 1;
            }
            chars[begin..*i].iter().collect()
        };
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        let token = if c.is_ascii_digit() || (c == '.' && chars.get(i + 1).is_some_and(|d| d.is_ascii_digit())) {
            let integer = digits(&mut i);
            let fraction = if i < chars.len() && chars[i] == '.' {
                i += 1;
                digits(&mut i)
            } else {
                String::new()
            };
            Token::Number(integer, fraction)
        } else if c.is_alphabetic() || c == '_' {
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            Token::Ident(chars[start..i].iter().collect())
        } else {
            i += 1;
            match c {
                '+' => Token::Plus,
                '-' => Token::Minus,
                '*' => Token::Times,
                '/' => Token::Divide,
                '^' => Token::Power,
                '(' => Token::LParen,
                ')' => Token::RParen,
                _ => return Err(ParseError(format!("at character {}: unexpected `{c}`", start + 1))),
            }
        };
        tokens.push((token, start + 1));
    }
    Ok(tokens)
}

struct Parser<'a, X> {
    tokens : Vec<(Token, usize)>,
    pos : usize,
    end : usize,
    variable : &'a dyn Fn(&str) -> Option<X>,
}

impl<X : Clone + Ord + Hash> Parser<'_, X> {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos).map(|(t, _)| t)
    }

    /// The position of the next token, or of the end of the input.
    fn here(&self) -> usize {
        self.tokens.get(self.pos).map_or(self.end, |(_, p)| *p)
    }

    fn error<T>(&self, message : &str) -> Result<T, ParseError> {
        Err(ParseError(format!("at character {}: {message}", self.here())))
    }

    fn sum<F : Coefficient>(&mut self) -> Result<Polynomial<F, X>, ParseError> {
        let mut p = self.product()?;
        loop {
            match self.peek() {
                Some(Token::Plus) => {
                    self.pos += 1;
                    p = p + self.product()?;
                }
                Some(Token::Minus) => {
                    self.pos += 1;
                    p = p - self.product()?;
                }
                _ => return Ok(p),
            }
        }
    }

    fn product<F : Coefficient>(&mut self) -> Result<Polynomial<F, X>, ParseError> {
        let mut p = self.unary()?;
        loop {
            match self.peek() {
                Some(Token::Times) => {
                    self.pos += 1;
                    p = p * self.unary()?;
                }
                Some(Token::Divide) => {
                    self.pos += 1;
                    let at = self.here();
                    let divisor : Polynomial<F, X> = self.unary()?;
                    if !divisor.domain().is_empty() {
                        return Err(ParseError(format!("at character {at}: the divisor must be a constant")));
                    }
                    if divisor.is_zero() {
                        return Err(ParseError(format!("at character {at}: division by zero")));
                    }
                    let c = divisor.coeff_of(&Monomial::one());
                    p = p * Polynomial::constant(F::one() / c);
                }
                Some(Token::Ident(_)) | Some(Token::LParen) => p = p * self.power()?,
                _ => return Ok(p),
            }
        }
    }

    fn unary<F : Coefficient>(&mut self) -> Result<Polynomial<F, X>, ParseError> {
        match self.peek() {
            Some(Token::Minus) => {
                self.pos += 1;
                Ok(-self.unary()?)
            }
            Some(Token::Plus) => {
                self.pos += 1;
                self.unary()
            }
            _ => self.power(),
        }
    }

    fn power<F : Coefficient>(&mut self) -> Result<Polynomial<F, X>, ParseError> {
        let base = self.atom()?;
        if self.peek() != Some(&Token::Power) {
            return Ok(base);
        }
        self.pos += 1;
        match self.peek().cloned() {
            Some(Token::Number(integer, fraction)) if fraction.is_empty() => {
                let Ok(n) = integer.parse::<Exponent>() else {
                    return self.error("the exponent is too large");
                };
                self.pos += 1;
                Ok(base.pow(n))
            }
            _ => self.error("the exponent must be a natural number"),
        }
    }

    fn atom<F : Coefficient>(&mut self) -> Result<Polynomial<F, X>, ParseError> {
        match self.peek().cloned() {
            Some(Token::Number(integer, fraction)) => match F::from_decimal(&integer, &fraction) {
                Some(c) => {
                    self.pos += 1;
                    Ok(Polynomial::constant(c))
                }
                None => self.error("the number is not a coefficient of this field"),
            },
            Some(Token::Ident(name)) => match (self.variable)(&name) {
                Some(x) => {
                    self.pos += 1;
                    Ok(Polynomial::var(x))
                }
                None => self.error(&format!("unknown variable `{name}`")),
            },
            Some(Token::LParen) => {
                self.pos += 1;
                let p = self.sum()?;
                if self.peek() != Some(&Token::RParen) {
                    return self.error("expected `)`");
                }
                self.pos += 1;
                Ok(p)
            }
            Some(_) => self.error("expected a number, a variable or `(`"),
            None => self.error("unexpected end of the polynomial"),
        }
    }
}

/// Parses a polynomial. The function `variable` gives the variable named by an
/// identifier, or `None` if the identifier is not a variable.
pub fn parse_polynomial<F : Coefficient, X : Clone + Ord + Hash>(
    src : &str,
    variable : impl Fn(&str) -> Option<X>,
) -> Result<Polynomial<F, X>, ParseError> {
    let mut parser = Parser { tokens : tokenize(src)?, pos : 0, end : src.chars().count() + 1, variable : &variable };
    let p = parser.sum()?;
    if parser.pos < parser.tokens.len() {
        return parser.error("expected an operator");
    }
    Ok(p)
}

/// The names of a polynomial, in the order of their first occurrence.
pub fn polynomial_names(src : &str) -> Result<Vec<String>, ParseError> {
    let mut names : Vec<String> = Vec::new();
    for (token, _) in tokenize(src)? {
        if let Token::Ident(name) = token
            && !names.contains(&name)
        {
            names.push(name);
        }
    }
    Ok(names)
}

/// Parses a polynomial in the variables `variables`, numbered from 0.
pub fn parse_polynomial_in<F : Coefficient>(src : &str, variables : &[String]) -> Result<Polynomial<F, usize>, ParseError> {
    parse_polynomial(src, |name| variables.iter().position(|v| v == name))
}

/// Writes a polynomial in the syntax of `parse_polynomial`, from the largest
/// monomial to the smallest, with the names that `name` gives the variables.
pub fn show_polynomial<F : Coefficient, X : Clone + Ord + Hash>(p : &Polynomial<F, X>, name : impl Fn(&X) -> String) -> String {
    let mut out = String::new();
    for m in p.monomials().rev() {
        let c = p.coeff_of(m);
        let negative = c < F::zero();
        let c = if negative { -c } else { c };
        out.push_str(match (out.is_empty(), negative) {
            (true, false) => "",
            (true, true) => "-",
            (false, false) => " + ",
            (false, true) => " - ",
        });
        let factors : Vec<String> = m
            .exponents()
            .map(|(x, e)| if e == 1 { name(x) } else { format!("{}^{e}", name(x)) })
            .collect();
        if factors.is_empty() {
            out.push_str(&c.to_string());
        } else {
            if !c.is_one() {
                out.push_str(&format!("{c}*"));
            }
            out.push_str(&factors.join("*"));
        }
    }
    if out.is_empty() {
        out.push('0');
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    type P = Polynomial<BigRational, usize>;

    fn names() -> Vec<String> {
        ["x", "y", "z"].iter().map(|s| s.to_string()).collect()
    }

    fn parse(src : &str) -> P {
        parse_polynomial_in(src, &names()).unwrap()
    }

    fn error(src : &str) -> String {
        parse_polynomial_in::<BigRational>(src, &names()).unwrap_err().0
    }

    fn q(n : i64, d : i64) -> P {
        Polynomial::constant(BigRational::new(n.into(), d.into()))
    }

    fn v(i : usize) -> P {
        Polynomial::var(i)
    }

    #[test]
    fn parses_the_operations() {
        assert_eq!(parse("x*y - z"), v(0) * v(1) - v(2));
        assert_eq!(parse("-x^2 + 3/2 y"), -(v(0) * v(0)) + q(3, 2) * v(1));
        assert_eq!(parse("(x + 1)^2"), v(0) * v(0) + q(2, 1) * v(0) + q(1, 1));
        assert_eq!(parse("2x(y - 1)"), q(2, 1) * v(0) * (v(1) - q(1, 1)));
        assert_eq!(parse("x y z"), v(0) * v(1) * v(2));
        assert_eq!(parse("0.25 x + .5"), q(1, 4) * v(0) + q(1, 2));
        assert_eq!(parse("x / 2 - x/2"), Polynomial::zero());
        assert_eq!(parse("x*-y"), -(v(0) * v(1)));
        assert_eq!(parse("2^3 x^0"), q(8, 1));
        assert_eq!(parse("  0 "), Polynomial::zero());
    }

    #[test]
    fn reports_errors() {
        assert_eq!(error("x + w"), "at character 5: unknown variable `w`");
        assert_eq!(error("x +"), "at character 4: unexpected end of the polynomial");
        assert_eq!(error("(x + y"), "at character 7: expected `)`");
        assert_eq!(error("x / y"), "at character 5: the divisor must be a constant");
        assert_eq!(error("x / (1 - 1)"), "at character 5: division by zero");
        assert_eq!(error("x^y"), "at character 3: the exponent must be a natural number");
        assert_eq!(error("x^1.5"), "at character 3: the exponent must be a natural number");
        assert_eq!(error("x 2"), "at character 3: expected an operator");
        assert_eq!(error("x # y"), "at character 3: unexpected `#`");
        assert_eq!(error(""), "at character 1: unexpected end of the polynomial");
        // The number does not fit in a 64-bit rational.
        let big = parse_polynomial_in::<Rational64>("12345678901234567890 x", &names()).unwrap_err().0;
        assert_eq!(big, "at character 1: the number is not a coefficient of this field");
    }

    #[test]
    fn printing_and_parsing_agree() {
        let name = |i : &usize| names()[*i].clone();
        for src in ["x*y - z", "-x^2 + 3/2 y - 7/3", "(x - 2y + z/5)^3", "0", "-1", "x - 1/2"] {
            let p = parse(src);
            let shown = show_polynomial(&p, name);
            assert_eq!(parse(&shown), p, "{src} was shown as {shown}");
        }
        // The monomials are written in decreasing order: z > x y in the order of the library.
        assert_eq!(show_polynomial(&parse("x*y - z + 1/2"), name), "-z + x*y + 1/2");
        assert_eq!(show_polynomial(&parse("-2x^2 y"), name), "-2*x^2*y");
    }
}
