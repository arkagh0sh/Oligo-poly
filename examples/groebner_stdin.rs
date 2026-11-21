//! Reads polynomials from standard input and prints a Gröbner basis of the
//! ideal that they generate, for the monomial order used in `mon.rs`
//! (lexicographic, where a larger variable name is more significant).
//!
//! Usage: `cargo run --release --example groebner_stdin -- [f2|q] < input`
//!
//! Input: polynomials separated by `;` or by new lines. A polynomial is a sum of
//! terms separated by `+`, and a term is a product of factors separated by `*`.
//! A factor is a coefficient (an integer, or over Q a fraction such as `-3/2`)
//! or a variable with an optional exponent (such as `x` or `x^3`).
//! Output: one polynomial per line.

use atomic_hilbert::bits::F2;
use atomic_hilbert::ideal::buchberger;
use atomic_hilbert::mon::Polynomial;
use num_rational::BigRational;
use num_traits::{ConstOne, One, Pow, Zero};
use std::io::Read;
use std::ops::AddAssign;

fn parse<F>(src : &str, coeff : impl Fn(&str) -> F) -> Polynomial<F, String>
where
    F : AddAssign + Default + Eq + Zero + ConstOne + Clone,
{
    let mut acc : Polynomial<F, String> = Polynomial::zero();
    for term in src.split('+').map(str::trim).filter(|t| !t.is_empty()) {
        let mut t : Polynomial<F, String> = Polynomial::constant(F::one());
        for factor in term.split('*').map(str::trim) {
            let first = factor.chars().next().expect("empty factor");
            if first.is_ascii_digit() || first == '-' {
                t = t * Polynomial::constant(coeff(factor));
            } else {
                let mut it = factor.split('^');
                let name = it.next().unwrap().trim().to_string();
                let e : u32 = it.next().map(|e| e.trim().parse().expect("bad exponent")).unwrap_or(1);
                t = t * Polynomial::var(name).pow(e);
            }
        }
        acc = acc + t;
    }
    acc
}

fn parse_f2(c : &str) -> F2 {
    let n : i64 = c.parse().expect("over F2, coefficients must be integers");
    F2(n.rem_euclid(2) == 1)
}

fn parse_q(c : &str) -> BigRational {
    c.parse().expect("bad rational coefficient")
}

fn main() {
    let field = std::env::args().nth(1).unwrap_or_else(|| "q".to_string());
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input).expect("cannot read standard input");
    let sources : Vec<&str> = input
        .split(|c| c == ';' || c == '\n')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .collect();
    match field.as_str() {
        "f2" => {
            let polys = sources.iter().map(|s| parse(s, parse_f2)).collect();
            for p in buchberger(polys) {
                println!("{}", p);
            }
        }
        "q" => {
            let polys = sources.iter().map(|s| parse(s, parse_q)).collect();
            for p in buchberger(polys) {
                println!("{}", p);
            }
        }
        other => {
            eprintln!("unknown field {other}; use f2 or q");
            std::process::exit(2);
        }
    }
}
