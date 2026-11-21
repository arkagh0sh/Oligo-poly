//! Runs the equivariant Buchberger algorithm on small equivariant ideals of
//! polynomials whose variables are atoms of (Q, <) or of the dense meet-tree
//! T_<, with rational coefficients. For each ideal, it compares the weak basis
//! of `equivariant_buchberger` with the equivariant Gröbner basis of
//! `equivariant_groebner_basis`.
//!
//! Usage: `cargo run --release --features equivariant --example equivariant_demo`

use atomic_hilbert::atoms::{AtomsWithOrd, Orbit};
use atomic_hilbert::dlo::DLO;
use atomic_hilbert::equivariant::{equivariant_buchberger, equivariant_groebner_basis, minimal_basis, OrbitList};
use atomic_hilbert::mon::Polynomial;
use atomic_hilbert::tree::Tree;
use num_rational::BigRational;
use num_traits::Pow;
use rug::Rational;
use std::fmt::Display;
use std::time::Instant;

fn c<A : AtomsWithOrd>(k : i64) -> Polynomial<BigRational, A> {
    Polynomial::constant(BigRational::from_integer(k.into()))
}

/// The variable of the atom i of (Q, <).
fn x(i : i64) -> Polynomial<BigRational, DLO> {
    Polynomial::var(DLO::new(Rational::from(i)))
}

/// The variable of the point of T_< given by a sequence (see `src/tree.rs`).
fn y(seq : &[i64]) -> Polynomial<BigRational, Tree> {
    Polynomial::var(Tree::from_ints(seq))
}

fn run<A : AtomsWithOrd + Display>(name : &str, generators : Vec<Polynomial<BigRational, A>>) {
    println!("{name}");
    for g in &generators {
        println!("  generator: orbit of {g}");
    }
    let orbits : OrbitList<BigRational, A> = generators.into_iter().map(Orbit::new).collect();
    for strong in [false, true] {
        let start = Instant::now();
        let (label, result) = if strong {
            ("equivariant Groebner basis (equivariant_groebner_basis)", equivariant_groebner_basis(orbits.clone(), 500))
        } else {
            ("weak basis (equivariant_buchberger)", equivariant_buchberger(orbits.clone(), 500))
        };
        match result {
            Ok(basis) => {
                println!("  {label}: {} orbits in {:.2?}; minimal basis:", basis.len(), start.elapsed());
                for g in minimal_basis(basis) {
                    println!("    {g}");
                }
            }
            Err(partial) => println!("  {label}: stopped after {} orbits ({:.2?})", partial.len(), start.elapsed()),
        }
    }
}

fn main() {
    println!("Atoms of (Q, <)\n");
    run("J0 = <x_a - 1>", vec![x(1) - c(1)]);
    run("<x_a x_b : a < b>", vec![x(1) * x(2)]);
    run("<x_a - x_b : a < b>", vec![x(1) - x(2)]);
    run("<x_a^2 - x_b : a < b>", vec![x(1).pow(2u8) - x(2)]);
    run("<x_b - x_a : a < b> + <x_a^2 - 1>", vec![x(2) - x(1), x(1).pow(2u8) - c(1)]);
    run("<x_a x_b - x_c : a < b < c>", vec![x(1) * x(2) - x(3)]);
    println!("\nPoints of the dense meet-tree T_< (a < b is the tree order)\n");
    run("<x_a - 1>", vec![y(&[0]) - c(1)]);
    run("<x_a - x_b : a < b>", vec![y(&[1]) - y(&[0])]);
    run("<x_a - x_b : a, b incomparable>", vec![y(&[1]) - y(&[0, -1, 0])]);
    run("<x_a^2 - x_b : a < b>", vec![y(&[0]).pow(2u8) - y(&[1])]);
}
