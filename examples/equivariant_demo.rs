//! Runs the equivariant Buchberger algorithm on small equivariant ideals of
//! polynomials whose variables are atoms of (Q, <), with rational coefficients.
//!
//! Usage: `cargo run --release --features equivariant --example equivariant_demo`

use atomic_hilbert::atoms::Orbit;
use atomic_hilbert::dlo::DLO;
use atomic_hilbert::equivariant::{equivariant_buchberger, minimal_basis, PolynomialOrbit};
use atomic_hilbert::mon::Polynomial;
use num_rational::BigRational;
use num_traits::Pow;
use rug::Rational;
use std::time::Instant;

type P = Polynomial<BigRational, DLO>;

fn x(i : i64) -> P {
    Polynomial::var(DLO::new(Rational::from(i)))
}

fn c(k : i64) -> P {
    Polynomial::constant(BigRational::from_integer(k.into()))
}

fn run(name : &str, generators : Vec<P>) {
    println!("{name}");
    for g in &generators {
        println!("  generator: orbit of {g}");
    }
    let start = Instant::now();
    let orbits : Vec<PolynomialOrbit<BigRational, DLO>> = generators.into_iter().map(Orbit::new).collect();
    match equivariant_buchberger(orbits, 200) {
        Ok(basis) => {
            println!("  {} orbits computed in {:.2?}; minimal basis:", basis.len(), start.elapsed());
            for g in minimal_basis(basis) {
                println!("    {g}");
            }
        }
        Err(partial) => println!("  stopped after {} orbits ({:.2?})", partial.len(), start.elapsed()),
    }
}

fn main() {
    run("J0 = <x_a - 1>", vec![x(1) - c(1)]);
    run("<x_a x_b : a < b>", vec![x(1) * x(2)]);
    run("<x_a - x_b : a < b>", vec![x(1) - x(2)]);
    run("<x_a^2 - x_b : a < b>", vec![x(1).pow(2u8) - x(2)]);
    run("<x_b - x_a : a < b> + <x_a^2 - 1>", vec![x(2) - x(1), x(1).pow(2u8) - c(1)]);
    run("<x_a x_b - x_c : a < b < c>", vec![x(1) * x(2) - x(3)]);
}
