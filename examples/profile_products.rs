//! Runs one example of the web page, for profiling: the colouring algorithm on
//! the orbit of x_a x_b - x_c with a < b < c, over the symbolic atoms of (Q, <).
use atomic_hilbert::equivariant::{equivariant_groebner_basis, minimal_basis};
use atomic_hilbert::generator::{parse_generator, show_generator};
use atomic_hilbert::symbolic::DenseOrder;
use num_rational::BigRational;

fn main() {
    let generator = parse_generator::<DenseOrder, BigRational>("x < y & y < z : x*y - z").unwrap();
    let start = std::time::Instant::now();
    let basis = equivariant_groebner_basis(vec![generator], 200).ok().unwrap();
    println!("{} orbits in {:.2} s", basis.len(), start.elapsed().as_secs_f64());
    for orbit in minimal_basis(basis) {
        println!("{}", show_generator(&orbit));
    }
}
