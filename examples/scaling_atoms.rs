//! Concrete atoms (DLO, Tree) against symbolic atoms (DenseOrder, MeetTree)
//! for larger tuples. Usage:
//!   scaling_atoms product <dense-chain|tree-chain|tree-comb> <n> <concrete|symbolic>
//!   scaling_atoms basis <dense|tree> <k> <concrete|symbolic> <colouring|one-colour> [default|domain|plain]
use std::collections::BTreeSet;
use std::time::Instant;
use atomic_hilbert::atoms::{diagram, AtomsWithOrd, Orbit, Structure};
use atomic_hilbert::dlo::DLO;
use atomic_hilbert::equivariant::{equivariant_groebner_basis_with, one_colour_groebner_basis_with, OrbitList, Options, Selection};
use atomic_hilbert::logic::Description;
use atomic_hilbert::mon::Polynomial;
use atomic_hilbert::symbolic::{orbit_of, DenseOrder, MeetTree, SymbolicAtom, SymbolicTheory};
use atomic_hilbert::tree::Tree;
use num_rational::BigRational as Q;
use num_traits::One;

fn dense_chain(n : usize) -> Vec<DLO> {
    (0..n as i64).map(DLO::from_int).collect()
}

fn tree_chain(n : usize) -> Vec<Tree> {
    (0..n as i64).map(|i| Tree::from_ints(&[i])).collect()
}

/// Pairwise incomparable points, branching off the trunk at heights 0, 1, ...
fn tree_comb(n : usize) -> Vec<Tree> {
    (0..n as i64).map(|i| Tree::from_ints(&[i, 1, 1])).collect()
}

/// The tuple of symbolic atoms in the orbit of a concrete tuple: the theories
/// have the same signature, so the diagram of the concrete tuple describes it.
fn symbolic<S : Structure, T : SymbolicTheory>(tuple : &[S]) -> Vec<SymbolicAtom<T>> {
    let description = Description { variables : (1..=tuple.len()).map(|i| format!("x{i}")).collect(), formula : diagram(tuple) };
    orbit_of::<T>(&description).unwrap().evaluate(|t| t.clone())
}

fn product<A : AtomsWithOrd>(tuple : Vec<A>) {
    let set : BTreeSet<A> = tuple.into_iter().collect();
    let start = Instant::now();
    let count = A::orbits_in_product(&set, &set).len();
    println!("{count} orbits in {:.4} s", start.elapsed().as_secs_f64());
}

/// The orbit of x_1 ... x_{k-1} - x_k over the given tuple.
fn generator<A : AtomsWithOrd>(tuple : Vec<A>) -> OrbitList<Q, A> {
    let x = |i : usize| Polynomial::<Q, A>::var(tuple[i].clone());
    let k = tuple.len();
    let product = (0..k - 1).fold(Polynomial::one(), |p, i| p * x(i));
    vec![Orbit::new(product - x(k - 1))]
}

fn basis<A : AtomsWithOrd>(tuple : Vec<A>, one_colour : bool, options : Options) {
    let generators = generator(tuple);
    let start = Instant::now();
    let result = if one_colour {
        one_colour_groebner_basis_with(generators, 2000, options)
    } else {
        equivariant_groebner_basis_with(generators, 2000, options)
    };
    match result {
        Ok(b) => println!("{} orbits in {:.3} s", b.len(), start.elapsed().as_secs_f64()),
        Err(b) => println!("limit reached ({} orbits) after {:.3} s", b.len(), start.elapsed().as_secs_f64()),
    }
}

fn main() {
    let args : Vec<String> = std::env::args().skip(1).collect();
    let n : usize = args[2].parse().unwrap();
    let concrete = args[3] == "concrete";
    match (args[0].as_str(), args[1].as_str()) {
        ("product", "dense-chain") if concrete => product(dense_chain(n)),
        ("product", "dense-chain") => product(symbolic::<DLO, DenseOrder>(&dense_chain(n))),
        ("product", "tree-chain") if concrete => product(tree_chain(n)),
        ("product", "tree-chain") => product(symbolic::<Tree, MeetTree>(&tree_chain(n))),
        ("product", "tree-comb") if concrete => product(tree_comb(n)),
        ("product", "tree-comb") => product(symbolic::<Tree, MeetTree>(&tree_comb(n))),
        ("basis", theory) => {
            let one_colour = args[4] == "one-colour";
            let selection = match args.get(5).map(String::as_str) {
                Some("domain") => Options { selection : Selection::SmallestDomain, first_criterion : false },
                Some("plain") => Options { selection : Selection::Creation, first_criterion : false },
                _ => Options::default(),
            };
            match (theory, concrete) {
                ("dense", true) => basis(dense_chain(n), one_colour, selection),
                ("dense", false) => basis(symbolic::<DLO, DenseOrder>(&dense_chain(n)), one_colour, selection),
                ("tree", true) => basis(tree_chain(n), one_colour, selection),
                (_, _) => basis(symbolic::<Tree, MeetTree>(&tree_chain(n)), one_colour, selection),
            }
        }
        _ => panic!("unknown case"),
    }
}
