use rug::Rational;
use std::collections::BTreeSet;
use std::fmt::{Debug, Display, Formatter, Result};
use itertools::Itertools;
use std::sync::OnceLock;
use crate::elements_with_atoms::{ElementsWithAtoms, PartialAut};
use crate::logic::{Signature, Theory, LINEAR_ORDER};

use super::atoms::*;

/// Atoms of the dense linear order without endpoints (Q, <).
/// The value is private, so programs can only compare atoms with the order and
/// equality.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DLO {
    val : Rational
}

impl DLO {
    pub fn new(q : Rational) -> DLO {
        DLO {val : q}
    }
}

impl Debug for DLO {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "d({})", self.val)
    }
}

impl Display for DLO {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "d({})", self.val)
    }
}

/// (Q, <) as a structure: its signature has only the order `<`, and its finite
/// substructures are the finite linear orders.
impl Structure for DLO {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| Theory::new(Signature::new(&[("<", 2)], &[]), &LINEAR_ORDER).unwrap())
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        assert_eq!(r, 0, "(Q, <) has only the relation <");
        args[0] < args[1]
    }

    fn apply(_ : usize, _ : &[Self]) -> Self {
        panic!("(Q, <) has no functions")
    }
}

/// (Q, <) is homogeneous: every order-preserving bijection between finite sets
/// extends to an automorphism.
impl HomogeneousStructure for DLO {}

impl AtomsWithOrd for DLO {

    /// Two finite sets are in the same orbit if and only if they have the same
    /// size. This is faster than the default, and agrees with it (see the tests).
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        first.len() == second.len()
    }

    /// The orbit of a pair (S, T) with |S| = n and |T| = m is determined by how S
    /// and T interleave. We list one representative per orbit: S ∪ T = {1, ..., k}
    /// for some k with max(n, m) <= k <= n + m, every element of {1, ..., k} not in
    /// S is in T, and T contains n + m - k elements of S.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>)
        -> Vec<SetPairOrbit<Self>> {
        let (n, m) = (first.len(), second.len());
        let atom = |i : usize| DLO::new(Rational::from(i as u64));
        let mut reps = Vec::new();
        for k in n.max(m)..=(n + m) {
            for s in (1..=k).combinations(n) {
                let outside_s : Vec<usize> = (1..=k).filter(|i| !s.contains(i)).collect();
                for common in s.iter().cloned().combinations(n + m - k) {
                    let s_atoms : BTreeSet<DLO> = s.iter().map(|&i| atom(i)).collect();
                    let t_atoms : BTreeSet<DLO> = outside_s.iter().chain(common.iter()).map(|&i| atom(i)).collect();
                    reps.push(Orbit::new((s_atoms, t_atoms)));
                }
            }
        }
        reps
    }
}

/// An atom is an element with atoms, with support {a}.
impl ElementsWithAtoms<DLO> for DLO {
    fn support(&self) -> BTreeSet<DLO> {
        BTreeSet::from([self.clone()])
    }

    fn apply_paut(&self, paut : &PartialAut<DLO>) -> Self {
        paut.apply(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(i : i64) -> DLO {
        DLO::new(Rational::from(i))
    }

    fn set(xs : &[i64]) -> BTreeSet<DLO> {
        xs.iter().map(|&i| d(i)).collect()
    }

    type SetPair = (BTreeSet<DLO>, BTreeSet<DLO>);

    #[test]
    fn same_orbit_for_sets() {
        assert!(DLO::in_same_orbit(&set(&[1, 2]), &set(&[5, 9])));
        assert!(!DLO::in_same_orbit(&set(&[1]), &set(&[1, 2])));
        let paut = PartialAut::new(&set(&[1, 2]), &set(&[5, 9])).unwrap();
        assert_eq!(paut.apply(&d(2)), d(9));
    }

    /// Counts the orbits of pairs (S, T) with |S| = n and |T| = m by brute force:
    /// all such pairs of subsets of {1, ..., n + m}, up to being in the same orbit.
    fn brute_force_orbit_count(n : usize, m : usize) -> usize {
        let universe : Vec<i64> = (1..=(n + m) as i64).collect();
        let mut reps : Vec<SetPair> = Vec::new();
        for s in universe.iter().cloned().combinations(n) {
            for t in universe.iter().cloned().combinations(m) {
                let pair = (set(&s), set(&t));
                if !reps.iter().any(|r| SetPair::tuples_in_same_orbit(std::slice::from_ref(r), std::slice::from_ref(&pair))) {
                    reps.push(pair);
                }
            }
        }
        reps.len()
    }

    #[test]
    fn orbits_in_product_are_complete_and_distinct() {
        for n in 0..=3 {
            for m in 0..=3 {
                let first = set(&(1..=n as i64).collect::<Vec<_>>());
                let second = set(&(1..=m as i64).collect::<Vec<_>>());
                let reps = DLO::orbits_in_product(&first, &second);
                for i in 0..reps.len() {
                    assert_eq!(reps[i].evaluate(|(s, t)| (s.len(), t.len())), (n, m));
                    for j in 0..i {
                        assert!(reps[i] != reps[j]);
                    }
                }
                assert_eq!(reps.len(), brute_force_orbit_count(n, m), "n = {n}, m = {m}");
            }
        }
        // Q^2 splits into the three orbits a < b, a = b and a > b.
        assert_eq!(DLO::orbits_in_product(&set(&[7]), &set(&[7])).len(), 3);
    }

    /// The canonical test of homogeneous structures agrees with the test of
    /// `in_same_orbit` for (Q, <): same size.
    #[test]
    fn canonical_orbit_test() {
        use crate::atoms::homogeneous_tuples_in_same_orbit;
        let sets : Vec<Vec<DLO>> = (0..4usize)
            .flat_map(|k| (1..=5i64).combinations(k).map(|c| c.into_iter().map(d).collect::<Vec<_>>()))
            .collect();
        for a in &sets {
            for b in &sets {
                assert_eq!(homogeneous_tuples_in_same_orbit(a, b), a.len() == b.len());
            }
        }
        // As tuples, the order matters: (1, 2) and (2, 1) are in different orbits.
        assert!(!homogeneous_tuples_in_same_orbit(&[d(1), d(2)], &[d(2), d(1)]));
        assert!(!homogeneous_tuples_in_same_orbit(&[d(1), d(1)], &[d(1), d(2)]));
    }

    #[test]
    fn polynomials_over_atoms() {
        use crate::bits::F2;
        use crate::mon::Polynomial;
        type P = Polynomial<F2, DLO>;
        let v = |i : i64| -> P { Polynomial::var(d(i)) };
        // f = a^2 c + b with atoms a < b < c.
        let f = v(1) * v(1) * v(3) + v(2);
        assert_eq!(f.support(), set(&[1, 2, 3]));
        let paut = PartialAut::new(&set(&[1, 2, 3]), &set(&[5, 6, 9])).unwrap();
        let g = f.apply_paut(&paut);
        assert_eq!(g, v(5) * v(5) * v(9) + v(6));
        // Partial automorphisms preserve the monomial order, so they commute with
        // taking leading monomials.
        assert_eq!(Polynomial::<F2, DLO>::from_monomial(g.leading_mon()),
                   Polynomial::<F2, DLO>::from_monomial(f.leading_mon()).apply_paut(&paut));
        // The orbit of f: equality and elements supported by {1, 2, 3, 4}.
        let orbit = Orbit::new(f.clone());
        assert!(orbit == Orbit::new(g));
        assert!(orbit != Orbit::new(v(1) * v(1) * v(2) + v(3)));
        assert_eq!(orbit.supported_by(&set(&[1, 2, 3, 4])).len(), 4);
    }

    #[test]
    fn orbit_operations() {
        // Orbits of single atoms and of 2-element sets.
        let atoms : Orbit<DLO, DLO> = Orbit::new(d(1));
        let pairs : Orbit<DLO, BTreeSet<DLO>> = Orbit::new(set(&[1, 2]));
        assert!(pairs == Orbit::new(set(&[3, 10])));
        assert!(pairs != Orbit::new(set(&[3])));
        // Elements supported by {1, 2, 3, 4}.
        let s = set(&[1, 2, 3, 4]);
        assert_eq!(atoms.supported_by(&s).len(), 4);
        assert_eq!(pairs.supported_by(&s).len(), 6);
        // The product of the orbit of atoms with itself has 3 orbits.
        let product = atoms.product(&atoms);
        assert_eq!(product.len(), 3);
        assert!(product.contains(&Orbit::new((d(5), d(5)))));
        assert!(product.contains(&Orbit::new((d(5), d(6)))));
        assert!(product.contains(&Orbit::new((d(6), d(5)))));
        // map and filter with equivariant functions.
        assert!(product.iter().all(|o| o.map(|(a, _)| a.clone()) == atoms));
        let diagonal : Vec<_> = product.iter().filter_map(|o| o.filter(|(a, b)| a == b)).collect();
        assert_eq!(diagonal.len(), 1);
    }
}
