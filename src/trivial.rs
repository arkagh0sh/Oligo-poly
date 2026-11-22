//! Finitely many variables x1, x2, ... with the trivial group: the atoms
//! `FinOrd(i)` of a finite linear order, whose only automorphism is the
//! identity.
//!
//! The only automorphism is the identity, so every set of variables is its own
//! orbit, and an orbit of polynomials is a single polynomial. With these atoms:
//!
//! - `equivariant_buchberger` is Buchberger's algorithm in which a polynomial f
//!   is only reduced by polynomials h with supp(h) ⊆ supp(f);
//! - `equivariant_groebner_basis` is the colouring of Section 5 of Ghosh and
//!   Lopez applied to an ideal I of K[x1, ..., xn].
//!
//! Its result B is an equivariant Gröbner basis for the trivial group: every
//! non-zero f in I has an element h of B with supp(h) ⊆ supp(f) and LM(h)
//! dividing LM(f). Equivalently, for every set V of variables, the elements of
//! B in K[X_V] form a Gröbner basis of the elimination ideal I ∩ K[X_V].
//! Indeed, if f is in I ∩ K[X_V], then supp(h) ⊆ supp(f) ⊆ V; conversely, apply
//! the property for V = supp(f). An ordinary Gröbner basis only has this
//! property for the sets V = {x1, ..., xk}, by the Elimination Theorem.

use std::collections::BTreeSet;
use std::fmt::{Debug, Display, Formatter, Result};
use std::sync::OnceLock;
use crate::atoms::{Atoms, AtomsWithOrd, Orbit, SetPairOrbit, Structure};
use crate::elements_with_atoms::{ElementsWithAtoms, PartialAut};
use crate::logic::{Signature, Theory, LINEAR_ORDER};

/// The variable x_i. Variables are ordered by their index.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FinOrd(pub u32);

impl Display for FinOrd {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "x{}", self.0)
    }
}

impl Debug for FinOrd {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "x{}", self.0)
    }
}

/// The finite linear order: its signature has only the order `<`.
impl Structure for FinOrd {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| Theory::new(Signature::new(&[("<", 2)], &[]), &LINEAR_ORDER).unwrap())
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        assert_eq!(r, 0, "a finite linear order has only the relation <");
        args[0] < args[1]
    }

    fn apply(_ : usize, _ : &[Self]) -> Self {
        panic!("a finite linear order has no functions")
    }
}

/// The automorphism group is trivial, so the structure is not declared
/// homogeneous: a tuple is only in the orbit of itself.
impl Atoms for FinOrd {
    fn tuples_in_same_orbit(first : &[Self], second : &[Self]) -> bool {
        first == second
    }
}

impl AtomsWithOrd for FinOrd {
    /// Only the identity maps a set onto a set.
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        first == second
    }

    /// Every pair of sets is its own orbit.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>)
        -> Vec<SetPairOrbit<Self>> {
        vec![Orbit::new((first.clone(), second.clone()))]
    }
}

/// A variable is an element with atoms, with support {x}.
impl ElementsWithAtoms<FinOrd> for FinOrd {
    fn support(&self) -> BTreeSet<FinOrd> {
        BTreeSet::from([*self])
    }

    fn apply_paut(&self, paut : &PartialAut<FinOrd>) -> Self {
        paut.apply(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atoms::Orbit;
    use crate::equivariant::{equivariant_groebner_basis, one_colour_groebner_basis, PolynomialOrbit};
    use crate::ideal::{buchberger, elimination_ideal};
    use crate::mon::Polynomial;
    use num_rational::Rational64 as Q;
    use num_traits::Zero;

    type P = Polynomial<Q, FinOrd>;

    fn x(i : u32) -> P {
        Polynomial::var(FinOrd(i))
    }

    fn c(k : i64) -> P {
        Polynomial::constant(Q::from_integer(k))
    }

    /// The polynomials of a list of orbits: each orbit is a single polynomial.
    fn polynomials(orbits : &[PolynomialOrbit<Q, FinOrd>]) -> Vec<P> {
        orbits.iter().map(|o| o.evaluate(|p| p.clone())).collect()
    }

    /// The sets V of variables among x1, ..., xn for which the elements of `basis`
    /// in K[X_V] do not form a Gröbner basis of I ∩ K[X_V], where I is generated
    /// by `generators` and `basis` is contained in I.
    fn failing_sets(generators : &[P], basis : &[P], n : u32) -> Vec<BTreeSet<FinOrd>> {
        (0..1u32 << n)
            .map(|mask| (1..=n).filter(|i| mask >> (i - 1) & 1 == 1).map(FinOrd).collect::<BTreeSet<FinOrd>>())
            .filter(|v| {
                let inside : Vec<&P> = basis.iter().filter(|h| h.domain().is_subset(v)).collect();
                !elimination_ideal(generators, v).iter().all(|e| {
                    inside.iter().any(|h| !h.is_zero() && e.leading_mon().is_divisible_by(&h.leading_mon()))
                })
            })
            .collect()
    }

    fn colouring(generators : &[P]) -> Vec<P> {
        let orbits : Vec<PolynomialOrbit<Q, FinOrd>> = generators.iter().cloned().map(Orbit::new).collect();
        polynomials(&equivariant_groebner_basis(orbits, 500).ok().unwrap())
    }

    fn one_colour(generators : &[P]) -> Vec<P> {
        let orbits : Vec<PolynomialOrbit<Q, FinOrd>> = generators.iter().cloned().map(Orbit::new).collect();
        polynomials(&one_colour_groebner_basis(orbits, 500).ok().unwrap())
    }

    #[test]
    fn a_reduced_basis_without_the_property() {
        // I = <x2 - x1, x1^2>. The reduced Gröbner basis {x2 - x1, x1^2} has no
        // element in K[x2], but x2^2 = (x2 + x1)(x2 - x1) + x1^2 is in I.
        let generators = vec![x(2) - x(1), x(1) * x(1)];
        let ordinary = buchberger(generators.clone());
        assert_eq!(failing_sets(&generators, &ordinary, 2), vec![BTreeSet::from([FinOrd(2)])]);
        let basis = colouring(&generators);
        assert!(basis.contains(&(x(2) * x(2))));
        assert!(failing_sets(&generators, &basis, 2).is_empty());
        assert!(failing_sets(&generators, &one_colour(&generators), 2).is_empty());
    }

    #[test]
    fn twisted_cubic() {
        let generators = vec![x(2) - x(1) * x(1), x(3) - x(1) * x(1) * x(1)];
        let basis = colouring(&generators);
        assert!(failing_sets(&generators, &basis, 3).is_empty());
        assert!(failing_sets(&generators, &one_colour(&generators), 3).is_empty());
        // The ordinary basis misses the cuspidal cubic in K[x2, x3].
        let ordinary = buchberger(generators.clone());
        assert_eq!(failing_sets(&generators, &ordinary, 3), vec![BTreeSet::from([FinOrd(2), FinOrd(3)])]);
    }

    /// A small deterministic pseudo-random generator (xorshift).
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n : u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
    }

    #[test]
    fn random_ideals_in_three_variables() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        for _ in 0..10 {
            let generators : Vec<P> = (0..2)
                .map(|_| {
                    (0..3).fold(P::zero(), |f, _| {
                        let mut t = c(rng.below(5) as i64 - 2);
                        for _ in 0..rng.below(3) {
                            t = t * x(1 + rng.below(3) as u32);
                        }
                        f + t
                    })
                })
                .collect();
            let basis = colouring(&generators);
            assert!(failing_sets(&generators, &basis, 3).is_empty(), "generators {generators:?}");
            let basis = one_colour(&generators);
            assert!(failing_sets(&generators, &basis, 3).is_empty(), "one colour, generators {generators:?}");
        }
    }
}
