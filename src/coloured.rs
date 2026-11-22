//! Two coloured copies of a set of ordered atoms.
//!
//! This is the set Y = X + X of Section 5 of A. Ghosh and A. Lopez,
//! Computability of equivariant Gröbner bases (2025). An atom of Y is an atom of
//! X with a colour, low or high. Every low atom is smaller than every high atom,
//! and atoms of the same colour are ordered as in X. An automorphism π of X acts
//! on Y by π(c, a) = (c, π(a)): both copies are moved together.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Debug, Display, Formatter, Result};
use crate::atoms::{theory_of_type, Atoms, AtomsWithOrd, Orbit, SetPairOrbit, Structure};
use crate::elements_with_atoms::PartialAut;
use crate::logic::{Signature, Theory};

/// The colour of an atom of Y: `Low` for the first copy of X, `High` for the
/// second one. `Low < High`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Colour {
    Low,
    High,
}

/// An atom of Y = X + X. The derived order compares the colour first, then the
/// atom, as required.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Coloured<A> {
    colour : Colour,
    atom : A,
}

impl<A> Coloured<A> {
    pub fn new(colour : Colour, atom : A) -> Self {
        Coloured { colour, atom }
    }

    pub fn colour(&self) -> Colour {
        self.colour
    }

    /// The underlying atom of X (the map `forget` of the paper).
    pub fn atom(&self) -> &A {
        &self.atom
    }
}

impl<A : Display> Display for Coloured<A> {
    /// High atoms are printed with a prime.
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        match self.colour {
            Colour::Low => write!(f, "{}", self.atom),
            Colour::High => write!(f, "{}'", self.atom),
        }
    }
}

impl<A : Debug> Debug for Coloured<A> {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        match self.colour {
            Colour::Low => write!(f, "{:?}", self.atom),
            Colour::High => write!(f, "{:?}'", self.atom),
        }
    }
}

/// The underlying atoms of a set of atoms of Y.
fn underlying<A : AtomsWithOrd>(set : &BTreeSet<Coloured<A>>) -> BTreeSet<A> {
    set.iter().map(|y| y.atom.clone()).collect()
}

/// The image of a set of atoms of Y under a partial automorphism of X, which
/// keeps the colours.
fn recolour<A : AtomsWithOrd>(set : &BTreeSet<Coloured<A>>, paut : &PartialAut<A>) -> BTreeSet<Coloured<A>> {
    set.iter().map(|y| Coloured::new(y.colour, paut.apply(&y.atom))).collect()
}

/// Y as a structure. Its signature has the relations of X, interpreted on the
/// underlying atoms, except the order `<`, which is the order of Y; a unary
/// relation `high`; and a binary relation `same`, which holds for two atoms
/// with the same underlying atom. The functions of X are interpreted on the
/// underlying atoms, and their values are low. The theory has no axioms: Y is
/// only used inside the algorithms, through its own orbit tests, and it is not
/// declared homogeneous.
impl<A : AtomsWithOrd> Structure for Coloured<A> {
    fn theory() -> &'static Theory {
        theory_of_type::<Self>(|| {
            let mut signature : Signature = A::theory().signature.clone();
            signature.relations.push(("high".to_string(), 1));
            signature.relations.push(("same".to_string(), 2));
            Theory { signature, axioms : Vec::new() }
        })
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        let relations = &A::theory().signature.relations;
        if r == relations.len() {
            args[0].colour == Colour::High
        } else if r == relations.len() + 1 {
            args[0].atom == args[1].atom
        } else if relations[r].0 == "<" {
            args[0] < args[1]
        } else {
            A::holds(r, &args.iter().map(|y| y.atom.clone()).collect::<Vec<_>>())
        }
    }

    fn apply(f : usize, args : &[Self]) -> Self {
        Coloured::new(Colour::Low, A::apply(f, &args.iter().map(|y| y.atom.clone()).collect::<Vec<_>>()))
    }
}

/// An automorphism π of X maps a tuple of Y to another one if and only if it
/// keeps the colours and maps the underlying tuple of atoms accordingly.
impl<A : AtomsWithOrd> Atoms for Coloured<A> {
    fn tuples_in_same_orbit(first : &[Self], second : &[Self]) -> bool {
        first.len() == second.len()
            && first.iter().zip(second).all(|(s, t)| s.colour == t.colour)
            && A::tuples_in_same_orbit(
                &first.iter().map(|y| y.atom.clone()).collect::<Vec<_>>(),
                &second.iter().map(|y| y.atom.clone()).collect::<Vec<_>>(),
            )
    }
}

impl<A : AtomsWithOrd> AtomsWithOrd for Coloured<A> {

    /// An automorphism of Y preserves the order of Y, so if it maps `first`
    /// onto `second`, it maps the i-th element of `first` to the i-th element of
    /// `second`. So `first` and `second` are in the same orbit if and only if
    /// these pairs have the same colours, and their underlying atoms are related
    /// by a partial automorphism of X, which then maps the underlying atoms of
    /// `first` onto those of `second` in increasing order.
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        if first.len() != second.len() {
            return false;
        }
        let (u, v) = (underlying(first), underlying(second));
        if u.len() != v.len() || !A::in_same_orbit(&u, &v) {
            return false;
        }
        let map : BTreeMap<&A, &A> = u.iter().zip(v.iter()).collect();
        first.iter().zip(second.iter()).all(|(s, t)| s.colour == t.colour && map[&s.atom] == &t.atom)
    }

    /// If σ maps a set S of atoms of Y to S', then the underlying atoms of S' are
    /// the image of those of S, and S' is determined by them. So the orbits of
    /// pairs (S', T') correspond to the orbits of pairs of their underlying
    /// atoms, which `A::orbits_in_product` lists.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>)
        -> Vec<SetPairOrbit<Self>> {
        let (u, v) = (underlying(first), underlying(second));
        A::orbits_in_product(&u, &v)
            .iter()
            .map(|pair| {
                let (u2, v2) = pair.representative();
                let to_u2 = PartialAut::new(&u, u2).expect("orbits_in_product returned a set in another orbit");
                let to_v2 = PartialAut::new(&v, v2).expect("orbits_in_product returned a set in another orbit");
                Orbit::new((recolour(first, &to_u2), recolour(second, &to_v2)))
            })
            .collect()
    }
}

#[cfg(all(test, feature = "equivariant"))]
mod tests {
    use super::*;
    use crate::dlo::DLO;
    use crate::elements_with_atoms::ElementsWithAtoms;
    use itertools::Itertools;
    use rug::Rational;

    type Y = Coloured<DLO>;

    fn low(i : i64) -> Y {
        Coloured::new(Colour::Low, DLO::new(Rational::from(i)))
    }

    fn high(i : i64) -> Y {
        Coloured::new(Colour::High, DLO::new(Rational::from(i)))
    }

    #[test]
    fn order_and_orbits_of_sets() {
        assert!(low(5) < high(1));
        let s = BTreeSet::from([low(1), high(1), high(2)]);
        assert!(Y::in_same_orbit(&s, &BTreeSet::from([low(4), high(4), high(7)])));
        // The low and the high atom must stay over the same atom of X.
        assert!(!Y::in_same_orbit(&s, &BTreeSet::from([low(4), high(5), high(7)])));
        // The colours must be kept.
        assert!(!Y::in_same_orbit(&s, &BTreeSet::from([low(4), low(5), high(4)])));
        // The order of the underlying atoms must be kept.
        assert!(!Y::in_same_orbit(&s, &BTreeSet::from([low(4), high(3), high(4)])));
    }

    /// Checks `orbits_in_product` against a brute-force count: all pairs of sets
    /// in the orbits of `first` and `second` whose underlying atoms are in a
    /// universe large enough for every orbit of pairs, up to the orbit relation.
    fn check_product(first : &BTreeSet<Y>, second : &BTreeSet<Y>) {
        let reps = Y::orbits_in_product(first, second);
        for i in 0..reps.len() {
            assert!(reps[i].evaluate(|(s, t)| Y::in_same_orbit(first, s) && Y::in_same_orbit(second, t)));
            for j in 0..i {
                assert!(reps[i] != reps[j]);
            }
        }
        let n = underlying(first).len() + underlying(second).len();
        let universe : Vec<Y> = (1..=n as i64).flat_map(|i| [low(i), high(i)]).collect();
        let in_orbit = |set : &BTreeSet<Y>, len : usize| -> Vec<BTreeSet<Y>> {
            universe.iter().cloned().combinations(len)
                .map(|c| c.into_iter().collect::<BTreeSet<Y>>())
                .filter(|c| Y::in_same_orbit(set, c))
                .collect()
        };
        let mut found : Vec<(BTreeSet<Y>, BTreeSet<Y>)> = Vec::new();
        for s in in_orbit(first, first.len()) {
            for t in in_orbit(second, second.len()) {
                let pair = (s.clone(), t);
                if !found.iter().any(|r| <(BTreeSet<Y>, BTreeSet<Y>)>::tuples_in_same_orbit(std::slice::from_ref(r), std::slice::from_ref(&pair))) {
                    found.push(pair);
                }
            }
        }
        assert_eq!(reps.len(), found.len(), "first = {first:?}, second = {second:?}");
    }

    #[test]
    fn orbits_in_product_are_complete_and_distinct() {
        let sets = [
            BTreeSet::from([low(1)]),
            BTreeSet::from([high(1)]),
            BTreeSet::from([low(1), high(1)]),
            BTreeSet::from([low(1), high(2)]),
            BTreeSet::from([low(2), high(1)]),
            BTreeSet::from([low(1), low(2), high(3)]),
        ];
        for first in &sets {
            for second in &sets {
                check_product(first, second);
            }
        }
    }
}
