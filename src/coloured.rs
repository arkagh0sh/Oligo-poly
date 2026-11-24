//! Two coloured copies of a set of ordered atoms.
//!
//! This is the set Y = X + X of Section 5 of A. Ghosh and A. Lopez,
//! Computability of equivariant Gröbner bases (2025). An atom of Y is an atom of
//! X with a colour, low or high. Every low atom is smaller than every high atom,
//! and atoms of the same colour are ordered as in X. An automorphism π of X acts
//! on Y by π(c, a) = (c, π(a)): both copies are moved together.

use std::collections::BTreeSet;
use std::fmt::{Display, Formatter, Result};
use std::sync::OnceLock;
use crate::atoms::{Atoms, AtomsWithOrd, Orbit, SetPairOrbit, Structure};
use crate::logic::{Signature, Theory, LINEAR_ORDER};
use crate::product::Product;

/// The colour of an atom of Y: `Low` for the first copy of X, `High` for the
/// second one. `Low < High`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum Colour {
    Low,
    High,
}

impl Display for Colour {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        match self {
            Colour::Low => write!(f, "low"),
            Colour::High => write!(f, "high"),
        }
    }
}

/// The two colours as a structure: the order `<` and the unary relation
/// `high`. The axioms say that there is at most one high and one low element,
/// and that the low one comes first.
impl Structure for Colour {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| {
            let axioms = ["high(x) & high(y) -> x = y", "!high(x) & !high(y) -> x = y", "x < y -> !high(x) & high(y)"];
            let signature = Signature::new(&[("<", 2), ("high", 1)], &[]);
            Theory::new(signature, &[&LINEAR_ORDER[..], &axioms[..]].concat()).unwrap()
        })
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        match r {
            0 => args[0] < args[1],
            1 => args[0] == Colour::High,
            _ => panic!("the colours have two relations"),
        }
    }

    fn apply(_ : usize, _ : &[Self]) -> Self {
        panic!("the colours have no functions")
    }
}

/// The colours are fixed by the automorphisms: a tuple is only in the orbit of
/// itself.
impl Atoms for Colour {
    fn tuples_in_same_orbit(first : &[Self], second : &[Self]) -> bool {
        first == second
    }
}

impl AtomsWithOrd for Colour {
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        first == second
    }

    /// Every pair of sets is its own orbit.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> Vec<SetPairOrbit<Self>> {
        vec![Orbit::new((first.clone(), second.clone()))]
    }
}

/// An atom of Y = X + X: a colour and an atom of X. As a product, Y is ordered
/// by the colour first, then the atom, and the automorphisms of X act on the
/// atom only, which is the action of the paper.
pub type Coloured<A> = Product<Colour, A>;

impl<A> Product<Colour, A> {
    pub fn colour(&self) -> Colour {
        *self.first()
    }

    /// The underlying atom of X (the map `forget` of the paper).
    pub fn atom(&self) -> &A {
        self.second()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dlo::DLO;
    use crate::elements_with_atoms::ElementsWithAtoms;
    use itertools::Itertools;

    type Y = Coloured<DLO>;

    fn low(i : i64) -> Y {
        Coloured::new(Colour::Low, DLO::from_int(i))
    }

    fn high(i : i64) -> Y {
        Coloured::new(Colour::High, DLO::from_int(i))
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
        let atoms = |set : &BTreeSet<Y>| set.iter().map(|y| *y.atom()).collect::<BTreeSet<DLO>>().len();
        let n = atoms(first) + atoms(second);
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
