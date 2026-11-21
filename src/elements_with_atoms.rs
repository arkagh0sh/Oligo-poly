use std::collections::{BTreeMap, BTreeSet};
use itertools::Itertools;
use super::atoms::*;

/// A partial automorphism: the restriction of an automorphism to a finite set.
/// For ordered atoms it is the order-preserving bijection from its domain onto
/// its range, so it is determined by these two sets.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PartialAut<A : AtomsWithOrd> {
    map : BTreeMap<A, A>
}

impl<A : AtomsWithOrd> PartialAut<A> {
    /// The partial automorphism mapping `domain` onto `range`, if some
    /// automorphism maps `domain` onto `range`.
    pub fn new(domain : &BTreeSet<A>, range : &BTreeSet<A>) -> Option<Self> {
        if A::in_same_orbit(domain, range) {
            Some(PartialAut { map : domain.iter().cloned().zip(range.iter().cloned()).collect() })
        } else {
            None
        }
    }

    pub fn domain(&self) -> BTreeSet<A> {
        self.map.keys().cloned().collect()
    }

    pub fn range(&self) -> BTreeSet<A> {
        self.map.values().cloned().collect()
    }

    /// The image of an atom of the domain.
    pub fn apply(&self, a : &A) -> A {
        match self.map.get(a) {
            Some(b) => b.clone(),
            None => panic!("the atom {:?} is not in the domain of the partial automorphism", a),
        }
    }
}

/// The union of the supports of the elements of a tuple.
pub fn support_of_all<A : AtomsWithOrd, B : ElementsWithAtoms<A>>(elements : &[B]) -> BTreeSet<A> {
    elements.iter().flat_map(|x| x.support()).collect()
}

/*
Since we mean to use it only for polynomials,
we only work with equivariant orbits.
*/
/// Elements built from atoms, on which the automorphisms of the atoms act.
pub trait ElementsWithAtoms<A : AtomsWithOrd> : Clone + Eq {

    /// The least support of the element: the atoms that occur in it.
    fn support(&self) -> BTreeSet<A>;

    /// Applies a partial automorphism whose domain contains the support.
    fn apply_paut(&self, paut : &PartialAut<A>) -> Self;

    /// Whether some automorphism maps the tuple `first` to the tuple `second`.
    /// Such an automorphism maps the support of `first` onto that of `second`,
    /// so it suffices to try the partial automorphism between the supports.
    fn tuples_in_same_orbit(first : &[Self], second : &[Self]) -> bool {
        if first.len() != second.len() {
            return false;
        }
        match PartialAut::new(&support_of_all(first), &support_of_all(second)) {
            Some(paut) => first.iter().zip(second.iter()).all(|(x, y)| x.apply_paut(&paut) == *y),
            None => false,
        }
    }

    /// The elements in the orbit of `rep` that are supported by `support`.
    /// Such an element is the image of `rep` under the partial automorphism from
    /// the support of `rep` onto a subset of `support`.
    /// Technically we should compute the algebraic closure of a support,
    /// but we omit that for simplicity.
    fn project_to_support(rep : &Self, support : &BTreeSet<A>) -> Vec<Self> {
        let rep_support = rep.support();
        support
            .iter()
            .cloned()
            .combinations(rep_support.len())
            .filter_map(|subset| PartialAut::new(&rep_support, &subset.into_iter().collect()))
            .map(|paut| rep.apply_paut(&paut))
            .collect()
    }
}

impl<A : AtomsWithOrd> ElementsWithAtoms<A> for BTreeSet<A> {
    fn support(&self) -> BTreeSet<A> {
        self.clone()
    }

    fn apply_paut(&self, paut : &PartialAut<A>) -> Self {
        self.iter().map(|a| paut.apply(a)).collect()
    }
}

impl<A : AtomsWithOrd, B : ElementsWithAtoms<A>, C : ElementsWithAtoms<A>> ElementsWithAtoms<A> for (B, C) {
    fn support(&self) -> BTreeSet<A> {
        let mut support = self.0.support();
        support.extend(self.1.support());
        support
    }

    fn apply_paut(&self, paut : &PartialAut<A>) -> Self {
        (self.0.apply_paut(paut), self.1.apply_paut(paut))
    }
}

impl<A : AtomsWithOrd, B : ElementsWithAtoms<A>> ElementsWithAtoms<A> for Vec<B> {
    fn support(&self) -> BTreeSet<A> {
        support_of_all(self)
    }

    fn apply_paut(&self, paut : &PartialAut<A>) -> Self {
        self.iter().map(|x| x.apply_paut(paut)).collect()
    }
}
