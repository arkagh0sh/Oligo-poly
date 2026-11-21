use std::collections::BTreeSet;
use std::fmt::{Debug, Display, Formatter, Result};
use std::hash::Hash;
use std::marker::PhantomData;
use super::elements_with_atoms::*;

/// Atoms of a computationally oligomorphic relational structure with a linear
/// order, such as the dense linear order (Q, <).
///
/// Automorphisms preserve the order, so an automorphism that maps a finite set
/// S onto a finite set T restricts to the unique order-preserving bijection
/// from S onto T. This is why finite sets of atoms are stored as sorted sets.
///
/// Since we mean to use it only for polynomials, we only work with equivariant
/// orbits.
pub trait AtomsWithOrd : Ord + Clone + Hash + Debug {

    /// Whether some automorphism maps `first` onto `second`.
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool;

    /// One representative (S, T) for each orbit of pairs of finite sets in the
    /// product of the orbit of `first` and the orbit of `second`.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>)
        -> Vec<(BTreeSet<Self>, BTreeSet<Self>)>;
}

/// The orbit of an element with atoms, given by a representative.
/// The representative is private, so that orbits can only be used through the
/// operations below. Applied to equivariant functions, these operations are
/// equivariant.
#[derive(Clone)]
pub struct Orbit<A : AtomsWithOrd, B : ElementsWithAtoms<A>> {
    rep : B,
    atoms : PhantomData<A>
}

impl<A : AtomsWithOrd, B : ElementsWithAtoms<A>> Orbit<A, B> {

    /// The orbit of `rep`.
    pub fn new(rep : B) -> Self {
        Orbit { rep, atoms : PhantomData }
    }

    /// The elements of the orbit whose support is contained in `support`.
    pub fn supported_by(&self, support : &BTreeSet<A>) -> Vec<B> {
        B::project_to_support(&self.rep, support)
    }

    /// The orbits of pairs in the product of `self` and `other`.
    ///
    /// For ordered atoms, the orbit of a pair (x, y) is determined by the orbit
    /// of the pair of supports (supp(x), supp(y)), so we take the images of the
    /// representatives under the partial automorphisms onto each representative
    /// pair of supports.
    pub fn product<C : ElementsWithAtoms<A>>(&self, other : &Orbit<A, C>) -> Vec<Orbit<A, (B, C)>> {
        let first = self.rep.support();
        let second = other.rep.support();
        A::orbits_in_product(&first, &second)
            .into_iter()
            .map(|(s, t)| {
                let to_s = PartialAut::new(&first, &s).expect("orbits_in_product returned a set in another orbit");
                let to_t = PartialAut::new(&second, &t).expect("orbits_in_product returned a set in another orbit");
                Orbit::new((self.rep.apply_paut(&to_s), other.rep.apply_paut(&to_t)))
            })
            .collect()
    }

    /// The image of the orbit under a function `f`, which must be equivariant.
    pub fn map<C : ElementsWithAtoms<A>>(&self, f : impl Fn(&B) -> C) -> Orbit<A, C> {
        Orbit::new(f(&self.rep))
    }

    /// The value of a function `f` on the orbit. The function must be invariant,
    /// that is, f(π(b)) = f(b) for every automorphism π, so it is constant on the
    /// orbit. Examples are the degree of a polynomial and the size of a support.
    pub fn evaluate<T>(&self, f : impl Fn(&B) -> T) -> T {
        f(&self.rep)
    }

    /// The orbit itself if the predicate `p` holds on it, and `None` otherwise.
    /// The predicate must be equivariant, so it is constant on the orbit.
    pub fn filter(&self, p : impl Fn(&B) -> bool) -> Option<Orbit<A, B>> {
        if p(&self.rep) {
            Some(self.clone())
        } else {
            None
        }
    }
}

impl<A : AtomsWithOrd, B : ElementsWithAtoms<A>> PartialEq for Orbit<A, B> {
    fn eq(&self, other : &Self) -> bool {
        B::tuples_in_same_orbit(std::slice::from_ref(&self.rep), std::slice::from_ref(&other.rep))
    }
}

impl<A : AtomsWithOrd, B : ElementsWithAtoms<A>> Eq for Orbit<A, B> {}

/// Displays the orbit through its representative, for output only.
impl<A : AtomsWithOrd, B : ElementsWithAtoms<A> + Display> Display for Orbit<A, B> {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "orbit of {}", self.rep)
    }
}

/*
  atoms to add
    1. Equality
    2. Ordered
    3. Bit-vectors
    4. Dense-tree
    5. Rado graph
    6. Ordered Rado
    7. Homogenous (as a subtrait)
    8. Finite sets
    9. Products
    10. Finitely supported (atoms where some values are fixed as constants)
    11. Nesting of atoms
*/
