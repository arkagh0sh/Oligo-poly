//! Products of ordered atoms.
//!
//! The atoms of `Product<A1, A2>` are the pairs (a, b) of an atom a of `A1` and
//! an atom b of `A2`. The product G1 × G2 of the automorphism groups acts on
//! each coordinate separately, and the pairs are ordered lexicographically,
//! first by a and then by b. Both groups preserve their orders, so G1 × G2
//! preserves this order.
//!
//! The orbits of pairs of sets are computed from those of the two factors, by
//! the following facts. For a set S of pairs, write p1(S) and p2(S) for its
//! projections.
//!
//! 1. For ordered atoms, at most one partial automorphism maps a finite set U
//!    onto a set U': the increasing bijection.
//! 2. Let S' and S'' be in the orbit of S, and T' and T'' in the orbit of T. The
//!    pairs (S', T') and (S'', T'') are in the same orbit if and only if the
//!    pairs (p1(S'), p1(T')) and (p1(S''), p1(T'')) are in the same G1-orbit
//!    and the pairs (p2(S'), p2(T')) and (p2(S''), p2(T'')) are in the same
//!    G2-orbit. Indeed, take σ1 and σ2 that relate these pairs, and π with
//!    S' = π(S) and ρ with S'' = ρ(S). By fact 1, σ1 π1 and ρ1 agree on p1(S),
//!    and σ2 π2 and ρ2 agree on p2(S), so σ = (σ1, σ2) maps S' to S''. The same
//!    holds for T' and T''.
//! 3. Every pair of an orbit of (p1(S), p1(T)) and an orbit of (p2(S), p2(T))
//!    occurs: extend the partial automorphisms from the projections of S and
//!    T onto the representatives to automorphisms.
//!
//! So the orbits of pairs (S', T') correspond to the pairs of such orbits.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{Debug, Display, Formatter, Result};
use crate::atoms::{theory_of_type, Atoms, AtomsWithOrd, Orbit, SetPairOrbit, Structure};
use crate::elements_with_atoms::{ElementsWithAtoms, PartialAut};
use crate::logic::{Signature, Theory};

/// An atom of the product: a pair of atoms. The derived order compares the
/// first atom, then the second one, as required.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Product<A1, A2> {
    first : A1,
    second : A2,
}

impl<A1, A2> Product<A1, A2> {
    pub fn new(first : A1, second : A2) -> Self {
        Product { first, second }
    }

    pub fn first(&self) -> &A1 {
        &self.first
    }

    pub fn second(&self) -> &A2 {
        &self.second
    }
}

impl<A1 : Display, A2 : Display> Display for Product<A1, A2> {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "({}, {})", self.first, self.second)
    }
}

impl<A1 : Debug, A2 : Debug> Debug for Product<A1, A2> {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "({:?}, {:?})", self.first, self.second)
    }
}

/// The first coordinates of a list of pairs.
fn firsts<A1 : Clone, A2>(args : &[Product<A1, A2>]) -> Vec<A1> {
    args.iter().map(|p| p.first.clone()).collect()
}

/// The second coordinates of a list of pairs.
fn seconds<A1, A2 : Clone>(args : &[Product<A1, A2>]) -> Vec<A2> {
    args.iter().map(|p| p.second.clone()).collect()
}

/// The functions of a signature that have arguments, by their numbers.
fn non_constants(signature : &Signature) -> Vec<usize> {
    (0..signature.functions.len()).filter(|&f| signature.functions[f].1 > 0).collect()
}

/// The name of a symbol of a factor in the product: `R` becomes `R_1` or
/// `R_2`, and the order `<` becomes `less_1` or `less_2`.
fn lifted(name : &str, factor : usize) -> String {
    if name == "<" { format!("less_{factor}") } else { format!("{name}_{factor}") }
}

/// The product as a structure. Its signature has, in this order:
/// - the product order `<`;
/// - the relations of `A1` on the first coordinates, then those of `A2` on the
///   second coordinates, renamed by `lifted`;
/// - the equivalences `same_1` and `same_2`: same first, or same second,
///   coordinate;
/// - the functions of `A1` with arguments, which apply to the first coordinates
///   and keep the second coordinate of the first argument, then those of `A2`
///   in the same way. This choice commutes with G1 × G2. The constants of the
///   factors are left out, since a constant of `A1` has no second coordinate.
///
/// The theory has no axioms: the product is used through its own orbit tests,
/// and it is not declared homogeneous.
impl<A1 : AtomsWithOrd, A2 : AtomsWithOrd> Structure for Product<A1, A2> {
    fn theory() -> &'static Theory {
        theory_of_type::<Self>(|| {
            let (s1, s2) = (&A1::theory().signature, &A2::theory().signature);
            let mut signature = Signature::new(&[("<", 2)], &[]);
            for (s, factor) in [(s1, 1), (s2, 2)] {
                signature.relations.extend(s.relations.iter().map(|(n, k)| (lifted(n, factor), *k)));
            }
            signature.relations.push(("same_1".to_string(), 2));
            signature.relations.push(("same_2".to_string(), 2));
            for (s, factor) in [(s1, 1), (s2, 2)] {
                signature.functions.extend(non_constants(s).into_iter().map(|f| (lifted(&s.functions[f].0, factor), s.functions[f].1)));
            }
            Theory { signature, axioms : Vec::new() }
        })
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        let n1 = A1::theory().signature.relations.len();
        let n2 = A2::theory().signature.relations.len();
        match r {
            0 => args[0] < args[1],
            r if r <= n1 => A1::holds(r - 1, &firsts(args)),
            r if r <= n1 + n2 => A2::holds(r - 1 - n1, &seconds(args)),
            r if r == n1 + n2 + 1 => args[0].first == args[1].first,
            r if r == n1 + n2 + 2 => args[0].second == args[1].second,
            _ => panic!("the product has {} relations", n1 + n2 + 3),
        }
    }

    fn apply(f : usize, args : &[Self]) -> Self {
        let f1 = non_constants(&A1::theory().signature);
        let f2 = non_constants(&A2::theory().signature);
        if f < f1.len() {
            Product::new(A1::apply(f1[f], &firsts(args)), args[0].second.clone())
        } else {
            Product::new(args[0].first.clone(), A2::apply(f2[f - f1.len()], &seconds(args)))
        }
    }
}

/// G1 × G2 maps a tuple to another one if and only if G1 maps the first
/// coordinates and G2 the second coordinates accordingly.
impl<A1 : AtomsWithOrd, A2 : AtomsWithOrd> Atoms for Product<A1, A2> {
    fn tuples_in_same_orbit(first : &[Self], second : &[Self]) -> bool {
        first.len() == second.len()
            && A1::tuples_in_same_orbit(&firsts(first), &firsts(second))
            && A2::tuples_in_same_orbit(&seconds(first), &seconds(second))
    }
}

/// The set of the first coordinates of a set of pairs.
fn first_projection<A1 : AtomsWithOrd, A2>(set : &BTreeSet<Product<A1, A2>>) -> BTreeSet<A1> {
    set.iter().map(|p| p.first.clone()).collect()
}

/// The set of the second coordinates of a set of pairs.
fn second_projection<A1, A2 : AtomsWithOrd>(set : &BTreeSet<Product<A1, A2>>) -> BTreeSet<A2> {
    set.iter().map(|p| p.second.clone()).collect()
}

/// The image of a set of pairs under a pair of partial automorphisms.
fn image<A1 : AtomsWithOrd, A2 : AtomsWithOrd>(
    set : &BTreeSet<Product<A1, A2>>,
    paut1 : &PartialAut<A1>,
    paut2 : &PartialAut<A2>,
) -> BTreeSet<Product<A1, A2>> {
    set.iter().map(|p| Product::new(paut1.apply(&p.first), paut2.apply(&p.second))).collect()
}

/// The partial automorphisms from `first` and `second` onto the two sets of
/// the representative of an orbit of pairs.
fn onto<A : AtomsWithOrd>(first : &BTreeSet<A>, second : &BTreeSet<A>, orbit : &SetPairOrbit<A>) -> (PartialAut<A>, PartialAut<A>) {
    let (s, t) = orbit.representative();
    let expect = "orbits_in_product returned a set in another orbit";
    (PartialAut::new(first, s).expect(expect), PartialAut::new(second, t).expect(expect))
}

impl<A1 : AtomsWithOrd, A2 : AtomsWithOrd> AtomsWithOrd for Product<A1, A2> {
    /// An automorphism π that maps `first` onto `second` preserves the order, so
    /// it maps the i-th element of `first` to the i-th element of `second`, and
    /// its coordinates map the projections increasingly (fact 1). Conversely,
    /// if the projections are in the same orbits and the increasing bijections
    /// between them map `first` onto `second`, then extensions π1 and π2 of
    /// these bijections give π = (π1, π2). This uses the set tests of the
    /// factors, which may be faster than the tuple test.
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        if first.len() != second.len() {
            return false;
        }
        let (u1, v1) = (first_projection(first), first_projection(second));
        let (u2, v2) = (second_projection(first), second_projection(second));
        if u1.len() != v1.len() || u2.len() != v2.len() || !A1::in_same_orbit(&u1, &v1) || !A2::in_same_orbit(&u2, &v2) {
            return false;
        }
        let map1 : BTreeMap<&A1, &A1> = u1.iter().zip(v1.iter()).collect();
        let map2 : BTreeMap<&A2, &A2> = u2.iter().zip(v2.iter()).collect();
        first.iter().zip(second.iter()).all(|(p, q)| map1[&p.first] == &q.first && map2[&p.second] == &q.second)
    }

    /// One orbit for each pair of an orbit of pairs of first projections and an
    /// orbit of pairs of second projections (see the module documentation).
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> Vec<SetPairOrbit<Self>> {
        let (u1, v1) = (first_projection(first), first_projection(second));
        let (u2, v2) = (second_projection(first), second_projection(second));
        let orbits2 = A2::orbits_in_product(&u2, &v2);
        let mut result = Vec::new();
        for o1 in A1::orbits_in_product(&u1, &v1) {
            let (to_s1, to_t1) = onto(&u1, &v1, &o1);
            for o2 in &orbits2 {
                let (to_s2, to_t2) = onto(&u2, &v2, o2);
                result.push(Orbit::new((image(first, &to_s1, &to_s2), image(second, &to_t1, &to_t2))));
            }
        }
        result
    }
}

/// A pair is an element with atoms, with support {(a, b)}.
impl<A1 : AtomsWithOrd, A2 : AtomsWithOrd> ElementsWithAtoms<Product<A1, A2>> for Product<A1, A2> {
    fn support(&self) -> BTreeSet<Product<A1, A2>> {
        BTreeSet::from([self.clone()])
    }

    fn apply_paut(&self, paut : &PartialAut<Product<A1, A2>>) -> Self {
        paut.apply(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coloured::Colour;
    use crate::logic::{Description, Formula, Term};
    use crate::symbolic::{orbit_of, DenseOrder, SymbolicAtom};
    use itertools::Itertools;

    type D = SymbolicAtom<DenseOrder>;
    type P = Product<D, D>;

    /// n atoms d_0 < ... < d_{n-1} of (Q, <), in one finite structure.
    fn chain(n : usize) -> Vec<D> {
        let formula = Formula::And((1..n).map(|i| Formula::Rel(0, vec![Term::Var(i - 1), Term::Var(i)])).collect());
        let description = Description { variables : (0..n).map(|i| format!("x{i}")).collect(), formula };
        orbit_of::<DenseOrder>(&description).unwrap().evaluate(|t| t.clone())
    }

    /// The orbits of pairs in the product of the orbits of `first` and
    /// `second`, by brute force: all pairs of sets in these orbits inside a
    /// universe large enough for every orbit, up to the orbit relation.
    fn brute_force<A : AtomsWithOrd>(first : &BTreeSet<A>, second : &BTreeSet<A>, universe : &[A]) -> usize {
        let in_orbit = |set : &BTreeSet<A>| -> Vec<BTreeSet<A>> {
            universe.iter().cloned().combinations(set.len())
                .map(|c| c.into_iter().collect::<BTreeSet<A>>())
                .filter(|c| A::in_same_orbit(set, c))
                .collect()
        };
        let mut found : Vec<(BTreeSet<A>, BTreeSet<A>)> = Vec::new();
        for s in in_orbit(first) {
            for t in in_orbit(second) {
                let pair = (s.clone(), t);
                if !found.iter().any(|r| <(BTreeSet<A>, BTreeSet<A>)>::tuples_in_same_orbit(std::slice::from_ref(r), std::slice::from_ref(&pair))) {
                    found.push(pair);
                }
            }
        }
        found.len()
    }

    fn check<A : AtomsWithOrd>(first : &BTreeSet<A>, second : &BTreeSet<A>, universe : &[A]) {
        let reps = A::orbits_in_product(first, second);
        for i in 0..reps.len() {
            assert!(reps[i].evaluate(|(s, t)| A::in_same_orbit(first, s) && A::in_same_orbit(second, t)));
            for j in 0..i {
                assert!(reps[i] != reps[j]);
            }
        }
        assert_eq!(reps.len(), brute_force(first, second, universe), "first = {first:?}, second = {second:?}");
    }

    /// Q × Q with Aut(Q) × Aut(Q).
    #[test]
    fn orbits_of_pairs_in_the_plane() {
        let d = chain(4);
        let universe : Vec<P> = d.iter().cartesian_product(d.iter()).map(|(a, b)| Product::new(a.clone(), b.clone())).collect();
        let p = |i : usize, j : usize| Product::new(d[i].clone(), d[j].clone());
        let sets = [
            BTreeSet::from([p(0, 0)]),
            BTreeSet::from([p(0, 0), p(1, 1)]),
            BTreeSet::from([p(0, 1), p(1, 0)]),
            BTreeSet::from([p(0, 0), p(0, 1)]),
        ];
        for first in &sets {
            for second in &sets[..2] {
                check(first, second, &universe);
            }
        }
        // A point and a point: three positions in each coordinate.
        assert_eq!(P::orbits_in_product(&sets[0], &sets[0]).len(), 9);
    }

    /// The order and the orbits of sets of the product.
    #[test]
    fn order_and_sets() {
        let d = chain(3);
        let p = |i : usize, j : usize| Product::new(d[i].clone(), d[j].clone());
        assert!(p(0, 2) < p(1, 0));
        assert!(P::in_same_orbit(&BTreeSet::from([p(0, 1), p(1, 0)]), &BTreeSet::from([p(0, 2), p(2, 0)])));
        assert!(!P::in_same_orbit(&BTreeSet::from([p(0, 1), p(1, 0)]), &BTreeSet::from([p(0, 0), p(1, 1)])));
        // The set test agrees with the tuple test on sorted sets.
        let points : Vec<P> = (0..3).flat_map(|i| (0..3).map(move |j| (i, j))).map(|(i, j)| p(i, j)).collect();
        let sets : Vec<BTreeSet<P>> = (1..=3).flat_map(|k| points.iter().cloned().combinations(k)).map(|c| c.into_iter().collect()).collect();
        for s in &sets {
            for t in &sets {
                let (a, b) : (Vec<P>, Vec<P>) = (s.iter().cloned().collect(), t.iter().cloned().collect());
                assert_eq!(P::in_same_orbit(s, t), <P as Atoms>::tuples_in_same_orbit(&a, &b), "{s:?} {t:?}");
            }
        }
        // The relations of the factors and the equivalences.
        let signature = &P::theory().signature;
        let less_2 = signature.relation("less_2").unwrap();
        let same_1 = signature.relation("same_1").unwrap();
        assert!(P::holds(less_2, &[p(1, 0), p(0, 1)]));
        assert!(P::holds(same_1, &[p(1, 0), p(1, 2)]));
        assert!(!P::holds(same_1, &[p(1, 0), p(2, 0)]));
    }

    /// Colours times symbolic atoms: the coloured atoms over (Q, <).
    #[test]
    fn coloured_symbolic_atoms() {
        let d = chain(3);
        let y = |c : Colour, i : usize| Product::new(c, d[i].clone());
        let universe : Vec<Product<Colour, D>> = [Colour::Low, Colour::High].into_iter().cartesian_product(0..3).map(|(c, i)| y(c, i)).collect();
        let sets = [
            BTreeSet::from([y(Colour::Low, 0)]),
            BTreeSet::from([y(Colour::Low, 0), y(Colour::High, 0)]),
            BTreeSet::from([y(Colour::Low, 0), y(Colour::High, 1)]),
        ];
        for first in &sets {
            for second in &sets[..2] {
                check(first, second, &universe);
            }
        }
    }
}
