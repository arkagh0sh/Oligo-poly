//! Atoms of the universal countable dense meet-tree with a lexicographic order,
//! written T_< in A. Ghosh and A. Lopez, Computability of equivariant Gröbner
//! bases (2025), Remark 16.
//!
//! The model. An atom is a sequence (h_1, k_1, h_2, k_2, ..., k_{n-1}, h_n) of
//! rational numbers with n >= 1 and every k_i non-zero. It is the point reached
//! by going up the trunk to the height h_1, taking there the branch with label
//! k_1, going up this branch to the height h_2, and so on. At every point there
//! is one direction for each rational label: the label 0 means going further up
//! the same branch, and a non-zero label k means taking the branch k. Every
//! branch is a copy of (Q, <), so it has no lowest point.
//!
//! - Tree order: x <= y if x without its last height is a prefix of y, and the
//!   last height of x is at most the height of y at that position.
//! - Meet: x ∧ y is the largest point below x and y.
//! - Lexicographic order (`Ord`): x comes before y if x < y in the tree order,
//!   or if x and y are incomparable and, at the point x ∧ y, the direction of x
//!   has a smaller label than the direction of y.
//!
//! This model is a countable dense meet-tree without a lowest point, in which
//! every point has a dense set of directions without a first or a last one, and
//! every direction contains points arbitrarily close to the branching point. It
//! has the extension property of the Fraïssé class of finite meet-trees with a
//! lexicographic order (see `one_point_extensions`), so it is the Fraïssé limit
//! T_< of that class. In particular, it is homogeneous.

use rug::Rational;
use std::cmp::Ordering;
use std::collections::BTreeSet;
use std::fmt::{Debug, Display, Formatter, Result};
use std::sync::OnceLock;
use crate::atoms::{AtomsWithOrd, HomogeneousStructure, Orbit, SetPairOrbit, Structure};
use crate::elements_with_atoms::{ElementsWithAtoms, PartialAut};
use crate::logic::{Signature, Theory, LINEAR_ORDER, TREE_AXIOMS};

/// A point of the dense meet-tree. The sequence is private, so programs can only
/// use the tree order, the meet and the lexicographic order.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Tree {
    seq : Vec<Rational>,
}

impl Tree {
    /// The point (h_1, k_1, ..., k_{n-1}, h_n). Panics if the length of `seq` is
    /// even or if a branch label k_i is zero.
    pub fn new(seq : Vec<Rational>) -> Tree {
        assert!(seq.len() % 2 == 1, "a point is given by an odd number of rationals");
        assert!(seq.iter().skip(1).step_by(2).all(|k| *k != 0), "branch labels must be non-zero");
        Tree { seq }
    }

    /// The point given by a sequence of integers, for tests and examples.
    pub fn from_ints(seq : &[i64]) -> Tree {
        Tree::new(seq.iter().map(|&i| Rational::from(i)).collect())
    }

    /// The tree order: whether `self` <= `other`.
    pub fn is_below(&self, other : &Tree) -> bool {
        let l = self.seq.len();
        l <= other.seq.len() && self.seq[..l - 1] == other.seq[..l - 1] && self.seq[l - 1] <= other.seq[l - 1]
    }

    /// The meet: the largest point below `self` and `other`.
    pub fn meet(&self, other : &Tree) -> Tree {
        let (x, y) = (&self.seq, &other.seq);
        let p = x.iter().zip(y.iter()).take_while(|(a, b)| a == b).count();
        if p == x.len() {
            // x is a prefix of y, so y branches off at x (or y = x).
            self.clone()
        } else if p == y.len() {
            other.clone()
        } else if p % 2 == 0 {
            // The heights differ on a common branch: the meet is the lower one.
            let mut seq = x[..p].to_vec();
            seq.push(x[p].clone().min(y[p].clone()));
            Tree { seq }
        } else {
            // x and y take different branches at the same point.
            Tree { seq : x[..p].to_vec() }
        }
    }

    /// The label of the direction of `self` at a point `u` strictly below it.
    fn direction(&self, u : &Tree) -> Rational {
        let l = u.seq.len();
        if self.seq[l - 1] > u.seq[l - 1] {
            Rational::new()
        } else {
            self.seq[l].clone()
        }
    }

    /// A point above `self` in the direction with the given label.
    fn above_in_direction(&self, label : &Rational) -> Tree {
        let mut seq = self.seq.clone();
        if *label == 0 {
            let last = seq.len() - 1;
            seq[last] += 1;
        } else {
            seq.push(label.clone());
            seq.push(Rational::new());
        }
        Tree { seq }
    }

    /// A point strictly between `self` and a point `upper` strictly above it.
    fn between(&self, upper : &Tree) -> Tree {
        let l = self.seq.len();
        let (h, hu) = (&self.seq[l - 1], &upper.seq[l - 1]);
        let mut seq = self.seq.clone();
        if hu > h {
            seq[l - 1] = Rational::from(h + hu) / 2;
        } else {
            // `upper` takes the branch upper[l] at `self`, and goes up to upper[l + 1].
            seq.push(upper.seq[l].clone());
            seq.push(Rational::from(&upper.seq[l + 1] - 1));
        }
        Tree { seq }
    }

    /// A point strictly below `self`.
    fn below(&self) -> Tree {
        Tree { seq : vec![Rational::from(&self.seq[0] - 1)] }
    }
}

impl Ord for Tree {
    fn cmp(&self, other : &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else if self.is_below(other) {
            Ordering::Less
        } else if other.is_below(self) {
            Ordering::Greater
        } else {
            let m = self.meet(other);
            self.direction(&m).cmp(&other.direction(&m))
        }
    }
}

impl PartialOrd for Tree {
    fn partial_cmp(&self, other : &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Display for Tree {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        let parts : Vec<String> = self.seq.iter().map(|q| q.to_string()).collect();
        write!(f, "t({})", parts.join(","))
    }
}

impl Debug for Tree {
    fn fmt(&self, f : &mut Formatter<'_>) -> Result {
        write!(f, "{self}")
    }
}

/// The meet-closure of a finite set: the meets a ∧ b for a, b in the set. It is
/// closed under meets, because the points below a form a chain, so a meet of
/// several points is the smallest of their pairwise meets.
fn closure(set : &BTreeSet<Tree>) -> BTreeSet<Tree> {
    set.iter().flat_map(|a| set.iter().map(move |b| a.meet(b))).collect()
}

/// The largest point of `c` strictly below `u` in the tree order, if any. The
/// points below `u` form a chain, on which the two orders agree.
fn parent(c : &BTreeSet<Tree>, u : &Tree) -> Option<Tree> {
    c.iter().filter(|p| *p != u && p.is_below(u)).max().cloned()
}

/// One representative b of every orbit of points under the automorphisms that
/// fix the finite set `x`. These automorphisms fix the meet-closure C of `x`.
/// There are 6|C| - 1 orbits:
/// - b is a point of C (|C| orbits);
/// - b is above a point u of C, in a new direction placed before, between or
///   after the directions of the children of u in C (2|C| - 1 orbits);
/// - for a point u of C, b is on the edge from the parent of u in C to u (or
///   below u if u is the root of C), or b is on a new branch from a point w of
///   this edge, before or after the direction of u at w (3|C| orbits).
///
/// The lexicographic order of the new point with respect to C only depends on
/// these choices, so the extension property of T_< holds: these are all the
/// ways to add a point to a finite meet-tree with a lexicographic order.
pub fn one_point_extensions(x : &BTreeSet<Tree>) -> Vec<Tree> {
    let c = closure(x);
    let mut points : Vec<Tree> = c.iter().cloned().collect();
    for u in &c {
        let mut labels : Vec<Rational> = c
            .iter()
            .filter(|v| *v != u && u.is_below(v) && parent(&c, v).as_ref() == Some(u))
            .map(|v| v.direction(u))
            .collect();
        labels.sort();
        match (labels.first(), labels.last()) {
            (Some(first), Some(last)) => {
                points.push(u.above_in_direction(&Rational::from(first - 1)));
                for w in labels.windows(2) {
                    points.push(u.above_in_direction(&(Rational::from(&w[0] + &w[1]) / 2)));
                }
                points.push(u.above_in_direction(&Rational::from(last + 1)));
            }
            _ => points.push(u.above_in_direction(&Rational::new())),
        }
        let w = match parent(&c, u) {
            Some(p) => p.between(u),
            None => u.below(),
        };
        let d = u.direction(&w);
        points.push(w.above_in_direction(&Rational::from(&d - 1)));
        points.push(w.above_in_direction(&Rational::from(&d + 1)));
        points.push(w);
    }
    points
}

/// Whether the increasing bijection from the sorted list `first` onto the sorted
/// list `second` preserves the relation a ∧ b <= c.
fn same_type(first : &[Tree], second : &[Tree]) -> bool {
    let n = first.len();
    if n != second.len() {
        return false;
    }
    for i in 0..n {
        for j in i..n {
            let (m, m2) = (first[i].meet(&first[j]), second[i].meet(&second[j]));
            for l in 0..n {
                if m.is_below(&first[l]) != m2.is_below(&second[l]) {
                    return false;
                }
            }
        }
    }
    true
}

/// Extends `chosen` (an increasing list) by points greater than its last point,
/// in all ways up to the automorphisms that fix `fixed` and `chosen`, such that
/// the result has the type of `target`.
fn extend(fixed : &BTreeSet<Tree>, chosen : &mut Vec<Tree>, target : &[Tree], out : &mut Vec<BTreeSet<Tree>>) {
    if chosen.len() == target.len() {
        out.push(chosen.iter().cloned().collect());
        return;
    }
    let x : BTreeSet<Tree> = fixed.iter().chain(chosen.iter()).cloned().collect();
    for b in one_point_extensions(&x) {
        if chosen.last().is_some_and(|last| b <= *last) {
            continue;
        }
        chosen.push(b);
        if same_type(chosen, &target[..chosen.len()]) {
            extend(fixed, chosen, target, out);
        }
        chosen.pop();
    }
}

/// T_< as a structure: the lexicographic order `<`, the tree order `le` and the
/// meet `meet`.
impl Structure for Tree {
    fn theory() -> &'static Theory {
        static THEORY : OnceLock<Theory> = OnceLock::new();
        THEORY.get_or_init(|| {
            let signature = Signature::new(&[("<", 2), ("le", 2)], &[("meet", 2)]);
            Theory::new(signature, &[&LINEAR_ORDER[..], &TREE_AXIOMS[..]].concat()).unwrap()
        })
    }

    fn holds(r : usize, args : &[Self]) -> bool {
        match r {
            0 => args[0] < args[1],
            1 => args[0].is_below(&args[1]),
            _ => panic!("T_< has two relations"),
        }
    }

    fn apply(f : usize, args : &[Self]) -> Self {
        assert_eq!(f, 0, "T_< has one function");
        args[0].meet(&args[1])
    }
}

/// T_< is homogeneous: it is the Fraïssé limit of the finite meet-trees with a
/// lexicographic order (see `README.tex`).
impl HomogeneousStructure for Tree {}

impl AtomsWithOrd for Tree {

    /// Faster than the default, and agrees with it (see the tests).
    ///
    /// Two finite sets S and T are in the same orbit if and only if the
    /// increasing bijection f from S onto T satisfies: a ∧ b <= c if and only if
    /// f(a) ∧ f(b) <= f(c), for all a, b, c in S. Indeed, this relation
    /// determines the order between meets (a ∧ b <= c ∧ d if and only if
    /// a ∧ b <= c and a ∧ b <= d), so f extends to an isomorphism of the
    /// meet-closures with their lexicographic orders, and T_< is homogeneous.
    fn in_same_orbit(first : &BTreeSet<Self>, second : &BTreeSet<Self>) -> bool {
        let first : Vec<Tree> = first.iter().cloned().collect();
        let second : Vec<Tree> = second.iter().cloned().collect();
        same_type(&first, &second)
    }

    /// Every orbit of pairs contains a pair (first, T'), and two such pairs are in
    /// the same orbit if and only if an automorphism fixing `first` maps one T' to
    /// the other. We build T' point by point, in increasing order, choosing each
    /// new point among the representatives of `one_point_extensions`. Each orbit
    /// is obtained exactly once.
    fn orbits_in_product(first : &BTreeSet<Self>, second : &BTreeSet<Self>)
        -> Vec<SetPairOrbit<Self>> {
        let target : Vec<Tree> = second.iter().cloned().collect();
        let mut out = Vec::new();
        extend(first, &mut Vec::new(), &target, &mut out);
        out.into_iter().map(|t| Orbit::new((first.clone(), t))).collect()
    }
}

/// An atom is an element with atoms, with support {a}.
impl ElementsWithAtoms<Tree> for Tree {
    fn support(&self) -> BTreeSet<Tree> {
        BTreeSet::from([self.clone()])
    }

    fn apply_paut(&self, paut : &PartialAut<Tree>) -> Self {
        paut.apply(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;
    use std::collections::HashSet;

    fn t(seq : &[i64]) -> Tree {
        Tree::from_ints(seq)
    }

    /// The points with at most `levels` levels, heights in `heights` and labels
    /// in {-1, 1}.
    fn pool(levels : usize, heights : &[i64]) -> Vec<Tree> {
        pool_with_labels(levels, heights, &[-1, 1])
    }

    /// The points with at most `levels` levels, heights in `heights` and labels
    /// in `labels`.
    fn pool_with_labels(levels : usize, heights : &[i64], labels : &[i64]) -> Vec<Tree> {
        let mut layer : Vec<Vec<i64>> = heights.iter().map(|&h| vec![h]).collect();
        let mut all = layer.clone();
        for _ in 1..levels {
            layer = layer
                .iter()
                .flat_map(|s| labels.iter().flat_map(move |&k| heights.iter().map(move |&h| {
                    let mut s = s.clone();
                    s.push(k);
                    s.push(h);
                    s
                })))
                .collect();
            all.extend(layer.iter().cloned());
        }
        all.iter().map(|s| t(s)).collect()
    }

    #[test]
    fn tree_order_meet_and_lexicographic_order() {
        let points = pool(3, &[0, 1]);
        for x in &points {
            for y in &points {
                let m = x.meet(y);
                assert!(m.is_below(x) && m.is_below(y));
                assert_eq!(x.is_below(y) && y.is_below(x), x == y);
                // (L1) the lexicographic order extends the tree order.
                if x.is_below(y) {
                    assert!(x <= y);
                }
                for z in &points {
                    // The meet is the largest lower bound.
                    if z.is_below(x) && z.is_below(y) {
                        assert!(z.is_below(&m));
                    }
                    // The points below x form a chain.
                    if y.is_below(x) && z.is_below(x) {
                        assert!(y.is_below(z) || z.is_below(y));
                    }
                    // The tree order is transitive.
                    if x.is_below(y) && y.is_below(z) {
                        assert!(x.is_below(z));
                    }
                    // (L2) the points above x form an interval of the
                    // lexicographic order, which is transitive.
                    if x.is_below(y) && x.is_below(z) {
                        for w in &points {
                            if y < w && w < z {
                                assert!(x.is_below(w));
                            }
                        }
                    }
                    if x < y && y < z {
                        assert!(x < z);
                    }
                }
            }
        }
    }

    /// The relation a ∧ b <= c on a sorted list, as a key: two sets are in the same
    /// orbit if and only if their keys are equal.
    fn type_key(set : &[Tree]) -> Vec<bool> {
        let n = set.len();
        let mut key = Vec::new();
        for i in 0..n {
            for j in i..n {
                let m = set[i].meet(&set[j]);
                key.extend(set.iter().map(|c| m.is_below(c)));
            }
        }
        key
    }

    /// The number of orbits of k-element sets is the number of plane trees with k
    /// marked nodes in which every unmarked node has at least two children:
    /// 1, 2, 8, 40 for k = 1, 2, 3, 4. Its generating function F satisfies
    /// F = x / (1 - F) + F^2 / (1 - F), that is, F = x + 2 F^2.
    #[test]
    fn number_of_orbits_of_sets() {
        // Some orbits of 4-element sets need a point with four directions.
        let mut points = pool(3, &[0, 1]);
        points.extend(pool_with_labels(2, &[0, 1], &[-1, 1, 2]));
        let points : Vec<Tree> = points.into_iter().unique().collect();
        for (k, expected) in [(1, 1), (2, 2), (3, 8), (4, 40)] {
            let keys : HashSet<Vec<bool>> = points.iter().cloned().combinations(k).map(|s| type_key(&s.into_iter().sorted().collect::<Vec<_>>())).collect();
            assert_eq!(keys.len(), expected, "k = {k}");
        }
        assert!(Tree::in_same_orbit(&BTreeSet::from([t(&[0]), t(&[1])]), &BTreeSet::from([t(&[0, -1, 0]), t(&[0, -1, 5])])));
        assert!(!Tree::in_same_orbit(&BTreeSet::from([t(&[0]), t(&[1])]), &BTreeSet::from([t(&[0, -1, 0]), t(&[1])])));
    }

    #[test]
    fn one_point_extensions_are_complete_and_distinct() {
        let points = pool(3, &[0, 1]);
        for x in [vec![t(&[0])], vec![t(&[0]), t(&[1])], vec![t(&[0, -1, 0]), t(&[1])], vec![t(&[0, -1, 0]), t(&[0, 1, 0]), t(&[1])]] {
            let set : BTreeSet<Tree> = x.iter().cloned().collect();
            let c = closure(&set);
            let ext = one_point_extensions(&set);
            assert_eq!(ext.len(), 6 * c.len() - 1);
            // The orbit of a point b over x is the type of the list x, b.
            let key = |b : &Tree| {
                let mut s : Vec<Tree> = x.clone();
                s.push(b.clone());
                let sorted : Vec<Tree> = s.iter().cloned().sorted().collect();
                let positions : Vec<usize> = s.iter().map(|p| sorted.iter().position(|q| q == p).unwrap()).collect();
                (type_key(&sorted), positions)
            };
            let found : HashSet<_> = ext.iter().map(key).collect();
            assert_eq!(found.len(), ext.len(), "two representatives of the same orbit over {x:?}");
            // Every point of the pool is in the orbit of a representative. (The pool
            // does not realise every orbit, so this checks only one inclusion.)
            for b in &points {
                assert!(found.contains(&key(b)), "{b} over {x:?}");
            }
        }
    }

    /// One representative of each orbit of k-element sets, found in a pool that
    /// realises all of them for k <= 3 (see `number_of_orbits_of_sets`).
    fn set_types(k : usize) -> Vec<BTreeSet<Tree>> {
        let mut keys = HashSet::new();
        pool(3, &[0, 1])
            .into_iter()
            .combinations(k)
            .map(|c| c.into_iter().sorted().collect::<Vec<Tree>>())
            .filter(|c| keys.insert(type_key(c)))
            .map(|c| c.into_iter().collect())
            .collect()
    }

    /// The orbits of pairs (S, T) with |S| = n and |T| = m correspond to the plane
    /// trees of `number_of_orbits_of_sets` with k marked nodes, each labelled S, T
    /// or both, with n labels S or both and m labels T or both. So their number is
    /// the sum over k of c_k k! / ((k - m)! (k - n)! (n + m - k)!), where c_k is the
    /// number of orbits of k-element sets. We check that `orbits_in_product` lists
    /// that many pairwise distinct orbits of pairs, over all orbits of S and T.
    #[test]
    fn orbits_in_product_are_complete_and_distinct() {
        // The pairs of points: equal, a < b, b < a, and incomparable in two orders.
        assert_eq!(Tree::orbits_in_product(&BTreeSet::from([t(&[0])]), &BTreeSet::from([t(&[0])])).len(), 5);
        let c : [usize; 7] = [0, 1, 2, 8, 40, 224, 1344];
        let factorial = |k : usize| -> usize { (1..=k).product() };
        let pair_key = |p : &(BTreeSet<Tree>, BTreeSet<Tree>)| {
            let union : Vec<Tree> = p.0.union(&p.1).cloned().collect();
            let marks : Vec<(bool, bool)> = union.iter().map(|a| (p.0.contains(a), p.1.contains(a))).collect();
            (type_key(&union), marks)
        };
        for (n, m) in [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1), (2, 3), (3, 2)] {
            let expected : usize = (n.max(m)..=n + m)
                .map(|k| c[k] * factorial(k) / (factorial(k - m) * factorial(k - n) * factorial(n + m - k)))
                .sum();
            let mut total = 0;
            for s in set_types(n) {
                for t in set_types(m) {
                    let reps = Tree::orbits_in_product(&s, &t);
                    for r in &reps {
                        assert!(r.evaluate(|(a, b)| Tree::in_same_orbit(&s, a) && Tree::in_same_orbit(&t, b)));
                    }
                    let keys : HashSet<_> = reps.iter().map(|r| r.evaluate(pair_key)).collect();
                    assert_eq!(keys.len(), reps.len(), "two representatives of the same orbit");
                    total += reps.len();
                }
            }
            assert_eq!(total, expected, "n = {n}, m = {m}");
        }
    }

    /// The points of the model satisfy the axioms of T_<.
    #[test]
    fn the_model_satisfies_the_axioms() {
        use crate::atoms::satisfies;
        let points = pool(3, &[0, 1]);
        let points : Vec<Tree> = points.into_iter().step_by(2).collect();
        for axiom in &Tree::theory().axioms {
            let k = axiom.variables.len();
            for args in itertools::repeat_n(points.iter().cloned(), k).multi_cartesian_product() {
                assert!(satisfies(&axiom.formula, &args), "{:?} fails at {args:?}", axiom.variables);
            }
        }
    }

    /// The canonical test of homogeneous structures agrees with the test of
    /// `in_same_orbit` for T_<, on sets of a pool of points.
    #[test]
    fn canonical_orbit_test() {
        use crate::atoms::homogeneous_tuples_in_same_orbit;
        let points = pool(3, &[0, 1]);
        let sets : Vec<Vec<Tree>> = (1..=3).flat_map(|k| points.iter().cloned().combinations(k).map(|c| c.into_iter().sorted().collect::<Vec<_>>())).collect();
        let sets : Vec<Vec<Tree>> = sets.into_iter().step_by(7).collect();
        for a in &sets {
            for b in &sets {
                let (sa, sb) : (BTreeSet<Tree>, BTreeSet<Tree>) = (a.iter().cloned().collect(), b.iter().cloned().collect());
                assert_eq!(homogeneous_tuples_in_same_orbit(a, b), Tree::in_same_orbit(&sa, &sb), "{a:?} {b:?}");
            }
        }
    }
}
