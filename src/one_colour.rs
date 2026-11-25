//! A direct implementation of the one-colour trick for finitely many variables,
//! without the orbit framework (compare `equivariant::one_colour_groebner_basis`
//! with the variables of `trivial.rs`, which computes the same kind of basis).
//!
//! For an ideal I of K[X], it computes a basis B such that, for every set V of
//! variables, the elements of B in K[X_V] form a Gröbner basis of I ∩ K[X_V].
//! This is proved in the section "Correctness of the one-colour variant" of `README.tex`, with
//! and without the criteria below, and the algorithm always stops.
//!
//! A coloured variable is a pair (high, x): `(false, x)` is the low copy of x
//! and `(true, x)` its high copy. Since `false < true`, every high variable is
//! larger than every low variable. The algorithm is the one of
//! `one_colour_groebner_basis`:
//!
//! 1. Every generator h is coloured in the |supp(h)| + 1 ways with at most one
//!    high variable.
//! 2. The S-polynomial of two coloured polynomials is only formed if their
//!    colours are consistent: together they have at most one high variable,
//!    and they do not contain both copies of a variable. Inconsistent pairs are
//!    never created.
//! 3. An S-polynomial is reduced with the support condition: repeatedly, the
//!    largest reducible monomial of f is reduced by an element h with
//!    supp(h) ⊆ supp(f) (as coloured variables) whose leading monomial divides
//!    it.
//! 4. A non-zero remainder r that keeps a high variable is added as it is; if r
//!    has no high variable, it is added with every variable low and with each
//!    one of its variables high.
//!
//! The result is the set of the polynomials with the colours forgotten.
//!
//! The pairs are treated in the order of their creation (first in, first out),
//! as in `one_colour_groebner_basis`, or optionally with the normal strategy
//! (smallest lcm first) or with the smallest domain |supp(f) ∪ supp(g)| first.
//! In the experiments, the normal strategy was often much slower: on one ideal
//! in 4 variables, 300 times slower.
//!
//! Optionally, Buchberger's two criteria are used, adapted to the support
//! condition:
//!
//! - first criterion: if LM(f) and LM(g) are coprime, S(f, g) is skipped. The
//!   standard representation of S(f, g) in this case only uses f and g, with
//!   multipliers in the variables of f and g, so it respects the support
//!   condition;
//! - chain criterion: the pair (f, g) is skipped if some h with LM(h) dividing
//!   lcm(LM(f), LM(g)) and supp(h) ⊆ supp(f) ∪ supp(g) has both pairs (f, h)
//!   and (g, h) already treated. The condition on supp(h) is needed because S(f,
//!   g) is then written with S(f, h) and S(g, h), which contain the variables of
//!   h. It also ensures that (f, h) and (g, h) have consistent colours, so that
//!   these pairs exist.

use std::collections::BTreeSet;
use std::hash::Hash;
use std::ops::{AddAssign, Div, Neg, Sub};
use num_traits::{ConstOne, One, Zero};
use crate::counters;
use crate::mon::{Monomial, Polynomial};

/// A coloured variable: `(true, x)` is high, `(false, x)` is low.
type Coloured<X> = (bool, X);

/// An element of the coloured basis, with data computed once.
struct Element<F, X : Ord + Hash + Clone> {
    poly : Polynomial<F, Coloured<X>>,
    leading : Monomial<Coloured<X>>,
    support : BTreeSet<Coloured<X>>,
    /// The variable whose high copy occurs, if any.
    high : Option<X>,
    /// The variables whose low copies occur.
    lows : BTreeSet<X>,
}

impl Default for Options {
    /// The adapted criteria, and the order of creation, which was much faster
    /// than the normal strategy in the experiments.
    fn default() -> Self {
        Options { criteria : true, strategy : Strategy::Creation }
    }
}

impl<F : AddAssign + Default + Eq + Zero + ConstOne + Clone, X : Ord + Hash + Clone> Element<F, X> {
    fn new(poly : Polynomial<F, Coloured<X>>) -> Self {
        let support = poly.domain();
        let high = support.iter().find(|(h, _)| *h).map(|(_, x)| x.clone());
        let lows = support.iter().filter(|(h, _)| !*h).map(|(_, x)| x.clone()).collect();
        Element { leading : poly.leading_mon(), poly, support, high, lows }
    }
}

/// Whether two coloured polynomials have consistent colours. Each of them has
/// consistent colours on its own.
fn consistent<F, X : Ord + Hash + Clone>(a : &Element<F, X>, b : &Element<F, X>) -> bool {
    match (&a.high, &b.high) {
        (None, None) => true,
        (Some(x), None) => !b.lows.contains(x),
        (None, Some(y)) => !a.lows.contains(y),
        (Some(x), Some(y)) => x == y,
    }
}

/// The colourings of a polynomial with at most one high variable: every
/// variable low, and each one of its variables high.
fn colourings<F : AddAssign + Default + Eq + Zero + ConstOne + Clone, X : Ord + Hash + Clone>(h : &Polynomial<F, X>) -> Vec<Polynomial<F, Coloured<X>>> {
    let mut list = vec![h.map_variables(|x| (false, x.clone()))];
    for y in h.domain() {
        list.push(h.map_variables(|x| (*x == y, x.clone())));
    }
    list
}

/// The order in which the pairs are treated. The algorithm stops when every
/// pair has been treated or skipped, whatever the order, and its correctness
/// proof does not depend on the order (`README.tex`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy {
    /// The order in which the pairs were created (first in, first out), as in
    /// `equivariant::one_colour_groebner_basis`.
    Creation,
    /// The normal strategy: smallest lcm of the leading monomials first.
    Normal,
    /// Smallest domain |supp(f) ∪ supp(g)| first.
    SmallestDomain,
}

/// The options of `one_colour_basis`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Options {
    /// Whether the adapted Buchberger criteria are used.
    pub criteria : bool,
    /// The order in which the pairs are treated; ties are broken by the order
    /// of creation.
    pub strategy : Strategy,
}

/// The key of a pending pair (i, j): domain size, lcm, number of creation, i, j.
type PairKey<X> = (usize, Monomial<Coloured<X>>, u64, usize, usize);

/// The basis being computed: its elements, the polynomials already in it, and
/// the pending pairs (with the set `members` for the chain criterion). A pair
/// is stored with a key: its domain size with the smallest domain first (0
/// otherwise), then its lcm with the normal strategy (1 otherwise), then its
/// number of creation.
struct State<F, X : Ord + Hash + Clone> {
    basis : Vec<Element<F, X>>,
    seen : BTreeSet<Polynomial<F, Coloured<X>>>,
    queue : BTreeSet<PairKey<X>>,
    members : BTreeSet<(usize, usize)>,
    created : u64,
    strategy : Strategy,
}

impl<F, X> State<F, X>
where
    F : AddAssign + Clone + ConstOne + Default + Zero + Eq + Div<Output = F> + Neg<Output = F> + Sub + Ord,
    X : Ord + Hash + Clone,
{
    /// Adds `p` if it is new, with its consistent pairs; returns whether it was new.
    fn add(&mut self, p : Polynomial<F, Coloured<X>>) -> bool {
        if self.seen.contains(&p) {
            return false;
        }
        self.seen.insert(p.clone());
        let e = Element::new(p);
        let k = self.basis.len();
        for (i, b) in self.basis.iter().enumerate() {
            if consistent(b, &e) {
                let domain = match self.strategy {
                    Strategy::SmallestDomain => b.support.union(&e.support).count(),
                    _ => 0,
                };
                let lcm = match self.strategy {
                    Strategy::Normal => b.leading.lcm(&e.leading),
                    _ => Monomial::one(),
                };
                self.queue.insert((domain, lcm, self.created, i, k));
                self.created += 1;
                self.members.insert((i, k));
            }
        }
        self.basis.push(e);
        true
    }

    /// The chain criterion adapted to the support condition, for the pair (i, j)
    /// already removed from `members`.
    fn chain(&self, i : usize, j : usize, lcm : &Monomial<Coloured<X>>) -> bool {
        let pending = |a : usize, b : usize| self.members.contains(&(a.min(b), a.max(b)));
        self.basis.iter().enumerate().any(|(k, h)| {
            k != i
                && k != j
                && lcm.is_divisible_by(&h.leading)
                && h.support.iter().all(|y| self.basis[i].support.contains(y) || self.basis[j].support.contains(y))
                && !pending(i, k)
                && !pending(j, k)
        })
    }

    /// The normal form of `f` with the support condition: repeatedly, the largest
    /// reducible monomial is reduced by an element h with supp(h) ⊆ supp(f).
    fn normal_form(&self, f : Polynomial<F, Coloured<X>>) -> Polynomial<F, Coloured<X>> {
        let mut f = f;
        loop {
            let support = f.domain();
            let step = f.monomials().rev().find_map(|m| {
                self.basis
                    .iter()
                    .find(|h| m.is_divisible_by(&h.leading) && h.support.is_subset(&support))
                    .map(|h| (m.clone(), h))
            });
            match step {
                Some((m, h)) => f = f.reduce_term_by(&m, &h.poly),
                None => return f,
            }
        }
    }
}

/// The one-colour trick for the ideal generated by `generators`, without the
/// orbit framework. Returns the polynomials of the coloured basis with the
/// colours forgotten, made monic, without repetitions and sorted.
pub fn one_colour_basis<F, X>(generators : Vec<Polynomial<F, X>>, options : Options) -> Vec<Polynomial<F, X>>
where
    F : AddAssign + Clone + ConstOne + Default + Zero + Eq + Div<Output = F> + Neg<Output = F> + Sub + Ord,
    X : Ord + Hash + Clone,
{
    let forgotten : BTreeSet<Polynomial<F, X>> = coloured_basis(generators, options)
        .iter()
        .map(|p| p.map_variables(|(_, x)| x.clone()))
        .filter(|p| !p.is_zero())
        .map(|p| p.monic())
        .collect();
    forgotten.into_iter().collect()
}

/// The coloured basis computed by `one_colour_basis`, before the colours are
/// forgotten.
fn coloured_basis<F, X>(generators : Vec<Polynomial<F, X>>, options : Options) -> Vec<Polynomial<F, Coloured<X>>>
where
    F : AddAssign + Clone + ConstOne + Default + Zero + Eq + Div<Output = F> + Neg<Output = F> + Sub + Ord,
    X : Ord + Hash + Clone,
{
    let mut state = State {
        basis : Vec::new(),
        seen : BTreeSet::new(),
        queue : BTreeSet::new(),
        members : BTreeSet::new(),
        created : 0,
        strategy : options.strategy,
    };
    for g in generators {
        if !g.is_zero() {
            for c in colourings(&g.monic()) {
                state.add(c);
            }
        }
    }
    while let Some((_, _, _, i, j)) = state.queue.pop_first() {
        state.members.remove(&(i, j));
        if options.criteria {
            let lcm = state.basis[i].leading.lcm(&state.basis[j].leading);
            if lcm == state.basis[i].leading.clone() * state.basis[j].leading.clone() {
                continue;
            }
            if state.chain(i, j, &lcm) {
                continue;
            }
        }
        let s = state.basis[i].poly.clone().syzygy(&state.basis[j].poly);
        let r = state.normal_form(s);
        if r.is_zero() {
            continue;
        }
        let r = r.monic();
        let new = if r.domain().iter().any(|(h, _)| *h) {
            vec![r]
        } else {
            colourings(&r.map_variables(|(_, x)| x.clone()))
        };
        for p in new {
            if state.add(p) {
                counters::count_added();
            }
        }
    }
    state.basis.into_iter().map(|e| e.poly).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ideal::{buchberger, elimination_ideal};
    use num_rational::BigRational as Q;

    type P = Polynomial<Q, u32>;

    fn x(i : u32) -> P {
        Polynomial::var(i)
    }

    /// The number of sets V of the variables 1, ..., n for which the elements of
    /// `basis` in K[X_V] do not form a Gröbner basis of I ∩ K[X_V].
    fn failing_sets(generators : &[P], basis : &[P], n : u32) -> usize {
        (0..1u32 << n)
            .map(|mask| (1..=n).filter(|i| mask >> (i - 1) & 1 == 1).collect::<BTreeSet<u32>>())
            .filter(|v| {
                let inside : Vec<&P> = basis.iter().filter(|h| h.domain().is_subset(v)).collect();
                !elimination_ideal(generators, v).iter().all(|e| inside.iter().any(|h| e.leading_mon().is_divisible_by(&h.leading_mon())))
            })
            .count()
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

    fn all_options() -> Vec<Options> {
        let strategies = [Strategy::Creation, Strategy::Normal, Strategy::SmallestDomain];
        [false, true].into_iter().flat_map(|criteria| strategies.map(|strategy| Options { criteria, strategy })).collect()
    }

    /// The options used on random ideals: the order of creation with and
    /// without the criteria, and the smallest domain first with the criteria.
    /// The other strategies can be very slow on some of these ideals (the
    /// normal strategy, and the smallest domain first without the criteria).
    fn creation_order_options() -> Vec<Options> {
        vec![
            Options { criteria : false, strategy : Strategy::Creation },
            Options { criteria : true, strategy : Strategy::Creation },
            Options { criteria : true, strategy : Strategy::SmallestDomain },
        ]
    }

    #[test]
    fn examples() {
        // <x2 - x1, x1^2>: x2^2 is in the ideal, and the reduced basis misses it.
        let generators = vec![x(2) - x(1), x(1) * x(1)];
        assert_eq!(failing_sets(&generators, &buchberger(generators.clone()), 2), 1);
        for options in all_options() {
            let basis = one_colour_basis(generators.clone(), options);
            assert!(basis.contains(&(x(2) * x(2))));
            assert_eq!(failing_sets(&generators, &basis, 2), 0);
        }
        // The twisted cubic: the ordinary basis misses x3^2 - x2^3.
        let generators = vec![x(2) - x(1) * x(1), x(3) - x(1) * x(1) * x(1)];
        for options in all_options() {
            assert_eq!(failing_sets(&generators, &one_colour_basis(generators.clone(), options), 3), 0);
        }
    }

    /// The worlds of a coloured basis B: for no variable, the elements without a
    /// high variable; for a variable z, the elements whose only high variable is
    /// z and that do not contain the low copy of z. The lemmas of the proof of
    /// correctness imply that the elements of a world, with the colours
    /// forgotten, form a Gröbner basis of the ideal for the order of the world:
    /// the original order for no variable, and the order in which z is the
    /// largest variable for z. This test checks that consequence.
    fn check_worlds(generators : &[P], options : Options) {
        let coloured = coloured_basis(generators.to_vec(), options);
        let vars : BTreeSet<u32> = generators.iter().flat_map(|g| g.domain()).collect();
        let worlds = std::iter::once(None).chain(vars.iter().map(|z| Some(*z)));
        for world in worlds {
            // In the world, a variable x becomes (x == z, x), so z is the largest.
            let tag = |x : &u32| (Some(*x) == world, *x);
            let in_world : Vec<Polynomial<Q, (bool, u32)>> = coloured
                .iter()
                .filter(|p| p.domain().iter().all(|(high, x)| *high == (Some(*x) == world)))
                .map(|p| p.map_variables(|(_, x)| tag(x)))
                .collect();
            let reference = buchberger(generators.iter().map(|g| g.map_variables(tag)).collect());
            for e in &reference {
                assert!(
                    in_world.iter().any(|h| e.leading_mon().is_divisible_by(&h.leading_mon())),
                    "world {world:?}: no element of the world divides a leading monomial of the reference basis"
                );
            }
        }
    }

    #[test]
    fn worlds_are_groebner_bases() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        for _ in 0..10 {
            let generators : Vec<P> = (0..3)
                .map(|_| {
                    (0..3).fold(P::zero(), |f, _| {
                        let mut t = Polynomial::constant(Q::from_integer([-2, -1, 1, 2][rng.below(4) as usize].into()));
                        for _ in 0..1 + rng.below(2) {
                            t = t * x(1 + rng.below(3) as u32);
                        }
                        f + t
                    })
                })
                .collect();
            for options in creation_order_options() {
                check_worlds(&generators, options);
            }
        }
    }

    #[test]
    fn random_ideals() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        // In 4 variables, some random ideals already need minutes for the 16
        // elimination ideals of the check, so the test uses 3 variables.
        for _ in 0..10 {
            let n = 3;
            let generators : Vec<P> = (0..3)
                .map(|_| {
                    (0..3).fold(P::zero(), |f, _| {
                        let mut t = Polynomial::constant(Q::from_integer([-2, -1, 1, 2][rng.below(4) as usize].into()));
                        for _ in 0..1 + rng.below(2) {
                            t = t * x(1 + rng.below(n as u64) as u32);
                        }
                        f + t
                    })
                })
                .collect();
            for options in creation_order_options() {
                let basis = one_colour_basis(generators.clone(), options);
                assert_eq!(failing_sets(&generators, &basis, n), 0, "{options:?}, generators {generators:?}");
                // Every element is in the ideal.
                let reduced = buchberger(generators.clone());
                assert!(basis.iter().all(|h| h.clone().normal_form(&reduced).is_zero()));
            }
        }
    }
}
