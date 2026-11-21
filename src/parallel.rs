//! Two parallel versions of Buchberger's algorithm, which use the same criteria
//! and the same selection strategy as `ideal::buchberger`.
//!
//! - `buchberger_batch`: in each round, the S-polynomials of all pending pairs
//!   are computed and reduced in parallel, and all non-zero remainders are added.
//! - `buchberger_first`: in each round, the pending pairs are taken in the order
//!   of the normal strategy and reduced in parallel, and only the first
//!   S-polynomial in this order that does not reduce to zero is added. The
//!   pairs whose S-polynomials reduced to zero are marked as done, because they
//!   stay reducible to zero when the basis grows; the other computed pairs stay
//!   pending and are reduced again in a later round. With one thread, this is
//!   the sequential algorithm.
//!
//! The pending pairs are kept sorted by the lcm of the leading monomials. In
//! both versions, the criteria are applied to the pending pairs before a round,
//! in this order (in `buchberger_first`, only until a window of 2 * threads
//! pairs is kept). This is correct: a pair is only removed by the chain
//! criterion if the two pairs that it relies on were treated before, and the
//! pairs kept for the round still count as pending. With one thread, no thread
//! is started.
//!
//! Both return the reduced Gröbner basis, so their results are equal to the
//! result of `ideal::buchberger`, and statistics about the computation.

use std::collections::{BTreeMap, BTreeSet};
use std::hash::Hash;
use std::ops::{AddAssign, Div, Neg, Sub};
use std::sync::atomic::{AtomicUsize, Ordering};
use num_traits::{ConstOne, Zero};
use crate::ideal::{chain_criterion, reduce_groebner_basis};
use crate::mon::{Monomial, Polynomial};

/// Statistics about a run of a parallel Buchberger algorithm.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// The number of rounds: in `buchberger_first`, the number of windows of
    /// pairs that were reduced.
    pub rounds : usize,
    /// The number of S-polynomials that were computed and reduced.
    pub reductions : usize,
    /// The number of them that reduced to zero.
    pub zero : usize,
    /// The number of non-zero remainders that were not added: in
    /// `buchberger_first`, those after the first one; in `buchberger_batch`,
    /// those that reduced to zero by the elements added in the same round.
    pub discarded : usize,
}

/// The operations that the algorithms need: those of a field, and sharing
/// between threads.
pub trait ParField : AddAssign + Clone + ConstOne + Default + Zero + Eq + Div<Output = Self> + Neg<Output = Self> + Sub + Ord + Send + Sync {}

impl<F> ParField for F
where
    F : AddAssign + Clone + ConstOne + Default + Zero + Eq + Div<Output = F> + Neg<Output = F> + Sub + Ord + Send + Sync,
{}

/// The pending pairs, sorted by the lcm of the leading monomials of the two
/// polynomials (the normal strategy). The set `members` is the matrix of the
/// pairs whose S-polynomials are not yet known to reduce to zero.
struct PairQueue<X : Ord + Hash + Clone> {
    ordered : BTreeSet<(Monomial<X>, usize, usize)>,
    lcms : BTreeMap<(usize, usize), Monomial<X>>,
    members : BTreeSet<(usize, usize)>,
}

impl<X : Ord + Hash + Clone> PairQueue<X> {
    fn new() -> Self {
        PairQueue { ordered : BTreeSet::new(), lcms : BTreeMap::new(), members : BTreeSet::new() }
    }

    fn insert<F : ParField>(&mut self, i : usize, j : usize, basis : &[Polynomial<F, X>]) {
        let lcm = basis[i].leading_mon().lcm(&basis[j].leading_mon());
        self.ordered.insert((lcm.clone(), i, j));
        self.lcms.insert((i, j), lcm);
        self.members.insert((i, j));
    }

    fn remove(&mut self, (i, j) : (usize, usize)) {
        if let Some(lcm) = self.lcms.remove(&(i, j)) {
            self.ordered.remove(&(lcm, i, j));
            self.members.remove(&(i, j));
        }
    }

    /// Removes the pairs that Buchberger's two criteria discard, going through
    /// the pairs in the order of the normal strategy, until `max` pairs are kept
    /// (all pairs if `max` is `None`), and returns the kept pairs in this order.
    fn next_pairs<F : ParField>(&mut self, basis : &[Polynomial<F, X>], max : Option<usize>) -> Vec<(usize, usize)> {
        let candidates : Vec<(Monomial<X>, usize, usize)> = self.ordered.iter().cloned().collect();
        let mut kept = Vec::new();
        for (lcm, i, j) in candidates {
            if max.is_some_and(|m| kept.len() >= m) {
                break;
            }
            // First criterion: coprime leading monomials.
            if lcm == basis[i].leading_mon() * basis[j].leading_mon() {
                self.remove((i, j));
                continue;
            }
            // Second (chain) criterion, with (i, j) removed as in `ideal::buchberger`.
            self.members.remove(&(i, j));
            let chain = chain_criterion(i, j, &self.members, basis);
            self.members.insert((i, j));
            if chain {
                self.remove((i, j));
                continue;
            }
            kept.push((i, j));
        }
        kept
    }
}

/// The non-zero generators, without repetitions, and the queue of all their pairs.
fn start<F : ParField, X : Ord + Hash + Clone + Send + Sync>(generators : Vec<Polynomial<F, X>>) -> (Vec<Polynomial<F, X>>, PairQueue<X>) {
    let mut basis : Vec<Polynomial<F, X>> = Vec::new();
    for g in generators {
        if !g.is_zero() && !basis.contains(&g) {
            basis.push(g);
        }
    }
    let mut queue = PairQueue::new();
    for j in 0..basis.len() {
        for i in 0..j {
            queue.insert(i, j, &basis);
        }
    }
    (basis, queue)
}

/// Adds `r` to the basis, with its pairs.
fn add<F : ParField, X : Ord + Hash + Clone>(basis : &mut Vec<Polynomial<F, X>>, queue : &mut PairQueue<X>, r : Polynomial<F, X>) {
    let k = basis.len();
    basis.push(r);
    for i in 0..k {
        queue.insert(i, k, basis);
    }
}

/// Reduces the S-polynomials of the `pairs` by `basis` with `threads` threads.
/// Each thread takes the next pair in the list. If `stop_at_first`, no pair is
/// started after the first pair (in the list) whose remainder is non-zero, and
/// every pair before it has been reduced. Returns the positions in the list of
/// the reduced pairs, with their non-zero remainders.
fn reduce_pairs<F : ParField, X : Ord + Hash + Clone + Send + Sync>(
    pairs : &[(usize, usize)],
    basis : &[Polynomial<F, X>],
    threads : usize,
    stop_at_first : bool,
) -> Vec<(usize, Option<Polynomial<F, X>>)> {
    let reduce = |(i, j) : (usize, usize)| -> Option<Polynomial<F, X>> {
        let r = basis[i].clone().syzygy(&basis[j]).normal_form(basis);
        (!r.is_zero()).then_some(r)
    };
    if threads <= 1 {
        // No thread is started: this is the sequential computation.
        let mut out = Vec::new();
        for (index, &pair) in pairs.iter().enumerate() {
            let r = reduce(pair);
            let non_zero = r.is_some();
            out.push((index, r));
            if stop_at_first && non_zero {
                break;
            }
        }
        return out;
    }
    let next = AtomicUsize::new(0);
    let stop = AtomicUsize::new(usize::MAX);
    std::thread::scope(|scope| {
        let workers : Vec<_> = (0..threads.max(1))
            .map(|_| {
                scope.spawn(|| {
                    let mut out = Vec::new();
                    loop {
                        let index = next.fetch_add(1, Ordering::SeqCst);
                        // Indices are taken in increasing order, so when the first
                        // non-zero remainder is at position m, every position below
                        // m was taken before the stop was set, and is reduced.
                        if index >= pairs.len() || (stop_at_first && index > stop.load(Ordering::SeqCst)) {
                            break;
                        }
                        let r = reduce(pairs[index]);
                        if r.is_some() {
                            stop.fetch_min(index, Ordering::SeqCst);
                        }
                        out.push((index, r));
                    }
                    out
                })
            })
            .collect();
        let mut results : Vec<_> = workers.into_iter().flat_map(|w| w.join().unwrap()).collect();
        results.sort_by_key(|(index, _)| *index);
        results
    })
}

/// Buchberger's algorithm in rounds: in each round, all pending S-polynomials
/// are reduced in parallel, and the non-zero remainders are added, after a
/// reduction by the elements added before them in the same round.
pub fn buchberger_batch<F : ParField, X : Ord + Hash + Clone + Send + Sync>(
    generators : Vec<Polynomial<F, X>>,
    threads : usize,
) -> (Vec<Polynomial<F, X>>, Stats) {
    let (mut basis, mut queue) = start(generators);
    let mut stats = Stats::default();
    loop {
        let round = queue.next_pairs(&basis, None);
        if round.is_empty() {
            break;
        }
        stats.rounds += 1;
        for &pair in &round {
            queue.remove(pair);
        }
        for (_, r) in reduce_pairs(&round, &basis, threads, false) {
            stats.reductions += 1;
            match r {
                None => stats.zero += 1,
                Some(r) => {
                    // r is reduced by the basis of the start of the round; reduce it by
                    // the elements added since then.
                    let r = r.normal_form(&basis);
                    if r.is_zero() {
                        stats.discarded += 1;
                    } else {
                        add(&mut basis, &mut queue, r);
                    }
                }
            }
        }
    }
    (reduce_groebner_basis(basis), stats)
}

/// Buchberger's algorithm in which each round adds only the first S-polynomial,
/// in the order of the normal strategy, that does not reduce to zero; the pairs
/// are reduced in parallel. The pending pairs play the role of the matrix of
/// pairs whose S-polynomials are not yet known to reduce to zero.
pub fn buchberger_first<F : ParField, X : Ord + Hash + Clone + Send + Sync>(
    generators : Vec<Polynomial<F, X>>,
    threads : usize,
) -> (Vec<Polynomial<F, X>>, Stats) {
    let (mut basis, mut queue) = start(generators);
    let mut stats = Stats::default();
    // The pairs are reduced in windows of 2 * threads pairs, in the order of the
    // normal strategy; the next window is only taken if the whole window reduced
    // to zero. So the added remainder is always that of the first pair, in this
    // order, whose S-polynomial does not reduce to zero.
    let window = 2 * threads.max(1);
    loop {
        let order = queue.next_pairs(&basis, Some(window));
        if order.is_empty() {
            break;
        }
        stats.rounds += 1;
        let results = reduce_pairs(&order, &basis, threads, true);
        let first = results.iter().find(|(_, r)| r.is_some()).map(|(index, _)| *index);
        let mut chosen = None;
        for (index, r) in results {
            stats.reductions += 1;
            match r {
                None => {
                    stats.zero += 1;
                    queue.remove(order[index]);
                }
                Some(r) if Some(index) == first => {
                    queue.remove(order[index]);
                    chosen = Some(r);
                }
                Some(_) => stats.discarded += 1,
            }
        }
        if let Some(r) = chosen {
            add(&mut basis, &mut queue, r);
        }
    }
    (reduce_groebner_basis(basis), stats)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ideal::buchberger;
    use num_rational::Rational64 as Q;

    type P = Polynomial<Q, u32>;

    fn x(i : u32) -> P {
        Polynomial::var(i)
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

    fn random_ideal(rng : &mut Rng, n : u32, gens : usize, terms : usize) -> Vec<P> {
        (0..gens)
            .map(|_| {
                (0..terms).fold(P::zero(), |f, _| {
                    let mut t = Polynomial::constant(Q::from_integer([-2, -1, 1, 2][rng.below(4) as usize]));
                    for _ in 0..1 + rng.below(2) {
                        t = t * x(1 + rng.below(n as u64) as u32);
                    }
                    f + t
                })
            })
            .collect()
    }

    #[test]
    fn parallel_versions_give_the_reduced_basis() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        for _ in 0..30 {
            let generators = random_ideal(&mut rng, 3, 3, 3);
            let expected = buchberger(generators.clone());
            for threads in [1, 2, 4] {
                assert_eq!(buchberger_batch(generators.clone(), threads).0, expected);
                assert_eq!(buchberger_first(generators.clone(), threads).0, expected);
            }
        }
    }

    #[test]
    fn first_with_one_thread_discards_nothing() {
        let mut rng = Rng(7);
        for _ in 0..10 {
            let generators = random_ideal(&mut rng, 3, 3, 3);
            let (_, stats) = buchberger_first(generators, 1);
            assert_eq!(stats.discarded, 0);
        }
    }
}
