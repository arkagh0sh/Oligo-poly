//! Counters of the steps of the algorithms, for experiments.
//!
//! The counters are kept per thread, so that they cost almost nothing and do
//! not interfere between threads; the counts of the threads started by
//! `parallel.rs` are not included. The steps are:
//!
//! - `s_polynomials`: the S-polynomials computed (`Polynomial::syzygy`);
//! - `reductions`: the elementary reduction steps, in which one term is
//!   cancelled by a multiple of a reducer (`Polynomial::reduce_by` when it
//!   reduces, and `Polynomial::reduce_term_by`), including those of the final
//!   interreduction;
//! - `added`: the polynomials (or orbits) added to a basis by the main loop of
//!   `ideal::buchberger`, `equivariant::equivariant_buchberger` and
//!   `equivariant::one_colour_groebner_basis`, not counting the generators.

use std::cell::Cell;

thread_local! {
    static S_POLYNOMIALS : Cell<u64> = const { Cell::new(0) };
    static REDUCTIONS : Cell<u64> = const { Cell::new(0) };
    static ADDED : Cell<u64> = const { Cell::new(0) };
}

/// The values of the counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Counts {
    pub s_polynomials : u64,
    pub reductions : u64,
    pub added : u64,
}

/// Sets the counters of the current thread to zero.
pub fn reset() {
    S_POLYNOMIALS.with(|c| c.set(0));
    REDUCTIONS.with(|c| c.set(0));
    ADDED.with(|c| c.set(0));
}

/// The counters of the current thread.
pub fn get() -> Counts {
    Counts {
        s_polynomials : S_POLYNOMIALS.with(Cell::get),
        reductions : REDUCTIONS.with(Cell::get),
        added : ADDED.with(Cell::get),
    }
}

pub(crate) fn count_s_polynomial() {
    S_POLYNOMIALS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn count_reduction() {
    REDUCTIONS.with(|c| c.set(c.get() + 1));
}

pub(crate) fn count_added() {
    ADDED.with(|c| c.set(c.get() + 1));
}
