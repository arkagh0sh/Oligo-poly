//! Polynomial rings, Gröbner bases and (in progress) equivariant algorithms
//! for polynomial rings whose variables are the atoms of an oligomorphic structure.

pub mod bits;
pub mod counters;
pub mod helpers;
pub mod ideal;
pub mod logic;
pub mod mon;
pub mod one_colour;
pub mod parallel;
pub mod parse;

// The equivariant framework and the symbolic atoms, built with
// `cargo build --features atoms`.
#[cfg(feature = "atoms")]
pub mod atoms;
#[cfg(feature = "atoms")]
pub mod coloured;
#[cfg(feature = "atoms")]
pub mod elements_with_atoms;
#[cfg(feature = "atoms")]
pub mod equivariant;
#[cfg(feature = "atoms")]
pub mod generator;
#[cfg(feature = "atoms")]
pub mod product;
#[cfg(feature = "atoms")]
pub mod symbolic;
#[cfg(feature = "atoms")]
pub mod trivial;

// The concrete atoms, which use rug (GMP), built with
// `cargo build --features equivariant`.
#[cfg(feature = "equivariant")]
pub mod dlo;
#[cfg(feature = "equivariant")]
pub mod tree;
