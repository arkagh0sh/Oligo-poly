//! Polynomial rings, Gröbner bases and (in progress) equivariant algorithms
//! for polynomial rings whose variables are the atoms of an oligomorphic structure.

pub mod bits;
pub mod helpers;
pub mod ideal;
pub mod mon;

// The equivariant framework is still under development. It is only built with
// `cargo build --features equivariant`.
#[cfg(feature = "equivariant")]
pub mod atoms;
#[cfg(feature = "equivariant")]
pub mod dlo;
#[cfg(feature = "equivariant")]
pub mod elements_with_atoms;
#[cfg(feature = "equivariant")]
pub mod equivariant;
