# oligo-poly

A Rust library for polynomial rings under oligomorphic group actions.
Its goal is to implement the equivariant Buchberger algorithm of
A. Ghosh and A. Lopez, *Computability of equivariant Gröbner bases* (2025).

## Status

- Polynomial rings over a field, with variables of any ordered type, and
  Gröbner bases: Buchberger's algorithm, reduced Gröbner bases, ideal
  membership, inclusion, equality, sum and product
  (`src/mon.rs`, `src/ideal.rs`).
- A framework for equivariant algorithms over ordered oligomorphic structures,
  with the dense linear order (Q, <) as the first example
  (`src/atoms.rs`, `src/elements_with_atoms.rs`, `src/dlo.rs`).
  It is only built with the Cargo feature `equivariant`.
- The equivariant Buchberger algorithm, in which a polynomial f is only
  reduced by elements h with supp(h) ⊆ supp(f) (`src/equivariant.rs`, example
  `equivariant_demo`). `equivariant_buchberger` computes a weak equivariant
  Gröbner basis, and `equivariant_groebner_basis` computes an equivariant
  Gröbner basis with the colouring of Section 5 of the article
  (`src/coloured.rs`). With the latter, f is in the ideal if and only if
  `reduces_to_zero` holds.

## Building and testing

```sh
cargo test
cargo test --features equivariant   # builds the crate rug, which compiles GMP
cargo run --release --features equivariant --example equivariant_demo
```

## Example

```sh
echo "x*y; x + y*z" | cargo run --example groebner_stdin -- f2
```

prints the reduced Gröbner basis {x², xy, x + yz} over the field with two
elements, for the lexicographic order in which a larger variable is more
significant. The script `scripts/compare_with_sympy.py` compares this example
with SymPy on random inputs.

## Documentation

`README.tex` explains the theory and the implementation.
Compile it with `latexmk -pdf README.tex`.

## License

MIT
