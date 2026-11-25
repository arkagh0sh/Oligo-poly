# Notes for Claude

## Rules

- Always check the correctness of an algorithm before relying on it: give an
  argument (a short proof), and test it, for example against a closed formula,
  a brute-force count, or an independent implementation.
- The public interface contains only equivariant functions. A function that
  returns representatives (such as `one_point_extensions` or
  `Orbit::representative`) stays private to the crate.
- Give short answers, in formal and simple English.

## Facts

- LOIS (Kopczyński and Toruńczyk) is much slower than this library: listing
  the orbits of pairs of 5-element sets of (Q, <) takes 1.8 s in LOIS, against
  26 ms with the symbolic atoms and 3 ms with `DLO` (November 2026).

- Treating the pairs with the smallest domain |supp(f) ∪ supp(g)| first
  (`Selection::SmallestDomain`, `Strategy::SmallestDomain`) is correct but not
  a good default: on 30 random ideals in 4 to 6 variables it was slightly
  faster on typical ideals, but it timed out (30 s) on 5 ideals that the order
  of creation solved, sometimes in 14 ms; on symbolic atoms it was slower in
  5 of 7 cases, adding 2 to 3 times more orbits (November 2026).

- Buchberger's first criterion in the orbit algorithms
  (`Options::first_criterion`: skip the positions whose leading monomials share
  no atom) is correct (README.tex, proof of `lem:settled`, and the argument for
  the colouring via `lem:weak basis`) and faster on every ideal measured: 1.1 to
  3 times for one colour and 3 to 11 times for the colouring on 30 random
  ideals in 4 to 6 variables, and 2 to 12 times on symbolic atoms, where it
  also finished cases that took more than 120 s (November 2026).

## Next steps

- Introduce tricks for faster Gröbner bases: for example Buchberger's criteria
  adapted to orbits (with the support condition), a better selection of pairs,
  or asking `orbits_in_product` only for the pairs whose leading monomials share
  atoms. Each trick needs a correctness argument first.
- Trees: small integer coordinates for `Tree`, with a canonical relabelling of
  the representatives, or a combinatorial `orbits_in_product`.
