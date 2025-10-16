/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Proofs.Defs

/-! # non_adjacent_form

Specification and proof for `Scalar::non_adjacent_form`.

This function computes the non-adjacent form representation.

**Source**: curve25519-dalek/src/scalar.rs:L920-L973

## TODO
- Write formal specification
- Complete proof
-/

open Aeneas.Std Result curve25519_dalek
open scalar

/-
natural language description:

    • Takes an input Scalar s and an integer w \in \{2,…,8\} and returns
      an array naf of type [i8; 256]. The output array naf represents
      the non-adjacent-form (NAF) of width w for the input Scalar s.

    • A width-w non-adjacent form of a positive integer k is an expression

      k = \sum_{i=0}^{m} n_i 2^i,

      whereby

      - each nonzero coefficient n_i is odd and satisfies |n_i| < 2^{w-1},
      - n_{m} \neq 0, and
      - among any w consecutive coefficients, at most one is nonzero.

    • The entry naf[i] in the output array is an i8 that represents n_i

natural language specs:

    • \sum_{i=0}^{255} naf[i] 2^i = scalar_to_nat(s)
    • \forall i \in \{0,…,255}: naf[i] \neq 0 => naf[i] is odd and |naf[i]| < 2^{w-1}
    • naf[255] \neq 0
    • \forall i \in \{0,…, 255 – w + 1\}: the sequence (naf[i], …, naf[i + w - 1]) contains at most one nonzero entry
-/
