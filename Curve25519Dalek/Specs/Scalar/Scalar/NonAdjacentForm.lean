/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic

/-! # Spec theorem for `curve25519_dalek::scalar::Scalar::non_adjacent_form`

Takes an input `Scalar` `s` and a width parameter `w ∈ {2, …, 8}`, and returns an array `naf`
of type `[i8; 256]` representing the width-`w` non-adjacent form (NAF) of `s`.

A width-`w` NAF of a positive integer `k` is a signed-digit representation

  k = ∑_{i=0}^{m} nᵢ · 2^i,

satisfying:
- each nonzero `nᵢ` is odd and satisfies `|nᵢ| < 2^{w-1}`,
- `n_m ≠ 0`, and
- among any `w` consecutive digits, at most one is nonzero.

The entry `naf[i]` in the output array stores `nᵢ` as an `i8`.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

end curve25519_dalek.scalar.Scalar
