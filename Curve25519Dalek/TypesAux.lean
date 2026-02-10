/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux

/-! # Auxiliary theorems for Types

Theorems which are useful for proving spec theorems in this project but aren't available upstream.
This file is for theorems which depend on Types.lean (the Aeneas-generated types) in addition to
Defs.lean. For theorems that only depend on Defs.lean, use Aux.lean instead.
-/

open Aeneas.Std Result
namespace curve25519_dalek.scalar.Scalar

/-- Two Scalars are equal if their bytes are equal. -/
theorem Scalar_ext (a b : Scalar) : a.bytes = b.bytes → a = b := by
  cases a with | mk _ =>
  cases b with | mk _ =>
  grind

/-- If `U8x32_as_Nat` of a Scalar equals `0` then is it `ZERO`. -/
lemma U8x32_as_Nat_eq_zero_iff_ZERO (s : Scalar) : U8x32_as_Nat s.bytes = 0 ↔ s = ZERO := by
  have : U8x32_as_Nat ZERO.bytes = 0 := by
    unfold ZERO ZERO_body eval_global U8x32_as_Nat
    decide
  constructor
  · intro _
    have : s.bytes = ZERO.bytes := U8x32_as_Nat_injective (by grind)
    apply Scalar_ext
    grind
  · grind

end curve25519_dalek.scalar.Scalar
