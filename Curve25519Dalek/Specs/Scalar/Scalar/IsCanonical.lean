/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Scalar.Scalar.Reduce
import Curve25519Dalek.Specs.Scalar.Scalar.CtEq

/-!
# Spec theorem for `curve25519_dalek::scalar::Scalar::is_canonical`

Returns `True` if the input scalar `s` is the canonical representative modulo ℓ
within the scalar field (i.e., s ∈ {0, …, ℓ − 1}), and `False` otherwise.

Source: "curve25519-dalek/src/scalar.rs"
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.scalar.Scalar

/-- **Spec theorem for `curve25519_dalek::scalar::Scalar::is_canonical`**
• No panic (always returns successfully)
• Returns `Choice.one` if and only if the bytes of `s` represent a value less than `L` (group order)
-/
@[step]
theorem is_canonical_spec (s : Scalar) :
    is_canonical s ⦃ (c : subtle.Choice) =>
      (c = Choice.one ↔ U8x32_as_Nat s.bytes < L) ⦄ := by
  unfold is_canonical
  step*
  constructor
  · grind
  · intro h
    rename_i s' _
    have bytes_eq : U8x32_as_Nat s.bytes = U8x32_as_Nat s'.bytes :=
        Nat.ModEq.eq_of_lt_of_lt s_post1 s_post2 h
    rw [c_post]
    apply U8x32_as_Nat_injective
    symm
    exact bytes_eq

end curve25519_dalek.scalar.Scalar
