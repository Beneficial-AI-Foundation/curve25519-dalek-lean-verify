/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryMul
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

set_option exponentiation.threshold 260

/-! # Spec Theorem for `Scalar52::as_montgomery`

Specification and proof for `Scalar52::as_montgomery`.

This function converts to Montgomery form.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas.Std Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

/-
natural language description:

    • Takes an input unpacked scalar u and returns an unpacked scalar m representing
      the value (u * R) mod L, where R = 2^260 is the Montgomery constant and L is the group order.

natural language specs:

    • scalar_to_nat(m) = (scalar_to_nat(u) * R) mod L
-/

/-- **Spec and proof concerning `scalar.Scalar52.as_montgomery`**:
- No panic (always returns successfully)
- The result represents the input scalar multiplied by the Montgomery constant R = 2^260, modulo L
-/
@[progress]
theorem as_montgomery_spec (u : Scalar52) :
    ∃ m, as_montgomery u = ok m ∧
    Scalar52_as_Nat m ≡ (Scalar52_as_Nat u * R) [MOD L] := by
  unfold as_montgomery
  progress as ⟨m, pos⟩
  suffices Scalar52_as_Nat m * R ≡ Scalar52_as_Nat u * R * R [MOD L] by
    exact Nat.ModEq.cancel_right_of_coprime (by decide) this
  have := Nat.ModEq.mul_left (Scalar52_as_Nat u) RR_spec
  have := (Nat.ModEq.trans this.symm pos).symm
  grind

end curve25519_dalek.backend.serial.u64.scalar.Scalar52
