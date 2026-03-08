/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic


/-! # identity

Specification and proof for `MontgomeryPoint::identity`.

This function returns the identity element of the Montgomery curve,
which is represented as 32 zero bytes.

**Source**: curve25519-dalek/src/montgomery.rs:L112-L117
-/

open Aeneas.Std Result Aeneas.Std.WP curve25519_dalek
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity

/-
natural language description:

• Returns the group identity element for Montgomery points, which has order 4

natural language specs:

• The function always succeeds (no panic)
• The resulting MontgomeryPoint is 32 zero bytes
• Interpreted as a natural number, the result equals 0
-/

/-- **Spec and proof concerning `montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity.identity`**:
- No panic (always returns successfully)
- The resulting MontgomeryPoint is 32 zero bytes
- Interpreted as a natural number via `U8x32_as_Nat`, the result equals 0
-/
@[progress]
theorem identity_spec :
    spec identity (fun q =>
    (∀ i : Fin 32, q[i]! = 0#u8) ∧
    U8x32_as_Nat q = 0) := by
  unfold identity
  suffices (∀ (i : Fin 32), (Array.repeat 32#usize 0#u8)[i] = 0#u8) ∧
    U8x32_as_Nat (Array.repeat 32#usize 0#u8) = 0 by simpa
  constructor
  · intro i
    fin_cases i <;> simp_all <;> decide
  · unfold U8x32_as_Nat
    simp only [Finset.sum_eq_zero_iff, Finset.mem_range]
    intro i hi
    have : (Array.repeat 32#usize 0#u8 : List U8)[i]!.val = 0 := by
      interval_cases i <;> simp [Array.repeat]
    simpa [*]

end curve25519_dalek.montgomery.MontgomeryPoint.Insts.Curve25519_dalekTraitsIdentity
