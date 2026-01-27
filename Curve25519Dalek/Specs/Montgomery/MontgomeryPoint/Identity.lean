/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Defs


/-! # identity

Specification and proof for `MontgomeryPoint::identity`.

This function returns the identity element of the Montgomery curve,
which is represented as 32 zero bytes.

**Source**: curve25519-dalek/src/montgomery.rs:L112-L117
-/

open Aeneas.Std Result curve25519_dalek
namespace curve25519_dalek.montgomery.IdentityMontgomeryPoint

/-
natural language description:

• Returns the group identity element for Montgomery points, which has order 4

natural language specs:

• The function always succeeds (no panic)
• The resulting MontgomeryPoint is 32 zero bytes
• Interpreted as a natural number, the result equals 0
-/

/-- **Spec and proof concerning `montgomery.IdentityMontgomeryPoint.identity`**:
- No panic (always returns successfully)
- The resulting MontgomeryPoint is 32 zero bytes
- Interpreted as a natural number via `U8x32_as_Nat`, the result equals 0
-/
@[progress]
theorem identity_spec :
    ∃ q, identity = ok q ∧
    (∀ i : Fin 32, q[i]! = 0#u8) ∧
    U8x32_as_Nat q = 0 := by
  use Array.repeat 32#usize 0#u8
  constructor
  · rfl
  constructor
  · intro i
    -- Each byte of a zero-filled array is zero
    simp only [Array.repeat, getElem!, List.getElem?_replicate]
    have h : i.val < 32 := i.isLt
    simp [h]
  · -- Sum of zeros is zero
    unfold U8x32_as_Nat
    simp only [Finset.sum_eq_zero_iff, Finset.mem_range]
    intro i hi
    simp only [Array.repeat, getElem!,List.getElem?_replicate]
    simp [hi]

end curve25519_dalek.montgomery.IdentityMontgomeryPoint
