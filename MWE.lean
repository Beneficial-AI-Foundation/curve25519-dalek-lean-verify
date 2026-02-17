/-
MWE: `progress` timeout after a spec with expensive postconditions.

The `progress` tactic runs `simp` on **all hypotheses** in the context. When a prior
`progress` step introduces hypotheses whose types are expensive for `simp` to reduce
(involving `Finset.sum` and `Nat.ModEq`), any subsequent `progress` call times out
at `whnf`.

The workaround is to wrap the expensive hypotheses in an opaque `Hold` wrapper before
calling `progress`, then recover them with `change` afterwards.
-/
import Aeneas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Aeneas Aeneas.Std Result Aeneas.Std.WP

def U8x32_as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (bytes.val.getD i 0#u8).val

def SliceU8_as_Nat (s : Slice U8) : Nat :=
  ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (s.val.getD i 0#u8).val

def Field51_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * (limbs[i]!).val

def p : Nat := 2 ^ 255 - 19

/-- Serialize a field element (5 × u64 limbs) to a 32-byte array.
The real implementation performs modular reduction then bit-packing.
See: https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Funs.lean#L1432 -/
noncomputable def to_bytes (input : Array U64 5#usize) :
    Result (Array U8 32#usize) := sorry

/-- The byte encoding is congruent to the field element modulo p.
See: https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master/Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ToBytes.lean#L158 -/
@[progress]
theorem to_bytes_spec (self : Array U64 5#usize) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ⦄ := sorry

/-- Serialize a field element to a byte slice (calls `to_bytes` then `Array.to_slice`). -/
noncomputable def my_fun (input : Array U64 5#usize) : Result (Slice U8) := do
  let bytes ← to_bytes input
  let s ← (↑(Array.to_slice bytes) : Result (Slice U8))
  ok s

-- TIMEOUT: the second `progress` (on `to_slice`) times out.
-- Uncomment to reproduce:
-- theorem my_fun_spec (input : Array U64 5#usize) :
--     my_fun input ⦃ result =>
--     SliceU8_as_Nat result ≡ Field51_as_Nat input [MOD p] ⦄ := by
--   unfold my_fun
--   progress
--   progress  -- timeout at `whnf` (progress runs simp on the Nat.ModEq / Finset.sum hypotheses)

-- FIX: wrap expensive hypotheses in an opaque definition to hide them from `simp`
private def Hold (P : Prop) : Prop := P

theorem my_fun_spec' (input : Array U64 5#usize) :
    my_fun input ⦃ (result : Slice U8) =>
    SliceU8_as_Nat result ≡ Field51_as_Nat input [MOD p] ⦄ := by
  unfold my_fun
  progress as ⟨bytes, h_mod⟩
  -- We need h_mod for the postcondition, so we can't clear it.
  -- Wrap it in `Hold` (opaque to simp) before continuing.
  have h_mod' : Hold (U8x32_as_Nat bytes ≡ Field51_as_Nat input [MOD p]) := h_mod
  clear h_mod
  progress
  -- Recover the hypothesis (`Hold P` is defeq to `P`)
  change U8x32_as_Nat bytes ≡ Field51_as_Nat input [MOD p] at h_mod'
  -- Complete the proof
  simp only [*]
  exact h_mod'
