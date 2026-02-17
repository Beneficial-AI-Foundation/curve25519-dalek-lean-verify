/-
MWE: `progress` timeout after a spec with expensive postconditions.

The `progress` tactic runs `simp` on **all hypotheses** in the context. When a prior
`progress` step introduces hypotheses whose types are expensive for `simp` to reduce
(involving `Finset.sum` and `Nat.ModEq`), any subsequent `progress` call times out
at `whnf`.

The workaround is to clear (or hide) the expensive hypotheses before calling `progress`
again.
-/
import Aeneas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Aeneas.Std Result Aeneas.Std.WP

def U8x32_as_Nat (bytes : Array U8 32#usize) : Nat :=
  ∑ i ∈ Finset.range 32, 2 ^ (8 * i) * (bytes[i]!).val

def Field51_as_Nat (limbs : Array U64 5#usize) : Nat :=
  ∑ i ∈ Finset.range 5, 2 ^ (51 * i) * (limbs[i]!).val

def p : Nat := 2 ^ 255 - 19

noncomputable def to_bytes (input : Array U64 5#usize) :
    Result (Array U8 32#usize) := by
  exact sorry

@[progress]
theorem to_bytes_spec (self : Array U64 5#usize) :
    spec (to_bytes self) (fun result =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p) := by
  exact sorry

noncomputable def my_fun (input : Array U64 5#usize) : Result (Slice U8) := do
  let bytes ← to_bytes input
  let s ← (↑(Array.to_slice bytes) : Result (Slice U8))
  ok s

-- TIMEOUT: the second `progress` (on `to_slice`) times out.
-- Uncomment to reproduce:
theorem my_fun_spec_timeout (input : Array U64 5#usize) :
    spec (my_fun input) (fun _ => True) := by
  unfold my_fun
  progress
  progress  -- timeout at `whnf` (progress runs simp on the Nat.ModEq / Finset.sum hypotheses)

-- WORKAROUND: clear the expensive hypotheses before the next `progress` call
theorem my_fun_spec_fix (input : Array U64 5#usize) :
    spec (my_fun input) (fun _ => True) := by
  unfold my_fun
  progress as ⟨bytes, h_mod, h_lt⟩
  clear h_mod h_lt
  progress
