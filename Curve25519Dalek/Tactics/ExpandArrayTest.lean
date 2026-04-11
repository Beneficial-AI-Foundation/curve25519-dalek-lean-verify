/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Tactics.ExpandArray

/-! # `expand_array` tactic tests -- mimicking the `reduce` proof context

These tests simulate the context that `step*` produces for `reduce`-like
computations WITHOUT importing the actual Reduce file. The goal is to serve
as a benchmark for tactic development.

## Structure of the `reduce` computation (simplified to 3 elements)

The Rust `reduce` function does a two-pass carry propagation over a limb array:

- **Pass 1 (mask)**: For each index k, compute `limbs[k] &&& mask` and store
  into the array. This produces intermediate arrays `arr1`, `arr2`, `arr3`.

- **Pass 2 (carry add)**: For each index k, read back the masked value and
  add the carry from the previous limb. This produces `arr4`, `arr5`, `arr6`.

After `step*`, the proof context contains:
- Defining equalities for each intermediate array: `arr1 = limbs.set 0 v0`, etc.
- `_post` hypotheses for each scalar operation: shifts, ANDs, adds.
- The final array `arr6` with a 6-deep .set chain (3 sets from pass 1, 3 from pass 2).

## Current behavior of `expand_array`

The current tactic:
1. Resolves the `.set` chain via `rw` + `simp (discharger := norm_num)`.
2. Applies `simp only [*]` to chain through `_post` hypotheses.

This already substitutes scalar `_post` hypotheses, but the `simp only [*]`
also substitutes hypotheses like `a0_base = (↑arr3)[0]!`, which introduces
intermediate array expressions (`arr3`, `arr4`, etc.) that remain unresolved.

## What is missing

After the current tactic, hypotheses look like:
```
harr60 : ↑arr6[0]! = ↑(((limbs.set 0#usize m0).set 1#usize m1).set 2#usize m2)[0]!
           + ↑limbs[2]! >>> 51 * 19
```

The missing steps are:
- `simp_lists` to resolve intermediate array reads like `(arr3)[0]!` to `m0`
- Possibly another `simp only [*]` + `simp_lists` pass for full normalization

The desired end state:
```
harr60 : ↑arr6[0]! = ↑limbs[0]! &&& (2^51-1) + ↑limbs[2]! >>> 51 * 19
```
-/

open Aeneas.Std

/-! ## Test 1: Current behavior -- single-pass `.set` chain

This test works with the CURRENT `expand_array` implementation.
It has a simple `.set` chain with `_post` hypotheses for scalars.
No intermediate array reads occur, so `simp only [*]` is sufficient.
-/
section CurrentBehavior

-- Single-pass: set indices 0, 1, 2 with computed values.
-- The _post hypotheses describe how each value was computed.
example
    (limbs : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (arr1 : Array U64 3#usize)
    (arr2 : Array U64 3#usize)
    (arr3 : Array U64 3#usize)
    (h1 : arr1 = limbs.set 0#usize v0)
    (h2 : arr2 = arr1.set 1#usize v1)
    (h3 : arr3 = arr2.set 2#usize v2)
    -- _post hypotheses from step* for scalar operations
    (v0_post : v0.val = 100)
    (v1_post : v1.val = 200)
    (v2_post : v2.val = 300) :
    arr3[0]!.val + arr3[1]!.val + arr3[2]!.val = 600 := by
  -- Current behavior: expand_array resolves the .set chain
  -- and simp only [*] chains through _post hypotheses.
  -- Result:
  --   harr30 : (↑arr3)[0]!.val = 100
  --   harr31 : (↑arr3)[1]!.val = 200
  --   harr32 : (↑arr3)[2]!.val = 300
  expand_array arr3
  simp only [*]

end CurrentBehavior

/-! ## Test 2: Two-pass -- current behavior shows the gap

This test mimics the `reduce` context. The current `expand_array` resolves
the `.set` chain and chains `_post` hypotheses, but leaves intermediate
array reads (from pass 1) unresolved.

The test demonstrates what the tactic currently produces, then manually
completes the expansion with `simp_lists` and another `simp only [*]` pass.
-/
section TwoPassCurrentGap

-- Mimics the context produced by `step*` on a 3-element `reduce`.
--
-- Aeneas-generated code structure:
--   Pass 1: reads limbs[k], masks with AND, stores into arr1..arr3
--   Pass 2: reads arr3[k] (or later), adds carry, stores into arr4..arr6
--
-- After step*, all intermediate scalars have _post hypotheses and
-- all intermediate arrays have defining equalities.

attribute [local simp_lists_safe] UScalar.val_and Nat.and_two_pow_sub_one_eq_mod

example
    -- Original input array
    (limbs : Array U64 3#usize)
    -- Carries computed from original limbs (pass 1 reads)
    (i0 : U64) (i0_post : i0 = (↑limbs)[0]!)
    (c0 : U64) (c0_post : c0.val = i0.val >>> 51)
    (i1 : U64) (i1_post : i1 = (↑limbs)[1]!)
    (c1 : U64) (c1_post : c1.val = i1.val >>> 51)
    (i2 : U64) (i2_post : i2 = (↑limbs)[2]!)
    (c2 : U64) (c2_post : c2.val = i2.val >>> 51)
    -- Mask constant
    (mask : U64) (mask_post : mask.val = 2 ^ 51 - 1)
    -- Pass 1: mask each limb
    (m0 : U64) (m0_post : m0.val = (i0 &&& mask).val)
    (arr1 : Array U64 3#usize) (harr1 : arr1 = limbs.set 0#usize m0)
    (m1_base : U64) (m1_base_post : m1_base = (↑arr1)[1]!)
    (m1 : U64) (m1_post : m1.val = (m1_base &&& mask).val)
    (arr2 : Array U64 3#usize) (harr2 : arr2 = arr1.set 1#usize m1)
    (m2_base : U64) (m2_base_post : m2_base = (↑arr2)[2]!)
    (m2 : U64) (m2_post : m2.val = (m2_base &&& mask).val)
    (arr3 : Array U64 3#usize) (harr3 : arr3 = arr2.set 2#usize m2)
    -- Pass 2: add carries
    (carry_mult : U64) (carry_mult_post : carry_mult.val = c2.val * 19)
    (a0_base : U64) (a0_base_post : a0_base = (↑arr3)[0]!)
    (a0 : U64) (a0_post : a0.val = a0_base.val + carry_mult.val)
    (arr4 : Array U64 3#usize) (harr4 : arr4 = arr3.set 0#usize a0)
    (a1_base : U64) (a1_base_post : a1_base = (↑arr4)[1]!)
    (a1 : U64) (a1_post : a1.val = a1_base.val + c0.val)
    (arr5 : Array U64 3#usize) (harr5 : arr5 = arr4.set 1#usize a1)
    (a2_base : U64) (a2_base_post : a2_base = (↑arr5)[2]!)
    (a2 : U64) (a2_post : a2.val = a2_base.val + c1.val)
    (arr6 : Array U64 3#usize) (harr6 : arr6 = arr5.set 2#usize a2) :
    -- Goal: a property that requires the fully expanded formulas.
    -- After full expansion, harr60 should express arr6[0]!.val purely in terms
    -- of limbs[k]!.val with &&& and >>> operations.
    True := by
  -- ============================================================
  -- Step 1: expand_array (current behavior)
  -- ============================================================
  -- This resolves the .set chain AND chains _post hypotheses via simp only [*].
  -- Result (from compiler diagnostics):
  --   harr60 : ↑arr6[0]! = ↑(((limbs.set 0#usize m0).set 1#usize m1).set 2#usize m2)[0]!
  --              + ↑limbs[2]! >>> 51 * 19
  --   harr61 : ↑arr6[1]! = ↑(((...).set 2#usize m2).set 0#usize a0)[1]! + ↑limbs[0]! >>> 51
  --   harr62 : ↑arr6[2]! = ↑((...).set 0#usize a0).set 1#usize a1)[2]! + ↑limbs[1]! >>> 51
  --
  -- Note: intermediate array expressions like (arr3.set ...)[0]! remain unresolved.
  -- This is the GAP that needs to be closed.
  expand_array arr6
  -- ============================================================
  -- Step 2: simp_lists resolves intermediate array reads
  -- ============================================================
  -- (((limbs.set 0 m0).set 1 m1).set 2 m2)[0]! becomes m0, etc.
  simp_lists at harr60 harr61 harr62
  -- ============================================================
  -- Step 3: another simp only [*] to chain remaining _post hyps
  -- ============================================================
  simp only [*] at harr60 harr61 harr62
  -- ============================================================
  -- Step 4: final simp_lists pass for any remaining array reads
  -- ============================================================
  simp_lists at harr60 harr61 harr62
  -- After all steps, we have:
  --   harr60 : ↑(↑arr6)[0]! = (↑(↑limbs)[0]! &&& ↑mask) + ↑(↑limbs)[2]! >>> 51 * 19
  --   harr61 : ↑(↑arr6)[1]! = (↑(↑limbs)[1]! &&& ↑mask) + ↑(↑limbs)[0]! >>> 51
  --   harr62 : ↑(↑arr6)[2]! = (↑(↑limbs)[2]! &&& ↑mask) + ↑(↑limbs)[1]! >>> 51
  --
  -- DESIRED: `expand_array arr6` alone should produce these hypotheses,
  -- replacing steps 1-4 with a single tactic call.
  trivial

end TwoPassCurrentGap

/-! ## Test 3: Two-pass -- desired behavior (when tactic is improved)

This test will serve as the benchmark. Once the tactic is improved,
UNCOMMENT the `expand_array arr6` line and REMOVE the manual steps.
The proof should close with just `expand_array arr6` + `linarith`.
-/
section TwoPassDesired

attribute [local simp_lists_safe] UScalar.val_and Nat.and_two_pow_sub_one_eq_mod

example
    (limbs : Array U64 3#usize)
    (i0 : U64) (i0_post : i0 = (↑limbs)[0]!)
    (c0 : U64) (c0_post : c0.val = i0.val >>> 51)
    (i1 : U64) (i1_post : i1 = (↑limbs)[1]!)
    (c1 : U64) (c1_post : c1.val = i1.val >>> 51)
    (i2 : U64) (i2_post : i2 = (↑limbs)[2]!)
    (c2 : U64) (c2_post : c2.val = i2.val >>> 51)
    (mask : U64) (mask_post : mask.val = 2 ^ 51 - 1)
    (m0 : U64) (m0_post : m0.val = (i0 &&& mask).val)
    (arr1 : Array U64 3#usize) (harr1 : arr1 = limbs.set 0#usize m0)
    (m1_base : U64) (m1_base_post : m1_base = (↑arr1)[1]!)
    (m1 : U64) (m1_post : m1.val = (m1_base &&& mask).val)
    (arr2 : Array U64 3#usize) (harr2 : arr2 = arr1.set 1#usize m1)
    (m2_base : U64) (m2_base_post : m2_base = (↑arr2)[2]!)
    (m2 : U64) (m2_post : m2.val = (m2_base &&& mask).val)
    (arr3 : Array U64 3#usize) (harr3 : arr3 = arr2.set 2#usize m2)
    (carry_mult : U64) (carry_mult_post : carry_mult.val = c2.val * 19)
    (a0_base : U64) (a0_base_post : a0_base = (↑arr3)[0]!)
    (a0 : U64) (a0_post : a0.val = a0_base.val + carry_mult.val)
    (arr4 : Array U64 3#usize) (harr4 : arr4 = arr3.set 0#usize a0)
    (a1_base : U64) (a1_base_post : a1_base = (↑arr4)[1]!)
    (a1 : U64) (a1_post : a1.val = a1_base.val + c0.val)
    (arr5 : Array U64 3#usize) (harr5 : arr5 = arr4.set 1#usize a1)
    (a2_base : U64) (a2_base_post : a2_base = (↑arr5)[2]!)
    (a2 : U64) (a2_post : a2.val = a2_base.val + c1.val)
    (arr6 : Array U64 3#usize) (harr6 : arr6 = arr5.set 2#usize a2) :
    -- Goal that exercises the fully expanded hypotheses
    True := by
  -- ============================================================
  -- DESIRED (once tactic is improved):
  --   expand_array arr6
  --   trivial
  --
  -- This single call should produce:
  --   harr60 : ↑(↑arr6)[0]! = (↑(↑limbs)[0]! &&& ↑mask) + ↑(↑limbs)[2]! >>> 51 * 19
  --   harr61 : ↑(↑arr6)[1]! = (↑(↑limbs)[1]! &&& ↑mask) + ↑(↑limbs)[0]! >>> 51
  --   harr62 : ↑(↑arr6)[2]! = (↑(↑limbs)[2]! &&& ↑mask) + ↑(↑limbs)[1]! >>> 51
  -- ============================================================
  --
  -- CURRENT workaround (steps 1-4 that the improved tactic should internalize):
  expand_array arr6
  simp_lists at harr60 harr61 harr62
  simp only [*] at harr60 harr61 harr62
  simp_lists at harr60 harr61 harr62
  trivial

end TwoPassDesired

/-! ## Test 4: Compatibility -- unrelated hypotheses and arrays are untouched -/
section Compatibility

example
    (limbs : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (arr1 : Array U64 3#usize)
    (arr2 : Array U64 3#usize)
    (result : Array U64 3#usize)
    (h1 : arr1 = limbs.set 0#usize v0)
    (h2 : arr2 = arr1.set 1#usize v1)
    (h3 : result = arr2.set 2#usize v2)
    -- Unrelated hypothesis that must not be touched
    (other : Array U64 3#usize)
    (hother : other[0]!.val + other[1]!.val = 100)
    -- Another unrelated hypothesis (intentionally unused, tests non-interference)
    (_hscalar : v0.val < 2 ^ 52) :
    result[0]!.val = v0.val ∧ hother = hother := by
  expand_array result
  exact ⟨hresult0, rfl⟩

end Compatibility

/-! ## Test 5: Single index expansion -/
section SingleIndex

example
    (limbs : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (arr1 : Array U64 3#usize)
    (arr2 : Array U64 3#usize)
    (result : Array U64 3#usize)
    (h1 : arr1 = limbs.set 0#usize v0)
    (h2 : arr2 = arr1.set 1#usize v1)
    (h3 : result = arr2.set 2#usize v2) :
    result[1]!.val = v1.val := by
  expand_array result 1
  exact hresult1

end SingleIndex
