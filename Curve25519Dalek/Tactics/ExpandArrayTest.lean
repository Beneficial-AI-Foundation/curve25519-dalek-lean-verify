/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas
import Curve25519Dalek.Tactics.ExpandArray

/-! # Tests for `expand_array`

-/

open Aeneas.Std

/-- Basic: 5-element `.set` chain is resolved to per-index value hypotheses. -/
example
    (out : Array U64 5#usize)
    (v0 v1 v2 v3 v4 : U64)
    (out1 out2 out3 out4 result : Array U64 5#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : out2 = out1.set 1#usize v1)
    (h3 : out3 = out2.set 2#usize v2)
    (h4 : out4 = out3.set 3#usize v3)
    (h5 : result = out4.set 4#usize v4)
    (hgoal : v0.val + v1.val = 42) :
    result[0]!.val + result[1]!.val = 42 := by
  expand_array result
  simp only [Array.getElem!_Nat_eq, *]

/-- Non-interference: hypotheses about unrelated arrays are not touched. -/
example
    (out : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (out1 out2 result other : Array U64 3#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : out2 = out1.set 1#usize v1)
    (h3 : result = out2.set 2#usize v2)
    (hother : other[0]!.val + other[1]!.val = 100) :
    ((result) : List U64)[0]!.val = v0.val ∧ other[0]!.val + other[1]!.val = 100 := by
  expand_array result
  exact ⟨by assumption, by assumption⟩

/-- Single-index form `expand_array x N` extracts just index `N`. -/
example
    (limbs : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (arr1 arr2 result : Array U64 3#usize)
    (h1 : arr1 = limbs.set 0#usize v0)
    (h2 : arr2 = arr1.set 1#usize v1)
    (h3 : result = arr2.set 2#usize v2) :
    ((result) : List U64)[1]!.val = v1.val := by
  expand_array result 1
  assumption

/-! ## Realistic two-pass carry-propagation context

Mirrors `reduce_spec`, exercising the `using [...]` extras and the `simp_lists_safe` interaction. -/
section TwoPass

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
    (↑(↑arr6) : List U64)[1]!.val = (↑(↑limbs) : List U64)[1]!.val % 2 ^ 51 +
      (↑(↑limbs) : List U64)[0]!.val >>> 51 := by
  expand_array arr6 using [UScalar.val_and]
  assumption

end TwoPass
