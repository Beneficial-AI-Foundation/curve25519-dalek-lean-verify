/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # `flatten_updates` tactic

In Aeneas-generated code, arrays are updated one element at a time:
```
out1 = out.set 0#usize v0
out2 = out1.set 1#usize v1
...
result = outN.set (N-1)#usize vN_1
```

After `step*`, we get hypotheses like:
```
h1 : out1 = out.set 0#usize v0
h2 : out2 = out1.set 1#usize v1
...
hN : result = outN_1.set (N-1)#usize vN_1
```

The `flatten_updates` tactic transforms these into:
```
result[0]! = v0
result[1]! = v1
...
result[N-1]! = vN_1
```

by inlining all intermediate arrays (`subst_vars`) and then
simplifying `getElem!`/`set` combinations.
-/

open Aeneas.Std

/-- `flatten_updates` inlines all intermediate array update
hypotheses via `subst_vars`, then simplifies all
`getElem!`/`set` in hypotheses using Aeneas library lemmas.

After this tactic, hypotheses involving chained `.set` calls
are resolved to direct element equalities. The goal is
left unchanged. -/
macro "flatten_updates" : tactic =>
  `(tactic| (
    subst_vars
    simp (discharger := agrind) only [
      Array.getElem!_Usize_set_eq,
      Array.getElem!_Usize_set_ne,
      Array.getElem!_Nat_set_eq,
      Array.getElem!_Nat_set_ne,
      Array.set_length,
      Array.length_eq
    ] at *
  ))

/-! ## Tests -/

section Test

open Aeneas.Std

-- Test 1: After flatten_updates, result[k]! = vk are
-- available as hypotheses, not just closing goals
example
    (out : Array U64 5#usize)
    (v0 v1 v2 v3 v4 : U64)
    (out1 : Array U64 5#usize)
    (out2 : Array U64 5#usize)
    (out3 : Array U64 5#usize)
    (out4 : Array U64 5#usize)
    (result : Array U64 5#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : out2 = out1.set 1#usize v1)
    (h3 : out3 = out2.set 2#usize v2)
    (h4 : out4 = out3.set 3#usize v3)
    (h5 : result = out4.set 4#usize v4) :
    result[0]!.val + result[1]!.val +
    result[2]!.val + result[3]!.val +
    result[4]!.val =
    v0.val + v1.val + v2.val + v3.val + v4.val + 1:= by
  flatten_updates -- resolves all result[k]! to vk

-- Test 2: Hypotheses involving result[k]! are
-- simplified and can be used in subsequent reasoning
example
    (out : Array U64 5#usize)
    (v0 v1 v2 v3 v4 : U64)
    (out1 : Array U64 5#usize)
    (out2 : Array U64 5#usize)
    (out3 : Array U64 5#usize)
    (out4 : Array U64 5#usize)
    (result : Array U64 5#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : out2 = out1.set 1#usize v1)
    (h3 : out3 = out2.set 2#usize v2)
    (h4 : out4 = out3.set 3#usize v3)
    (h5 : result = out4.set 4#usize v4)
    (hv : v0.val + v1.val = 42) :
    result[0]!.val + result[1]!.val = 42 := by
  flatten_updates -- goal becomes v0.val + v1.val = 42
  exact hv

-- Test 3: Partial update — unmodified indices
-- fall through to the base array
example
    (out : Array U64 5#usize)
    (v0 v2 : U64)
    (out1 : Array U64 5#usize)
    (result : Array U64 5#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : result = out1.set 2#usize v2) :
    result[0]!.val + result[1]!.val +
    result[2]!.val =
    v0.val + out[1]!.val + v2.val := by
  flatten_updates

-- Test 4: U8 arrays (not just U64)
example
    (out : Array U8 3#usize)
    (a b c : U8)
    (out1 : Array U8 3#usize)
    (out2 : Array U8 3#usize)
    (result : Array U8 3#usize)
    (h1 : out1 = out.set 0#usize a)
    (h2 : out2 = out1.set 1#usize b)
    (h3 : result = out2.set 2#usize c) :
    result[0]!.val + result[1]!.val +
    result[2]!.val =
    a.val + b.val + c.val := by
  flatten_updates

end Test
