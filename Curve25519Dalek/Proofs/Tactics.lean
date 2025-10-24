/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Mathlib

/-! # Custom Tactics

This file contains custom tactics used throughout the verification project.
-/

open Lean Elab Tactic Meta

/--
Expand a universal quantifier hypothesis `h : ∀ i < n, P i` into individual hypotheses
`h_0 : P 0`, `h_1 : P 1`, ..., `h_{n-1} : P (n-1)`.

Usage: `expand h with 5` creates hypotheses `h_0`, `h_1`, `h_2`, `h_3`, `h_4`.

The bound `n` must be provided explicitly. Each hypothesis is proven using `omega`.

Example:
```lean
h : ∀ i < 5, a[i]! < 100
expand h with 5
-- Now have h_0 : a[0]! < 100, h_1 : a[1]! < 100, ..., h_4 : a[4]! < 100
```
-/
elab "expand " h:ident " with " n:num : tactic => do
  let n := n.getNat
  for i in [:n] do
    let newName := h.getId.appendAfter s!"_{i}"
    evalTactic (← `(tactic| have $(mkIdent newName) := $h $(quote i) (by omega)))
