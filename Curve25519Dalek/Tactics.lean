/-
Copyright 2025 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Lean
import Mathlib.Tactic
import Aeneas
import Curve25519Dalek.Tactics.Attr

/-! # Custom Tactics

This file contains custom tactics used throughout the verification project.
-/

open Lean Elab Tactic Meta
open Aeneas Aeneas.Std

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

-- The `array_post_nf` simp attribute is registered in
-- `Curve25519Dalek/Tactics/Attr.lean` (Lean 4 forbids using a `register_simp_attr`
-- attribute in the same file it's declared). Tag upstream lemmas
-- (core / std / Aeneas) here so the simp set is self-contained. Project-local
-- helpers in `Curve25519Dalek/Aux.lean` are tagged at their definition sites.
attribute [array_post_nf]
  Array.getElem!_Nat_eq Array.set_val_eq
  List.length_set List.Vector.length_val
  List.getElem_set_self List.getElem_set_ne
  UScalar.ofNatCore_val_eq getElem!_pos ne_eq
  Nat.reduceLT Nat.reduceEqDiff Nat.succ_ne_self
  Nat.lt_add_one Nat.ofNat_pos Nat.one_lt_ofNat
  OfNat.ofNat_ne_zero OfNat.ofNat_ne_one
  OfNat.zero_ne_ofNat OfNat.one_ne_ofNat
  one_ne_zero zero_ne_one
  not_false_eq_true

/--
`array_post_nf` normalizes Aeneas array read-after-write expressions of the form
`((arr.set i a).set j b ...)[k]! = e` arising from `progress`/`step*` chains.
Encapsulates the recurring `simp only [Array.set_val_eq, List.getElem_set_*, …,
limbs_N_post, …]` boilerplate scattered across `Curve25519Dalek/Specs/`.

Behavior (stage 1):
1. Collect every local hypothesis whose type is a propositional equality
   (`_ = _`). This catches `progress`/`step*` post-condition equations
   (currently named `*_post`/`*_post<N>`, but the test is shape-based so
   it survives Aeneas naming changes).
2. Fire `simp only [array_post_nf, <those hypotheses>]` — the registered
   simp set (see `Curve25519Dalek/Tactics/Attr.lean`) plus the collected
   equations.

Closes the goal if normalization makes it `rfl`; otherwise leaves whatever
residual for `scalar_tac`/`omega`/`grind` to pick up.

Deliberately does NOT call `subst_vars`, `simp_all`, `*`, or any arithmetic
tactic — the simp arguments are explicit and bounded.

Usage:
```lean
have h_l0 : limbs9.val[0]! = i18 := by array_post_nf
-- or, when a residual remains:
· array_post_nf; scalar_tac
```
-/
elab "array_post_nf" : tactic => do
  withMainContext do
    let lctx ← getLCtx
    let mut eqLemmas : TSyntaxArray ``Parser.Tactic.simpLemma := #[]
    for decl in lctx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      if type.isAppOf ``Eq then
        let lem ← `(Parser.Tactic.simpLemma| $(mkIdent decl.userName):term)
        eqLemmas := eqLemmas.push lem
    evalTactic (← `(tactic| try simp only [array_post_nf, $eqLemmas,*]))
