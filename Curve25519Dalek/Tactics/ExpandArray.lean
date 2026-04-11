/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # `expand_array` tactic

Given an array `result` built through a chain of `.set` operations,
`expand_array result` introduces hypotheses `h_result_0 : result[0]! = v0`,
`h_result_1 : result[1]! = v1`, etc. for every index of the array.

## Requirements
- `result` must be a local variable of type `Aeneas.Std.Array α n`
  with a literal size (the size is extracted automatically)
- The `.set` chain must be visible (call `subst_vars` first if needed)
- Produces one hypothesis per index, named `h_<varname>_<index>`
- Intermediate array variables are consumed by `subst_vars`
-/

open Lean Elab Tactic Meta Aeneas.Std

private def getArraySize (fvarId : FVarId) : MetaM Nat := do
  let ty ← Meta.inferType (mkFVar fvarId)
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  unless fn.isConstOf ``Aeneas.Std.Array && args.size ≥ 2 do
    throwError "expand_array: variable is not an Aeneas.Std.Array"
  -- args[1] is the Usize expression, e.g. @Usize.ofNat 5 proof
  let usizeArgs := args[1]!.getAppArgs
  unless usizeArgs.size ≥ 1 do
    throwError "expand_array: could not parse array size"
  let reduced ← whnf usizeArgs[0]!
  match reduced with
  | .lit (.natVal n) => return n
  | _ => throwError "expand_array: array size is not a literal (got {reduced})"

elab "expand_array " x:ident : tactic => do
  withMainContext do
    let xName := x.getId
    -- Find the variable
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? xName
      | throwError "expand_array: variable '{xName}' not found"
    let n ← getArraySize decl.fvarId
    -- subst_vars, protecting result by revert/intro
    -- Also revert hypotheses that depend on result
    let goal0 ← getMainGoal
    let (_, goal1) ← goal0.revert #[decl.fvarId]
    replaceMainGoal [goal1]
    evalTactic (← `(tactic| subst_vars))
    -- Re-introduce result and its defining equality as a hyp
    let goal2 ← getMainGoal
    let (_, goal3) ← goal2.intro xName
    let (hEqFVar, goal4) ← goal3.intro `h_expand_eq_
    replaceMainGoal [goal4]
    -- Now context has: result, h_expand_eq_ : result = <.set chain>
    -- For each index, introduce h_<name>_k with chain on the RHS
    let eqIdent := mkIdent `h_expand_eq_
    for k in [:n] do
      withMainContext do
        let kLit := Syntax.mkNumLit (toString k)
        let hName := Name.mkSimple s!"h_{xName}_{k}"
        let hIdent := mkIdent hName
        -- Introduce trivial equality, then rewrite RHS to the .set chain
        evalTactic (←
          `(tactic| have $hIdent : ($x)[$kLit]! = ($x)[$kLit]! := rfl))
        evalTactic (←
          `(tactic| conv at $hIdent => rhs; rw [$eqIdent:ident]))
    -- Clean up internal hypothesis by fvarId (name may be inaccessible)
    let goal5 ← getMainGoal
    let goal6 ← goal5.clear hEqFVar
    replaceMainGoal [goal6]
    -- Simplify all .set chains in one pass
    evalTactic (←
      `(tactic|
        simp (discharger := agrind) only [
          Array.getElem!_Usize_set_eq,
          Array.getElem!_Usize_set_ne,
          Array.getElem!_Nat_set_eq,
          Array.getElem!_Nat_set_ne,
          Array.set_length,
          Array.length_eq] at *))

/-! ## Tests -/

section Test
open Aeneas.Std

-- Test 1: basic 5-element array
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
    (hgoal : v0.val + v1.val = 42) :
    result[0]!.val + result[1]!.val = 42 := by
  expand_array result
  -- Now h_result_0 : result[0]! = v0
  --     h_result_1 : result[1]! = v1, etc.
  simp only [*]

-- Test 2: 3-element U8 array
example
    (out : Array U8 3#usize)
    (a b c : U8)
    (out1 : Array U8 3#usize)
    (out2 : Array U8 3#usize)
    (result : Array U8 3#usize)
    (h1 : out1 = out.set 0#usize a)
    (h2 : out2 = out1.set 1#usize b)
    (h3 : result = out2.set 2#usize c) :
    result[0]!.val + result[1]!.val + result[2]!.val =
    a.val + b.val + c.val := by
  expand_array result
  rw [h_result_0, h_result_1, h_result_2]

-- Test 3: partial updates (index 1 not set)
example
    (out : Array U64 3#usize)
    (v0 v2 : U64)
    (out1 : Array U64 3#usize)
    (result : Array U64 3#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : result = out1.set 2#usize v2) :
    result[0]! = v0 ∧
    result[1]! = out[1]! ∧
    result[2]! = v2 := by
  expand_array result
  exact ⟨h_result_0, h_result_1, h_result_2⟩

end Test
