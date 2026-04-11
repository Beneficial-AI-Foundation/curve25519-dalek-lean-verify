/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Aeneas

/-! # `expand_array` tactic

Given an array `result` built through a chain of `.set` operations,
`expand_array result` introduces hypotheses `hresult0 : result[0]! = v0`,
`hresult1 : result[1]! = v1`, etc. for every index of the array.

## Requirements
- `result` must be a local variable of type `Aeneas.Std.Array α n`
  with a literal size (the size is extracted automatically)
- The `.set` chain must be visible via defining equalities for intermediates
- Produces one hypothesis per index, named `h<varname><index>`
- Only intermediate array variables in the `.set` chain are consumed;
  unrelated hypotheses are left untouched
-/

open Lean Elab Tactic Meta Aeneas.Std

/-- Extract the array size `n` from the type `Aeneas.Std.Array α n` of a variable.
    The Usize literal is reduced to a Nat via `whnf`. -/
private def getArraySize (fvarId : FVarId) : MetaM Nat := do
  let ty ← Meta.inferType (mkFVar fvarId)
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  unless fn.isConstOf ``Aeneas.Std.Array && args.size ≥ 2 do
    throwError "expand_array: variable is not an Aeneas.Std.Array"
  let usizeArgs := args[1]!.getAppArgs
  unless usizeArgs.size ≥ 1 do
    throwError "expand_array: could not parse array size"
  let reduced ← whnf usizeArgs[0]!
  match reduced with
  | .lit (.natVal n) => return n
  | _ => throwError "expand_array: array size is not a literal (got {reduced})"

/-- Find a hypothesis of the form `fvarId = rhs` in the local context. -/
private def findDefEq (lctx : LocalContext) (fvarId : FVarId) :
    Option (FVarId × Expr) :=
  lctx.foldl (init := none) fun acc d =>
    match acc with
    | some _ => acc
    | none =>
      match d.type.eq? with
      | some (_, lhs, rhs) =>
        if lhs.isFVar && lhs.fvarId! == fvarId then some (d.fvarId, rhs)
        else none
      | none => none

/-- If `e` is `base.set idx val`, return the fvarId of `base`. -/
private def extractSetBase (e : Expr) : Option FVarId :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  if fn.isConstOf `Aeneas.Std.Array.set && args.size ≥ 5 then
    if args[2]!.isFVar then some args[2]!.fvarId!
    else none
  else none

/-- Walk the `.set` chain from `resultFVar`'s defining equality, collecting
    the equality hypothesis fvarIds for each intermediate array variable.
    Returns them in bottom-up order (ready for `substCore`). -/
private partial def collectChainAux (lctx : LocalContext) (rhs : Expr)
    (acc : Array FVarId) : Array FVarId :=
  match extractSetBase rhs with
  | none => acc
  | some baseFVar =>
    match findDefEq lctx baseFVar with
    | none => acc
    | some (hFVar, nextRhs) => collectChainAux lctx nextRhs (acc.push hFVar)

private def collectChainEqs (lctx : LocalContext) (resultFVar : FVarId) :
    Array FVarId :=
  match findDefEq lctx resultFVar with
  | none => #[]
  | some (_, rhs) => (collectChainAux lctx rhs #[]).reverse

/-- `expand_array result` introduces hypotheses `hresult0 : result[0]! = v0`,
    `hresult1 : result[1]! = v1`, etc. for an array built through `.set` chains.

    The array size is inferred from the type. Only intermediate array variables
    in the `.set` chain for `result` are substituted; other hypotheses in the
    context are left untouched. -/
elab "expand_array " x:ident : tactic => do
  withMainContext do
    let xName := x.getId
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? xName
      | throwError "expand_array: variable '{xName}' not found"
    let n ← getArraySize decl.fvarId
    -- Collect intermediate chain equalities before any context modification
    let chainEqs := collectChainEqs lctx decl.fvarId
    -- Revert result to protect it from substitution
    let goal ← getMainGoal
    let (_, goal) ← goal.revert #[decl.fvarId]
    replaceMainGoal [goal]
    -- Targeted substitution: only the intermediates in the .set chain
    let mut fvarSubst : FVarSubst := {}
    for hFVar in chainEqs do
      let goal ← getMainGoal
      let mapped := fvarSubst.get hFVar
      if mapped.isFVar then
        let (newSubst, newGoal) ← substCore goal mapped.fvarId!
        fvarSubst := fvarSubst.append newSubst
        replaceMainGoal [newGoal]
    -- Re-introduce result and its defining equality
    let goal ← getMainGoal
    let (resultFVar, goal) ← goal.intro xName
    let (hEqFVar, goal) ← goal.intro `h_expand_eq_
    replaceMainGoal [goal]
    -- Build hypotheses via congrArg at the meta level (no evalTactic per index)
    let hIdents : Array (TSyntax `ident) :=
      (Array.range n).map fun k => mkIdent (Name.mkSimple s!"h{xName}{k}")
    for k in [:n] do
      withMainContext do
        let kLit := Syntax.mkNumLit (toString k)
        let resultK ← Lean.Elab.Term.elabTerm (← `(($x)[$kLit]!)) none
        let f ← mkLambdaFVars #[mkFVar resultFVar] resultK
        let proof ← mkCongrArg f (mkFVar hEqFVar)
        let proofType ← inferType proof
        let hName := Name.mkSimple s!"h{xName}{k}"
        let goal ← getMainGoal
        let goal ← goal.assert hName proofType proof
        let (_, goal) ← goal.intro1P
        replaceMainGoal [goal]
    -- Clean up internal equality
    let goal ← getMainGoal
    let goal ← goal.clear hEqFVar
    replaceMainGoal [goal]
    -- Single simp call to resolve .set chains, targeting only generated hypotheses
    evalTactic (←
      `(tactic|
        simp (discharger := agrind) only [
          Array.getElem!_Usize_set_eq,
          Array.getElem!_Usize_set_ne,
          Array.getElem!_Nat_set_eq,
          Array.getElem!_Nat_set_ne,
          Array.set_length,
          Array.length_eq] at $hIdents:ident*))

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
  -- Now hresult0 : result[0]! = v0
  --     hresult1 : result[1]! = v1, etc.
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
  rw [hresult0, hresult1, hresult2]

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
  exact ⟨hresult0, hresult1, hresult2⟩

-- Test 4: other hypotheses in context are not modified
example
    (out : Array U64 3#usize)
    (v0 v1 v2 : U64)
    (out1 : Array U64 3#usize)
    (out2 : Array U64 3#usize)
    (result : Array U64 3#usize)
    (other : Array U64 3#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : out2 = out1.set 1#usize v1)
    (h3 : result = out2.set 2#usize v2)
    (hother : other[0]!.val + other[1]!.val = 100) :
    result[0]! = v0 ∧ other[0]!.val + other[1]!.val = 100 := by
  expand_array result
  -- hother should still be in context unchanged
  exact ⟨hresult0, hother⟩

end Test
