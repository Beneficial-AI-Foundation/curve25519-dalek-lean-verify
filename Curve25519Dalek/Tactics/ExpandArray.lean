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
- Only the generated hypotheses are modified; all other context (including
  Aeneas step markers) is left untouched
-/

open Lean Elab Tactic Meta Aeneas.Std

/-- Extract the array size `n` from the type `Aeneas.Std.Array α n` of a variable. The Usize
literal is reduced to a Nat via `whnf`. -/
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

/-- Walk the `.set` chain from an expression, collecting equality hypothesis fvarIds for each
intermediate array variable. Returns them in walk order (top-down). -/
private partial def collectChainAux (lctx : LocalContext) (rhs : Expr)
    (acc : Array FVarId) : Array FVarId :=
  match extractSetBase rhs with
  | none => acc
  | some baseFVar =>
    match findDefEq lctx baseFVar with
    | none => acc
    | some (hFVar, nextRhs) => collectChainAux lctx nextRhs (acc.push hFVar)

/-- Collect ALL chain equality hypothesis fvarIds starting from the target's defining equality,
in top-down order (defining eq first, then intermediates). Suitable for `rw [h5, h4, h3, h2, h1]`
to inline the full chain. -/
private def collectAllChainEqs (lctx : LocalContext) (resultFVar : FVarId) :
    Array (TSyntax `ident) :=
  match findDefEq lctx resultFVar with
  | none => #[]
  | some (hFVar, rhs) =>
    let allFVars := #[hFVar] ++ collectChainAux lctx rhs #[]
    allFVars.map fun fvar => mkIdent (lctx.get! fvar).userName

/-- Core implementation for expanding a single array index. Produces
`h<name><k> : x[k]!.val = ...` by inlining the `.set` chain via `rw`, resolving index
comparisons via `simp (discharger := norm_num)`, then chaining through `_post` hypotheses. -/
private def expandSingleIndex (x : TSyntax `ident) (xName : Name) (k : Nat)
    (chainIdents : Array (TSyntax `ident)) : TacticM (TSyntax `ident) := do
  let kLit := Syntax.mkNumLit (toString k)
  let hIdent := mkIdent (Name.mkSimple s!"h{xName}{k}")
  -- Introduce .val rfl hypothesis, then rw chain on RHS
  evalTactic (←
    `(tactic| have $hIdent : ($x)[$kLit]!.val = ($x)[$kLit]!.val := rfl))
  evalTactic (←
    `(tactic| conv at $hIdent => rhs; rw [$[$chainIdents:ident],*]))
  -- Resolve .set chain with norm_num discharger (fast)
  let hArr := #[hIdent]
  evalTactic (←
    `(tactic|
      simp (discharger := norm_num) only [
        Array.getElem!_Nat_set_eq, Array.getElem!_Nat_set_ne,
        Array.set_length, Array.length_eq] at $hArr:ident*))
  return hIdent

/-- `expand_array x` or `expand_array x k` introduces `.val`-level hypotheses for an array built
through `.set` chains. With an index argument, only that index is expanded. The array size is
inferred from the type. Uses `norm_num` for fast index comparison. After `.set` resolution, chains
through `_post` hypotheses via `simp only [*]`. Aeneas step markers and unrelated hypotheses are
left untouched. -/
elab "expand_array " x:ident idx:(num)? : tactic => do
  withMainContext do
    let xName := x.getId
    let lctx ← getLCtx
    let some decl := lctx.findFromUserName? xName
      | throwError "expand_array: variable '{xName}' not found"
    let n ← getArraySize decl.fvarId
    let chainIdents := collectAllChainEqs lctx decl.fvarId
    -- Determine which indices to expand
    let indices := match idx with
      | some idxSyn => #[idxSyn.getNat]
      | none => (Array.range n)
    -- Expand each index
    let mut hIdents : Array (TSyntax `ident) := #[]
    for k in indices do
      let hIdent ← expandSingleIndex x xName k chainIdents
      hIdents := hIdents.push hIdent
    if idx.isNone then
      -- All-indices: clear defining eq, then chain through _post hypotheses
      withMainContext do
        if let some (hFVar, _) := findDefEq (← getLCtx) decl.fvarId then
          try let goal ← getMainGoal; replaceMainGoal [← goal.clear hFVar] catch _ => pure ()
      try evalTactic (← `(tactic| simp only [*] at $hIdents:ident*)) catch _ => pure ()

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

-- Test 3: partial updates (index 1 not set), .val level
example
    (out : Array U64 3#usize)
    (v0 v2 : U64)
    (out1 : Array U64 3#usize)
    (result : Array U64 3#usize)
    (h1 : out1 = out.set 0#usize v0)
    (h2 : result = out1.set 2#usize v2) :
    result[0]!.val = v0.val ∧
    result[1]!.val = out[1]!.val ∧
    result[2]!.val = v2.val := by
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
    result[0]!.val = v0.val ∧ other[0]!.val + other[1]!.val = 100 := by
  expand_array result
  exact ⟨hresult0, hother⟩

end Test
