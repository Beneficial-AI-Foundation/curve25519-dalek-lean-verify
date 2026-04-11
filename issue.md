# `step*` tactic loses user postcondition variable names

## Summary

When a user writes a spec with a named postcondition variable (e.g., `result`), the `step*` tactic replaces it with the Aeneas-generated internal variable name (e.g., `limbs10`). This makes proofs fragile and unpredictable — the user must guess the internal name to reference the result.

## Minimal Working Example

From `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean`:

```lean
@[step]
theorem reduce_spec (limbs : Array U64 5#usize) :
    reduce limbs ⦃ (result : FieldElement51) =>
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧
      Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p] ∧
      Field51_as_Nat result < 2 * p ⦄ := by
  unfold reduce
  step*
```

The user chose the postcondition variable name `result`. After `step*` processes all the monadic steps, the remaining goal is:

```
limbs10 : Std.Array U64 5#usize
limbs10_post : limbs10 = limbs9.set 4#usize i25
⊢ (∀ i < 5, ↑limbs10[i]! < 2 ^ 52) ∧
    Field51_as_Nat limbs ≡ Field51_as_Nat limbs10 [MOD p] ∧ Field51_as_Nat limbs10 < 2 * p
```

The variable is `limbs10` (Aeneas-generated), not `result` (user-chosen).

## Why this is inconvenient

- The user must write `expand_array limbs10` instead of the predictable `expand_array result`.
- The internal name `limbs10` depends on the Aeneas translation output and can change if the Rust source or Aeneas version changes.
- Any tactic or proof step referencing the result variable is fragile.

## Root cause

The issue arises from the interaction of two mechanisms:

### Mechanism 1: `.bind` name extraction

File: `Aeneas/Tactic/Step/StepStar.lean`, lines 498-499:

```lean
| .bind varName => do
  let names := if varName.hasMacroScopes then #[] else #[some varName]
```

When `step*` processes each `let x <- ...` step, the variable name `x` comes from the continuation binder of the `Bind.bind` in the monadic program. These names are Aeneas-generated (e.g., `limbs10`, `i25`). The user's postcondition variable name is never consulted.

### Mechanism 2: `spec_ok` simplification

File: `Aeneas/Tactic/Step/Step.lean`, lines 967-968 (via `step_simps` at line 70):

After all binds are processed, the last goal has the form:
```
spec (ok limbs10) (fun result => body)
```

The `simplifyTarget` call inside `evalStepCore` applies `spec_ok : spec (ok x) p ↔ p x`, which beta-reduces the postcondition lambda:
```
(fun result => body) limbs10  -->  body[result := limbs10]
```

This substitution replaces the user's `result` with `limbs10` in the goal body. Since `limbs10` is already a concrete fvar in the context (introduced by a previous `.bind` step), the user's name `result` disappears completely.

## Detailed code flow

File: `Aeneas/Tactic/Step/StepStar.lean`

1. **`traverseProgram`** (line 485) repeatedly calls `analyzeTarget` (line 387) to classify the goal.

2. For each intermediate step, `analyzeTarget` returns `.bind varName` (lines 398-403) where `varName` comes from the program's continuation binder.

3. On the **last bind** (`let limbs10 <- Array.update ...`), `step*` introduces `limbs10` in the context (line 499 -> `onBind` -> `tryStep` -> `evalStepCore` -> `introOutputs`).

4. The remaining goal is `spec (ok limbs10) (fun result => ...)`. `analyzeTarget` returns `.result` (line 407).

5. **`onResult`** (line 572) calls `getPostNamesFromGoal` (line 583) which correctly extracts `[some result]` from the postcondition lambda.

6. `onResult` calls **`onBind`** (line 584) with `names = [some result]`.

7. Inside `onBind` -> `tryStep` (line 651) -> `evalStepCore` (line 844):
   - Line 967: `simpAt` with `step_simps` (which includes `spec_ok`) fires on `spec (ok limbs10) (fun result => body)`, simplifying to `body[limbs10/result]`.
   - The goal is no longer `spec ... ...`, so `getFirstBind` (line 224) throws at line 230.
   - `evalStepCore` propagates the exception.
   - `tryStep` catches it and returns `none` (line 845).

8. Back in `onBind`, the `else` branch (line 795) calls `onFinish`, which tries `agrind` and if that fails, leaves the goal for the user.

9. The user's remaining goal contains `limbs10` everywhere, not `result`.

## Proposed fix

**Location**: `onResult` function in `StepStar.lean`, lines 572-591.

**Strategy**: After `spec_ok` has eliminated the `spec (ok x)` wrapper, `onResult` should introduce a let-alias binding `<postName> := <programVar>` so the user can refer to the result by their chosen name.

### Concrete change (pseudo-code)

```lean
onResult (cfg : Config) (ss : Step.StepState) : TacticM (Info × Option MVarId) := do
    withTraceNode `Step (fun _ => pure m!"onResult") do
    -- Extract the user's postcondition name(s)
    let names ← Step.getPostNamesFromGoal
    -- Also extract the program variable that `ok` returns
    let resultVar? ← getOkResultVar  -- NEW: inspect `spec (ok x) post`, extract `x`
    let (info, mainGoalAndState) ← onBind cfg names ss
    match mainGoalAndState with
    | none => pure (info, none)
    | some (mvarId, _) =>
      -- NEW: if the postcondition name differs from the program variable,
      -- introduce a let-alias
      let mvarId ← do
        if let (some postName, some resultExpr) := (names[0]?.join, resultVar?) then
          if let .fvar fid := resultExpr then
            let progName ← fid.getUserName
            if postName != progName then
              -- introduce `let result := limbs10` in the context
              mvarId.withContext do
              setGoals [mvarId]
              let ty ← inferType resultExpr
              Utils.addDeclTac postName resultExpr ty (asLet := true) fun _ => do
                pure (← getMainGoal)
            else pure mvarId
          else pure mvarId
        else pure mvarId
      let (info', mvarId) ← onFinish cfg mvarId
      pure (info ++ info', mvarId)
```

### New helper

A helper `getOkResultVar` would inspect the current goal **before** simplification to extract the argument of `ok`:

```lean
/-- If the goal is `spec (ok x) post`, return the expression `x`. -/
def getOkResultVar : TacticM (Option Expr) := do
  try
    let goalTy ← (← getMainGoal).getType
    goalTy.consumeMData.withApp fun spec? args => do
    if spec?.isConstOf ``Std.WP.spec && args.size = 3 then
      let program := args[1]!
      program.consumeMData.withApp fun ok? okArgs => do
      if ok?.isConstOf ``Std.Result.ok && okArgs.size = 2 then
        return some okArgs[1]!
      else return none
    else return none
  catch _ => return none
```

This helper must be called **before** `onBind` (which triggers `spec_ok` simplification), so the extraction happens while the goal still has the `spec (ok x) post` shape.

### Alternative

Instead of introducing a let-binding, the fix could rename the fvar. However, Lean 4 does not have a straightforward fvar renaming API, so the let-binding approach (using the existing `addDeclTac`) is more practical.

## Key file paths and line numbers

All paths are relative to `.lake/packages/aeneas/backends/lean/`:

| File | Lines | What |
|---|---|---|
| `Aeneas/Tactic/Step/StepStar.lean` | 380-383 | `TargetKind` definition (`.bind`, `.result`, etc.) |
| `Aeneas/Tactic/Step/StepStar.lean` | 387-413 | `analyzeTarget` — classifies the goal |
| `Aeneas/Tactic/Step/StepStar.lean` | 485-528 | `traverseProgram` — main loop, `.bind` case at 498 |
| `Aeneas/Tactic/Step/StepStar.lean` | 558-570 | `traverseProgram` — `.result` case dispatches to `onResult` |
| `Aeneas/Tactic/Step/StepStar.lean` | 572-591 | **`onResult`** — the primary fix location |
| `Aeneas/Tactic/Step/StepStar.lean` | 583 | `getPostNamesFromGoal` — extracts `result` from postcondition |
| `Aeneas/Tactic/Step/StepStar.lean` | 648-797 | `onBind` — calls `tryStep` and handles success/failure |
| `Aeneas/Tactic/Step/StepStar.lean` | 843-845 | `tryStep` — wraps `evalStepCore` in try/catch |
| `Aeneas/Tactic/Step/Step.lean` | 70 | `spec_ok` registered in `step_simps` |
| `Aeneas/Tactic/Step/Step.lean` | 270-288 | `getPostNames` — extracts names from postcondition lambda |
| `Aeneas/Tactic/Step/Step.lean` | 292-300 | `getPostNamesFromGoal` — extracts postcondition names from goal |
| `Aeneas/Tactic/Step/Step.lean` | 959-968 | `evalStepCore` — initial `simpAt` that fires `spec_ok` |
| `Aeneas/Std/WP.lean` | 68 | `spec_ok` lemma: `spec (ok x) p <-> p x` |

## Auto-closing behavior

### How auto-closing works

When `step*` reaches the final monadic result (the goal is `spec (ok x) post` with no further `Bind.bind`), the flow is:

1. `traverseProgram` calls `analyzeTarget` which returns `.result` (line 407 in `StepStar.lean`).

2. `.result` dispatches to **`onResult`** (line 572). `onResult` extracts the user's postcondition variable names via `getPostNamesFromGoal` (line 583), then calls `onBind` (line 584).

3. Inside `onBind` (line 648), `tryStep` (line 843) calls `evalStepCore` which runs `simp only [step_simps]` on the goal. This fires `spec_ok : spec (ok x) p <-> p x`, beta-reducing the postcondition. Since this is the last step (there is no further `Bind.bind`), `evalStepCore` fails when `getFirstBind` (line 230) finds no bind. `tryStep` catches the exception and returns `none` (line 845).

4. Because `tryStep` returned `none`, `onBind` falls to the `else` branch (line 795) and calls **`onFinish`** (line 796).

5. **`onFinish`** (line 593) does two things:
   - **`simplifyTarget`** (line 598): runs `Simp.simpAt` with `step_simps` to simplify the goal. This can sometimes close the goal entirely (if the postcondition becomes trivially true after simplification).
   - If the goal survives simplification, it runs **`agrind`** (line 606-640): `evalAGrindWithPreprocess` first preprocesses with `ScalarTac.simpAsmsTarget` (arithmetic simp), then calls Lean's `grind` (actually Aeneas's augmented `agrind`) to close the goal.

6. If `agrind` succeeds, `onFinish` returns `(info, none)` (no remaining goal). If it fails, the goal is left for the user.

The key path for auto-closing is: `onResult` -> `onBind` (tryStep fails) -> `onFinish` -> `simplifyTarget` + `agrind`.

### Relevant code in `onFinish` (lines 593-646)

```lean
onFinish (cfg : Config) (mvarId : MVarId) : TacticM (Info x Option MVarId) := do
  ...
  let (info, mvarId) <- simplifyTarget   -- simp only [step_simps]
  match mvarId with
  | none => pure (info, mvarId)           -- goal already closed by simp
  | some mvarId =>
    ...
    let grindTac : TacticM Unit :=
      Step.evalAGrindWithPreprocess ...     -- preprocess then agrind
    ...
    tryFinish [("grind", <- `(tactic| agrind), grindTac)]
    ...
```

### Examples of proofs that auto-close

There are at least 67 files in the project where `step*` is the only tactic after `unfold` and fully closes the proof. Representative examples:

1. **`FieldElement51/Add.lean`** (line 38): `add` wraps `add_assign`, so the postcondition follows directly from the `add_assign` spec. `agrind` closes it.
   ```lean
   theorem add_spec ... :
       add a b {{ result => ... }} := by
     unfold add
     step*
   ```

2. **`FieldElement51/Neg.lean`** (line 37): `neg` wraps `negate`, postcondition follows from `negate_spec`. `agrind` closes it.
   ```lean
   theorem neg_spec ... :
       neg self {{ (neg : FieldElement51) => ... }} := by
     unfold neg
     step*
   ```

3. **`ProjectivePoint/Identity.lean`** (line 36): `identity` constructs a point from `ZERO` and `ONE`. The postcondition states `Field51_as_Nat` of each coordinate. `agrind` closes it using the `ZERO_spec` and `ONE_spec` facts.
   ```lean
   theorem identity_spec :
       identity {{ (result : ProjectivePoint) => ... }} := by
     unfold identity
     step*
   ```

4. **`Reduce.lean`** (line 18): `reduce` has a complex monadic body. `step*` processes all steps and `agrind` closes the remaining arithmetic postcondition.
   ```lean
   theorem reduce_spec ... :
       reduce limbs {{ (result : FieldElement51) => ... }} := by
     unfold reduce
     step*
   ```

5. **Various `ConditionalSelect`, `ConditionalAssign`, `Identity`, `Eq` specs** across `CurveModels/` and `Montgomery/`: These are simple wrapper functions where the postcondition follows from sub-specs. `agrind` closes them after `step*` processes all binds.

### Analysis of whether the proposed fix preserves auto-closing

The proposed fix introduces `let result := limbs10` in the local context **between** `onBind` returning and `onFinish` being called. The question is whether `onFinish` (specifically `simplifyTarget` then `agrind`) can still close the goal.

**The let-binding should be transparent to both `simplifyTarget` and `agrind`.** Here is why:

1. **`simplifyTarget`** runs `simp only [step_simps]`. Lean's `simp` performs zeta-reduction by default (it unfolds let-bindings in the goal). Even if the goal contained `result` after the let-binding was introduced, `simp` would substitute it back to `limbs10`, producing the same goal as without the fix. However, note that the proposed fix introduces the let-binding in the **context** (via `addDeclTac ... asLet := true`), not in the goal. The goal itself still mentions `limbs10` directly (since `spec_ok` already substituted `result := limbs10` in the goal). The let-binding `let result := limbs10` simply adds a new local definition to the context -- it does not change the goal at all.

2. **`agrind`** (via `evalAGrindWithPreprocess`): The preprocessing step runs `ScalarTac.simpAsmsTarget` which simplifies both assumptions and the target. The let-binding `let result := limbs10` in the context is a definitional equality -- `grind` internalizes it as `result = limbs10`. This gives `agrind` strictly more information, not less. If `agrind` could close the goal before, it can still close it with the extra hypothesis.

3. **The goal is unchanged**: This is the critical point. The proposed fix adds `let result := limbs10` to the context but does **not** rewrite the goal to use `result`. The goal still contains `limbs10` everywhere, exactly as it did before the fix. Therefore, `onFinish` sees the exact same goal and should behave identically.

**Conclusion**: The proposed fix preserves auto-closing behavior because it only adds information to the context without modifying the goal that `onFinish` needs to close.

### Edge cases and risks

#### 1. Postcondition mentions `result` in a way that `agrind` needs to see `limbs10` directly

This is not a risk. As explained above, the proposed fix does not change the goal -- the goal still says `limbs10` everywhere. The let-binding `result := limbs10` is only in the context. If the user later (in a non-auto-closing proof) references `result`, the let-binding is definitionally equal to `limbs10`, so any tactic can unfold it.

#### 2. Multiple return values

When the postcondition has multiple return values (e.g., a tuple), `getPostNamesFromGoal` extracts multiple names. The `.result` case in `onResult` extracts `names[0]?.join` for the first name. The proposed fix as written only introduces a let-alias for the first postcondition name. However, for the auto-closing case this is not a concern: the let-binding only adds to the context, and `onFinish` still sees the same goal regardless of how many let-bindings were added.

For correctness of the name-aliasing itself (not auto-closing), multiple return values would need multiple let-bindings. The proposed fix should be extended to handle this, but this is orthogonal to auto-closing preservation.

#### 3. Postcondition name is `_` (anonymous)

If the user writes `{{ _ => ... }}`, `getPostNamesFromGoal` returns `[none]` (the name is `none`). In the proposed fix, the check `if let (some postName, some resultExpr) := (names[0]?.join, resultVar?)` would fail because `names[0]?.join` would be `none`. The let-binding would not be introduced. This is correct behavior -- there is no user name to alias, so nothing should be done. Auto-closing is unaffected.

#### 4. Postcondition name matches the program variable

If the user happens to write `{{ limbs10 => ... }}` matching the Aeneas-generated name, the check `if postName != progName` would be false, and no let-binding would be introduced. Auto-closing is unaffected.

#### 5. `simplifyTarget` closing the goal before `agrind`

In some cases, `simplifyTarget` (the `simp only [step_simps]` pass inside `onFinish`) might close the goal entirely, returning `none`. The proposed fix introduces the let-binding **before** `onFinish` is called. Since the let-binding only adds to the context and does not change the goal, `simplifyTarget` would still close the goal exactly as before. The match on `mvarId` (line 599-600) catches this case and returns early.

#### 6. Async mode

When `cfg.stepConfig.async` is true (line 631), `onFinish` runs `agrind` asynchronously. The let-binding in the context is still present when the async task runs (it is part of the metavariable's local context). No issue.

#### 7. Performance

Adding a let-binding introduces one extra local declaration in the context. This is negligible for both `simp` and `agrind`. For proofs with very large contexts (like the arithmetic-heavy field element proofs), one extra `let` is irrelevant.

### Summary

The proposed fix is safe with respect to auto-closing. The core invariant is that the fix only adds a let-binding to the local context without modifying the goal that `onFinish` needs to close. Both `simplifyTarget` and `agrind` see the same goal as before, with strictly more context available. All 67+ auto-closing proofs in the project should continue to work unchanged.
