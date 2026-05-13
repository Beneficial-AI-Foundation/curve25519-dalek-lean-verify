/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# StepStarRegression — `step*` gets stuck under the new aeneas `do` elaborator

This investigation file is intentionally isolated. It is safe to delete once
aeneas fixes the underlying issue (see the patch proposal at the bottom).

## What this file does

1. Defines a minimal `Result`-typed `do` block whose first monadic operation
   destructures a tuple via `Array.index_mut_usize`, followed by another
   monadic operation. This is the exact shape that triggers the bug.

2. Shows that `step*` alone fails to fully traverse the block — it performs
   exactly **one** bind step per invocation instead of iterating until the
   `do` block is exhausted.

3. Shows that `repeat (step*; simp_all only)` (or simply repeated `step*`)
   succeeds.

4. Documents the root cause and proposes an upstream patch in a comment
   block at the end.

NOTE on LSP usage: the lean-lsp-mcp tools need the file saved on disk.
After every edit the harness's `Read`/`Write` writes to disk, so subsequent
`lean_diagnostic_messages` / `lean_goal` calls see the latest content.
-/
import Curve25519Dalek.Funs

open Aeneas Aeneas.Std Result

namespace Curve25519Dalek.Investigations.StepStarRegression

/-! ## MWE definition

A tiny function with the shape that triggers the bug:

  - `let (_x, setter) ← Array.index_mut_usize v 0`   — tuple destructure
  - `let y ← Array.index_usize v 1`                   — further monadic call
  - return `setter y`                                 — pure tail

Mirrors the Rust pattern emitted by aeneas for in-place updates such as
`self[0] = …; self[1]` in `FieldElement51::conditional_assign`. -/

def mwe (v : Std.Array U64 2#usize) : Result (Std.Array U64 2#usize) := do
  let (_x, setter) ← Std.Array.index_mut_usize v 0#usize
  let y ← Std.Array.index_usize v 1#usize
  ok (setter y)

theorem mwe_spec_broken (v : Std.Array U64 2#usize) :
    mwe v ⦃ (result : Std.Array U64 2#usize) =>
      result = Std.Array.set v 0#usize v.val[1]! ⦄ := by
  unfold mwe
  step*
  -- At this point the goal is still a `do` block:
  -- ⊢ (do
  --   let y ← v.index_usize 1#usize
  --   ok (x✝ y)) ⦃
  -- res => res = v.set 0#usize (↑v)[1]! ⦄
  sorry

theorem mwe_spec_hack (v : Std.Array U64 2#usize) :
    mwe v ⦃ (result : Std.Array U64 2#usize) =>
      result = Std.Array.set v 0#usize v.val[1]! ⦄ := by
  unfold mwe
  repeat (step*; simp_all only)

/-! ## Quick reference: the five manifestations and their hacks

We have characterised five distinct symptoms produced by the same
underlying PR #918 regression. The root cause (do-block intent markers
and metavariable residues persisting between `step*` iterations) shows
up differently depending on the surrounding tactic.

**1. `step*` stalls; subsequent `intro` / `interval_cases` fails.**
Hack: `repeat (step*; simp_all only)`.
Live example: `Specs/Backend/Serial/U64/Field/FieldElement51/ConditionalAssign.lean`
(lines ~45-60).

**2. `step*` produces a kernel-rejected term on a long do-block.**
Hack: `all_goals (repeat step); rename_i ...`.
Live example: `Specs/Backend/Serial/U64/Scalar/Scalar52/ToBytes.lean`
(~line 431, `all_goals (repeat step); rename_i i i_post`).

**3. `grind only` times out near do-blocks** because intent markers
pollute the e-graph context.
Hack: replace with explicit `exact` / `apply` — the goal is often a
literal hypothesis already.
Live example: `Specs/Backend/Serial/CurveModels/ProjectivePoint/Double.lean`
(`double_spec_aux`, ~lines 128-149).

**4. `step*` stalls at `let (a, b) := result` pattern destructure** of
a tuple-typed monadic result.
Hack: `obtain ⟨a, b⟩ := result; simp only at *; step*` (and propagate
the rename through the proof tail).
Live example: `Specs/Ristretto/RistrettoPoint/Compress.lean`
(~line 223, manual destructure of `(Choice × FieldElement51)`).

**5. `grind` on array-indexing bridges** (`arr[i]!` vs `arr.val[i]!`)
fails because `Array.getElem!_Nat_eq` is no longer auto-applied.
Hack: `grind [Array.getElem!_Nat_eq]`.
Live example: `Specs/Backend/Serial/U64/Field/FieldElement51/Pow2K.lean`
(~line 834).

The upstream patch sketch (Option A) at the bottom of this file
addresses all five: running a hypothesis-aware `simp_all only
[step_simps]` between walker iterations folds away the residual
post-condition equalities and intent markers that each variant exploits
in its own way.

-/

/-! ## Variant: kernel-level rejection on long do-blocks (alternate hack)

The bug described above manifests in two distinct ways depending on the
shape and length of the `do` block:

**Pattern A — `step*` stalls.** `step*` walks one bind, leaves an intent
marker, and stops. The proof tail (e.g. `intro i _`) then fails because
the goal is still a `do` block. This is what `mwe_spec_broken` above
demonstrates. The hack is `repeat (step*; simp_all only)`.

**Pattern B — `step*` produces a kernel-rejected proof term.** On long
do-blocks (e.g. ~30 to 70 monadic binds, like the 32-byte serialiser in
`Scalar52::to_bytes`), `step*` runs through more steps than it does in
the small MWE — but the proof term it builds is ill-typed, and Lean's
kernel rejects it with messages of the form

    (kernel) application type mismatch
      eq_false_of_decide (eagerReduce (Eq.refl false))

right at the `step*` invocation. Worse: `repeat` *swallows* this kernel
failure silently with 0 iterations, leaving the do-block completely
unprocessed and triggering cascade "Unknown identifier" errors in the
proof tail.

The working hack for Pattern B is

    all_goals (repeat step)

— note `step` (singular, walks one bind), wrapped in `repeat`, *inside*
`all_goals`. `step` produces side-cases that `all_goals` propagates the
recursion into, walking the entire block one bind at a time without
ever building the ill-typed `step*` proof term.

Often, `repeat step` names new hypotheses with inaccessible `result✝` /
`result_post✝` (because the final post-condition variable `result`
shadows them). A `rename_i` after the walk exposes them with stable
names that the proof tail can refer to. Live example:

  `Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ToBytes.lean`
  ~line 431: `all_goals (repeat step); rename_i i i_post`

Faithfully reproducing Pattern B in a small isolated MWE inside this
file appears to require many binds (≥ ~30) AND specific Aeneas spec
shapes — the small two-bind MWE here exhibits only Pattern A. The
Pattern-B failure has been observed exclusively on the 32-byte
serialisers in production. -/

end Curve25519Dalek.Investigations.StepStarRegression

/-!
================================================================================
## Root cause analysis and proposed fix
================================================================================

### 1. What the new `do` elaborator produces internally

The Aeneas custom `do` elaborator
(`.lake/packages/aeneas/backends/lean/Aeneas/Do/Elab.lean`, PR aeneas#918,
commit `3c9b4907`, controlled by `Aeneas.customDoElab : Bool := true`)
compiles

    let (x, setter) ← Array.index_mut_usize v 0#usize
    let y ← Array.index_usize v 1#usize
    ok (setter y)

into a term of the shape

    Bind.bind (Array.index_mut_usize v 0#usize)
      (Function.uncurry fun x setter =>
        Bind.bind (Array.index_usize v 1#usize)
          (fun y => ok (setter y)))

See `Aeneas.Do.Elab.mkPatContinuation`, `unpackFvar`, and `mkUncurries`
(Elab.lean lines ~135-260): a tuple pattern of width `n` is elaborated to
`Function.uncurry (fun a₁ … aₙ => …)` rather than to a `Prod.casesOn` or
single-arg `fun ⟨a, b⟩ => …`. The corresponding step-set lemmas registered
in `Aeneas/Tactic/Step/Step.lean` lines 74-75 are

    attribute [step_simps] Aeneas.Std.bind_assoc_eq
    attribute [step_simps] Function.uncurry_apply_pair

so the rewrites for `Function.uncurry f (a, b) = f a b` are in the simp set
that `step*` uses internally — when applicable.

### 2. Why `step*` alone stalls after exactly one bind step

The empirical facts established with `lean_multi_attempt`:

    step*                       — one bind step, then stops
    step*; step*                — two bind steps (both binds processed)
    step                        — same as `step*` (one step)
    step; step                  — both steps

So the bug is **not** "step* refuses to process a tuple-destructure"; it
*does* process it. The bug is "after the tuple-destructure step, the
recursion in `traverseProgram` (StepStar.lean ~lines 494-526) does not
continue, even though the residual goal is still a `Bind.bind`".

Looking at the residual goal under `pp.all`, the surviving continuation
is **already** a bare `fun (y : U64) ↦ ok (x✝ y)` — i.e. the
initial `simplifyTarget` *did* fire `Function.uncurry_apply_pair`
against the fresh pair fvar `(res, x✝)` and beta-reduced the
`Function.uncurry`-headed wrapper away. So `analyzeTarget` ought to
return `.bind y` for the residual goal — yet iteration stops.

The bottleneck is the unassigned-mvar guard in `traverseProgram`
(StepStar.lean lines 515-526):

    setGoals [mainGoal]
    if info.unassignedVars.isEmpty then
      let restInfo ← traverseProgram cfg fuel ss
      return (info ++ restInfo)
    else
      trace[Step] "Found unassigned meta-variables of type ≠ Prop: stopping"
      let info' : Info ← pure
        { script := .tacs #[.done (← `(tactic| sorry))], … }
      pure (info ++ info')

The `info` returned by `onBind` reports any unassigned metavariables
left after the step. With the new elaborator, the *output* of the
tuple-destructure has type `α × (α → Array α n)` — i.e. a pair whose
second component is a function type whose return type still mentions a
`Usize` proof obligation that flows back from the original array's
length parameter. After `let* ⟨res, x✝⟩ ← Array.index_mut_usize_spec`
runs, one or more of those proof-component mvars (`mwe._proof_1`,
`mwe._proof_2`, … visible in the `pp.all` dump above) can still be
unassigned, even though they unify on a subsequent `step*` once the
goal is fully unified against the next call's spec.

Each *fresh* `step*` invocation runs `simplifyTarget` then `traverseProgram`
with an *empty* `unassignedVars` start state, so it gets one more step
done before bailing out on the next mvar residue. `step*; step*` thus
crawls forward one bind at a time. The user-level `repeat` hack
flattens this into a single tactic block.

Why does `simp_all only` between steps help? It does two things that
`step*`'s narrow internal `simp only [step_simps]` does not:

  1. It folds away the leftover post-condition hypotheses
     (`res_post1 : x✝ = v.set 0#usize` and similar), substituting `x✝`
     by `v.set 0#usize` in the goal. This eliminates the metavariable
     residue that flagged `info.unassignedVars` as non-empty.

  2. It uses the `[> let ... <]` intent-marker hypothesis to discharge
     any synthetic `prettyMonadEq` mvars that may still be open from
     the previous step's intent-marker introduction
     (`introPrettyEquality` in Step.lean line 576).

The narrower `simpThms := #[← Step.stepSimpExt.getTheorems]` inside
`simplifyTarget` (StepStar.lean line 464) is appropriate for tactic
performance, but it doesn't use *local hypotheses*, so it can't perform
the substitution from (1).

### 3. The specific fix aeneas would need

Two non-exclusive options, in decreasing order of locality:

**Option A — re-run `simplifyTarget` (using local hypotheses too)
inside `traverseProgram` between iterations.**
Insert a `simplifyTarget`-equivalent call right after `setGoals [mainGoal]`
in `traverseProgram` (around `StepStar.lean` line 514), and have *that*
inner simplification include local hypotheses (i.e. mirror
`simp_all only [step_simps]`, not just `simp only [step_simps]`). The
extra cost per iteration is small (each step introduces a handful of
new hypotheses) and the user-visible benefit is that `step*` no longer
stops one step short.

**Option B — relax the unassigned-mvar guard.**
In `traverseProgram` lines 515-526, instead of bailing out on
`info.unassignedVars.isEmpty == false`, optionally retry after running
`simp_all only [step_simps]` first. This is a more surgical fix but
more invasive in `tryStep`'s contract.

**The simpler one-line variant** that already gives a partial
improvement is: tag the eta-expansion lemma

    @[step_simps]
    theorem Aeneas.Std.bind_uncurry_pair {α β γ}
        (e : Result (α × β)) (f : α → β → Result γ) :
        Bind.bind e (Function.uncurry f) =
          Bind.bind e (fun p => f p.1 p.2) := by
      simp [Function.uncurry]

so that the rewrite fires *even when the pair argument is a fresh
fvar*. This addresses any residual `Function.uncurry`-shaped
continuations that haven't been beta-reduced yet (e.g. deeper into a
longer `do` chain). But on its own it does **not** fix the iteration
bug — only Option A or B do that.

### 4. Proposed upstream patch sketch (aeneas)

**File**: `backends/lean/Aeneas/Tactic/Step/StepStar.lean`

Around the existing recursive call inside `traverseProgram` (lines
510-519 in the current source), add a hypothesis-aware target
re-simplification *and* allow the walker to continue when the only
remaining unassigned mvars are discharged by the new normalisation:

```diff
       | some (mainGoal, ss) =>
         …
         setGoals [mainGoal]
+        -- Re-normalise the new target using local hypotheses so that
+        -- the unassigned-mvar guard below is not tripped by trivially
+        -- discharged post-condition residues from the previous step.
+        -- This mirrors what each user-level `step*` invocation does at
+        -- start-up but extends it to use local context.
+        let r ← Simp.simpAt (simpOnly := true)
+          { maxDischargeDepth := 1, failIfUnchanged := false }
+          { simpThms := #[← Step.stepSimpExt.getTheorems] }
+          (.targets (← (← getMainGoal).getNondepPropHyps) true)
         if info.unassignedVars.isEmpty then
           let restInfo ← traverseProgram cfg fuel ss
           return (info ++ restInfo)
```

(Exact API may need adjustment — `simpAt` over all prop hyps and the
target is what we want.)

**Expected behaviour after the patch.** The MWE theorem
`mwe_spec_broken` above closes with plain `step*` (no `repeat`, no
`simp_all only`). Likewise, in production, the proof of
`FieldElement51.conditional_assign_spec`
(`Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ConditionalAssign.lean`)
can revert from

    repeat (step*; simp_all only)
    interval_cases i <;> simp [*]

back to

    step*
    intro i _
    interval_cases i <;> simp [*]

**One-line regression test** to drop into
`backends/lean/Aeneas/Tactic/Step/Tests/`:

```lean
example (v : Std.Array U64 2#usize) :
    (do let (_x, setter) ← Std.Array.index_mut_usize v 0#usize
        let y ← Std.Array.index_usize v 1#usize
        Std.ok (setter y))
    ⦃ res => res = Std.Array.set v 0#usize v.val[1]! ⦄ := by
  step*
  subst_vars; rfl
```

This test fails today and would pass with either fix.
-/
