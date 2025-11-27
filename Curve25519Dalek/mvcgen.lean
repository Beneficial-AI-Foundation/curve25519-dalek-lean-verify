import Aeneas
import Std.Do

namespace Aeneas

namespace Std

universe u

open Result
open Std.Do
open Std.Do.PredTrans

/-!

# mvcgen Integration for Aeneas

This file provides the Hoare triple instance for Aeneas's `Result` monad,
enabling `mvcgen` to work with programs extracted by Aeneas.

The `WP` (Weakest Precondition) instance allows `Std.Do.Triple` to generate
verification conditions for imperative programs written using Aeneas's `Result` monad.
-/

/-- We interpret `Result` as an exception monad whose error type is `Error`.
    Divergence (`div`) is treated as non-termination and hence an impossible precondition. -/
abbrev ResultError := ULift.{u} Error
abbrev ResultPostShape : PostShape.{u} := .except ResultError .pure

/-- Weakest-precondition transformer for `Result`. -/
def Result.wp {α : Type u} (x : Result α) : PredTrans ResultPostShape α :=
  { apply := fun Q =>
      match x with
      | ok v   => Q.1 v
      | fail e => Q.2.fst ⟨e⟩
      | div    => ⌜False⌝
    conjunctive := by
      intro Q₁ Q₂
      cases x <;> simp }

@[simp] lemma Result.wp_apply_ok {α : Type u} (v : α) (Q : PostCond α ResultPostShape) :
    (Result.wp (.ok v)).apply Q = Q.1 v := by rfl

@[simp] lemma Result.wp_apply_fail {α : Type u} (e : Error) (Q : PostCond α ResultPostShape) :
    (Result.wp (.fail e)).apply Q = Q.2.fst ⟨e⟩ := by rfl

@[simp] lemma Result.wp_apply_div {α : Type u} (Q : PostCond α ResultPostShape) :
    (Result.wp (@Result.div α)).apply Q = ⌜False⌝ := by rfl

instance : LawfulMonad Result := LawfulMonad.mk'
  (m := Result)
  (id_map := by intro α x; cases x <;> rfl)
  (pure_bind := by intro α β a f; rfl)
  (bind_assoc := by intro α β γ x f g; cases x <;> rfl)

/-- `WP` instance for `Result`, exposing the exception barrel for `fail`. -/
instance Result.WP : WP Result ResultPostShape where
  wp := Result.wp

/-- `WPMonad` instance showing that `Result.wp` is a monad morphism. -/
instance Result.wpMonad : WPMonad Result ResultPostShape where
  wp := Result.wp
  wp_pure := by
    intro α a; rfl
  wp_bind := by
    intro α β x f; cases x <;> rfl

/-- Helper lemma mirroring `Std.Do.Id.of_wp_run_eq` that lets us discharge
`Result` goals by proving the corresponding weakest-precondition obligation. -/
theorem Result.of_wp_run_eq {α : Type u} {x : α} {prog : Result α}
    (h : prog = Result.ok x) (P : α → Prop) :
    (⊢ₛ wp⟦prog⟧ (⇓ a => ⌜P a⌝)) → P x := by
  intro hspec
  subst h
  have hx := hspec True.intro
  simpa [Result.wp, PostCond.noThrow] using hx

/-- Extract a property from a Result via the weakest-precondition transformer.
    The postcondition has shape `(α → Assertion) × ((ResultError → Assertion) × PUnit)`. -/
theorem Result.of_wp {α : Type u} {x : Result α} (P : Result α → Prop) :
    (⊢ₛ wp⟦x⟧ (fun a => ⌜P (.ok a)⌝, (fun e => ⌜P (.fail e.down)⌝, ⟨⟩))) → P x := by
  intro hspec
  cases x with
  | ok v =>
    have hx := hspec True.intro
    simp only [WP.wp, Result.wp_apply_ok] at hx
    exact hx
  | fail e =>
    have hx := hspec True.intro
    simp only [WP.wp, Result.wp_apply_fail] at hx
    exact hx
  | div =>
    have hx := hspec True.intro
    simp only [WP.wp, Result.wp_apply_div] at hx
    exact hx.elim


end Std

end Aeneas

/-

alok:

- [ ] look at aeneas.std.primitives in aeneas source code

ref: https://lean-lang.org/doc/reference/latest/The--mvcgen--tactic

see `18.1.7. Extending mvcgen With Support for Custom Monads`

goal: implement for aeneas primitive monad types

may need to implement monad and lawfulMonad too

then implement WP and WPMonad (see ref)

-/
