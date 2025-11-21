import Aeneas
import Std.Do

namespace Aeneas

namespace Std

open Result
open Std.Do

/-!
# mvcgen Integration for Aeneas

This file provides the Hoare triple instance for Aeneas's `Result` monad,
enabling `mvcgen` to work with programs extracted by Aeneas.

The `WP` (Weakest Precondition) instance allows `Std.Do.Triple` to generate
verification conditions for imperative programs written using Aeneas's `Result` monad.
-/

/-- Weakest precondition transformer for `Result` monad -/
def Result.wp_apply {α : Type*} (x : Result α) (Q : PostCond α PostShape.pure) : Assertion PostShape.pure :=
  match x with
  | ok v => Q.1 v
  | fail _ => ULift.up False
  | div => ULift.up False

/-- WP instance for `Result` monad using PostShape.pure -/
instance : WP Result PostShape.pure where
  wp := fun {α} (x : Result α) => {
    apply := Result.wp_apply x
    conjunctive := by
      simp [PredTrans.Conjunctive]
      intro Q1 Q2
      match x with
      | ok v => simp [Result.wp_apply]
      | fail e => simp [Result.wp_apply]
      | div => simp [Result.wp_apply]
  }

end Std

end Aeneas
