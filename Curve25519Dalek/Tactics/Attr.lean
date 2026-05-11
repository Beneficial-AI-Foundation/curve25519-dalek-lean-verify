/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Mathlib.Tactic.Attr.Register

/-! # Simp attributes for project tactics

`register_simp_attr` has a Lean 4 limitation: the attribute it declares cannot be
used in the same file. So all project simp-attr registrations live here, and the
files that tag lemmas (or define tactics that consume the set) import this. -/

/-- Simp set used by the `array_post_nf` tactic. See
`Curve25519Dalek/Tactics.lean` for the tactic and its main lemma tags. Tag a
lemma at its definition site with `@[array_post_nf]` to add it to the set. -/
register_simp_attr array_post_nf
