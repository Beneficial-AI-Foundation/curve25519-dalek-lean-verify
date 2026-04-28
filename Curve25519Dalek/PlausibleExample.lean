-- Example: using Plausible to catch a specification error.
--
-- Subject: `backend.serial.u64.field.FieldElement51.reduce`
--   Normalises a FieldElement51 by masking each limb to 51 bits and
--   propagating the carries (limb[4]'s carry is folded back via ×19).
--   It takes any input without preconditions and always returns ok.
--
-- Run with:  lake env lean Curve25519Dalek/PlausibleExample.lean

import Curve25519Dalek.Plausible

open Plausible Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek

private abbrev FE := backend.serial.u64.field.FieldElement51
private abbrev reduce := backend.serial.u64.field.FieldElement51.reduce

/-! ## ❌ Wrong spec — Plausible finds a counterexample

Claim: `reduce` is the identity (every output limb equals the input limb).

This is false as soon as any limb has bits above position 50: `reduce`
masks those bits away and carries them into the next limb, changing both
the masked limb and its neighbour.  Plausible will produce a counterexample
almost immediately. -/

#eval Plausible.Testable.check (∀ (fe : FE),
  WP.spec (reduce fe) (fun result =>
    result[0]!.val = fe[0]!.val ∧ result[1]!.val = fe[1]!.val ∧
    result[2]!.val = fe[2]!.val ∧ result[3]!.val = fe[3]!.val ∧
    result[4]!.val = fe[4]!.val))

/-! ## ✓ Correct spec — Plausible finds no counterexample

Claim: every output limb fits in 52 bits.

After one masking pass and carry propagation, each limb is bounded by
2^52.  This is the actual post-condition proved in `reduce_spec`. -/

#eval Plausible.Testable.check (∀ (fe : FE),
  WP.spec (reduce fe) (fun result =>
    result[0]!.val < 2^52 ∧ result[1]!.val < 2^52 ∧ result[2]!.val < 2^52 ∧
    result[3]!.val < 2^52 ∧ result[4]!.val < 2^52))
