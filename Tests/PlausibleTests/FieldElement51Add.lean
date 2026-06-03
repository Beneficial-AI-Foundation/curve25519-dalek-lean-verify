/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign
import Curve25519Dalek.Plausible

/-! # Plausible test for `FieldElement51::add`

Property-based test exercising the `Arbitrary`/`Shrinkable` infrastructure from
`Curve25519Dalek.Plausible`. This file lives in the `Tests` library, which is **not**
part of `defaultTargets`, so the randomized `#eval` below does not run on a normal
`lake build`. Run it explicitly with `lake build Tests`.

`FieldElement51::add` performs element-wise addition of field-element limbs.

Source: curve25519-dalek/src/backend/serial/u64/field.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
open CoreOpsArithAddAssignSharedAFieldElement51

namespace curve25519_dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51

/-! ## Plausible test for `add`

The spec has preconditions `ha : ∀ i < 5, a[i]!.val < 2^53` (and similarly for `b`).
Quantifying over the plain array type and filtering via the hypothesis would almost never
produce valid test cases (probability ≈ 1/2^110), causing Plausible to "give up".

The fix is to quantify directly over the bounded subtype
`{ a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 }`.
`varTestable` then uses our `Arbitrary` instance from `Plausible.lean` to generate
bounded arrays by construction, and `.val` extracts the underlying array for `add`. -/

-- ✓ Correct spec — Plausible finds no counter-example (bounded subtype sampling active).
#eval Plausible.Testable.check
  (∀ (a : { a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 })
     (b : { b : Array U64 5#usize // ∀ i < 5, b[i]!.val < 2^53 }),
   WP.spec (add a.val b.val) (fun (result : Array U64 5#usize) =>
     (∀ i < 5, (result[i]!.val : ℕ) = a.val[i]!.val + b.val[i]!.val) ∧
     (∀ i < 5, result[i]!.val < 2^54)))
  (cfg := { numInst := 1000 })

-- -- ✗ Wrong spec — Plausible finds a counter-example immediately.
-- #eval Plausible.Testable.check
--   (∀ (a : { a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 })
--      (b : { b : Array U64 5#usize // ∀ i < 5, b[i]!.val < 2^53 }),
--    WP.spec (add a.val b.val) (fun (result : Array U64 5#usize) =>
--      ∀ i < 5, result[i]!.val < 2^50))
--   (cfg := { numInst := 1000 })

end CoreOpsArithAddSharedAFieldElement51FieldElement51
end curve25519_dalek.Shared0FieldElement51.Insts
