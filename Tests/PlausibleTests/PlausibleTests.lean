import Curve25519Dalek.Funs
import Curve25519Dalek.PlausibleDomain

/-! # Plausible tests

Tests exercising the `Arbitrary`/`Shrinkable`/`SampleableExt` infrastructure from
`Curve25519Dalek.Plausible`. Property tests are phrased as an `example` discharged by
the `plausible` tactic: it randomly samples the quantified variables and either reports
a counter-example (failing the build) or, finding none, closes the goal like `admit`.

This file lives in the `Tests` library, which is **not** part of `defaultTargets`, so
these tests do not run on a normal `lake build`. Run them with `lake build Tests`. -/

open Plausible
open Aeneas Aeneas.Std
open curve25519_dalek

/-! ## Instance smoke tests

The `Arbitrary`/`Shrinkable`/`SampleableExt` instances exist for every key type. -/

-- Arbitrary instances exist for all key types.
#check (inferInstance : Arbitrary scalar.Scalar)
#check (inferInstance : Arbitrary backend.serial.u64.field.FieldElement51)
#check (inferInstance : Arbitrary edwards.EdwardsPoint)
#check (inferInstance : Arbitrary ristretto.RistrettoPoint)

-- Arbitrary instances exist for all primitive scalar types (unsigned and signed).
#check (inferInstance : Arbitrary Std.U8)
#check (inferInstance : Arbitrary Std.U16)
#check (inferInstance : Arbitrary Std.U32)
#check (inferInstance : Arbitrary Std.U64)
#check (inferInstance : Arbitrary Std.Usize)
#check (inferInstance : Arbitrary Std.I8)
#check (inferInstance : Arbitrary Std.I16)
#check (inferInstance : Arbitrary Std.I32)
#check (inferInstance : Arbitrary Std.I64)
#check (inferInstance : Arbitrary Std.Isize)

-- Shrinkable instances exist for every primitive scalar type.
#check (inferInstance : Shrinkable Std.U8)
#check (inferInstance : Shrinkable Std.U16)
#check (inferInstance : Shrinkable Std.U32)
#check (inferInstance : Shrinkable Std.U64)
#check (inferInstance : Shrinkable Std.Usize)
#check (inferInstance : Shrinkable Std.I8)
#check (inferInstance : Shrinkable Std.I16)
#check (inferInstance : Shrinkable Std.I32)
#check (inferInstance : Shrinkable Std.I64)
#check (inferInstance : Shrinkable Std.Isize)

#check (inferInstance : SampleableExt edwards.affine.AffinePoint)
#check (inferInstance : SampleableExt montgomery.ProjectivePoint)
#check (inferInstance : SampleableExt backend.serial.curve_models.ProjectivePoint)
#check (inferInstance : SampleableExt backend.serial.curve_models.ProjectiveNielsPoint)
#check (inferInstance : SampleableExt backend.serial.curve_models.AffineNielsPoint)
#check (inferInstance : SampleableExt backend.serial.curve_models.CompletedPoint)
#check (inferInstance : SampleableExt backend.serial.u64.scalar.Scalar52)
#check (inferInstance : SampleableExt edwards.CompressedEdwardsY)
#check (inferInstance : SampleableExt montgomery.MontgomeryPoint)
#check (inferInstance : SampleableExt ristretto.CompressedRistretto)
#check (inferInstance : SampleableExt scalar.Scalar)
#check (inferInstance : SampleableExt edwards.EdwardsPoint)
#check (inferInstance : SampleableExt (Array U64 5#usize))
#check (inferInstance : SampleableExt { a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 })

/-! ## Signed-integer instances

Sanity checks that the `Arbitrary`/`Shrinkable` instances for the signed scalar types
(`I8`/`I16`/`I32`/`I64`/`Isize`) generate in-range values and that arrays of them work. -/

example : ∀ (x : I8), x.val ≥ -128 ∧ x.val ≤ 127 := by
  plausible (config := { numInst := 100 })

example : ∀ (x : I16), x.val ≥ -32768 ∧ x.val ≤ 32767 := by
  plausible (config := { numInst := 100 })

example : ∀ (x : I64), x.val ≥ -9223372036854775808 := by
  plausible (config := { numInst := 100 })

-- Arrays of signed integers generate at the requested length.
example : ∀ (arr : Array I8 5#usize), arr.val.length = 5 := by
  plausible (config := { numInst := 100 })

example : ∀ (x : I32), x.val ≥ -2147483648 ∧ x.val ≤ 2147483647 := by
  plausible (config := { numInst := 100 })

example : ∀ (x : Isize), x.val ≥ -9223372036854775808 := by
  plausible (config := { numInst := 100 })


/-! ## `curve25519_dalek::backend::serial::u64::field::FieldElement51::FieldElement51::add`

`FieldElement51::add` performs element-wise addition of field-element limbs.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

The spec has preconditions `ha : ∀ i < 5, a[i]!.val < 2^53` (and similarly for `b`).
Quantifying over the plain array type and filtering via the hypothesis would almost never
produce valid test cases (probability ≈ 1/2^110), causing Plausible to "give up".

The fix is to quantify directly over the bounded subtype
`{ a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 }`.
`varTestable` then uses our `Arbitrary` instance from `Plausible.lean` to generate
bounded arrays by construction, and `.val` extracts the underlying array for `add`. -/

open Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts
open CoreOpsArithAddAssignSharedAFieldElement51

namespace curve25519_dalek.Shared0FieldElement51.Insts
namespace CoreOpsArithAddSharedAFieldElement51FieldElement51

/-! ### Catching a wrong spec

This is a deliberately **incorrect** spec: it claims every output limb is `< 2^50`, but
since each input limb can be up to `2^53 - 1`, a sum reaches `≈ 2^54`, so the bound is far
too tight. `plausible` finds a counter-example, which `Testable.check` reports by throwing
an error — normally that fails the build.

To keep the build green while still demonstrating the bug is caught, we run `plausible`
with `quiet := true` (so the thrown message is the deterministic string
`"Found a counter-example!"`, with no random values) and capture that expected error with
`#guard_msgs`. The command therefore succeeds **iff** Plausible discovered the spec error;
if the spec were accidentally correct, no error would be thrown and `#guard_msgs` would
fail instead. -/

/-- error: Found a counter-example! -/
#guard_msgs in
example :
    ∀ (a : { a : Array U64 5#usize // ∀ i < 5, a[i]!.val < 2^53 })
      (b : { b : Array U64 5#usize // ∀ i < 5, b[i]!.val < 2^53 }),
    add a.val b.val ⦃ (result : Array U64 5#usize) =>
      ∀ i < 5, result[i]!.val < 2^50 ⦄ := by
  plausible (config := { numInst := 1000, quiet := true })

end CoreOpsArithAddSharedAFieldElement51FieldElement51
end curve25519_dalek.Shared0FieldElement51.Insts
