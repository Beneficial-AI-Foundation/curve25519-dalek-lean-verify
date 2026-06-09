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
