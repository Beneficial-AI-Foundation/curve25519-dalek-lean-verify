/-
  Config: Project-specific configuration for Utils tools.

  This file centralizes all project-specific values. To adapt these tools
  for a different Aeneas-generated project, modify the values here.
-/
import Lean

open Lean

namespace Utils.Config

/-- The main module to import (contains Funs and Specs) -/
def mainModule : Name := `Curve25519Dalek

/-- The module containing function definitions -/
def funsModule : Name := `Curve25519Dalek.Funs

/-- The crate name used for relevance filtering (matches source paths) -/
def crateName : String := "curve25519-dalek"

/-!
### Extraction Artifact Suffixes

Functions whose name ends with any of these suffixes are Aeneas extraction
artifacts (internal implementation helpers). They will be marked with
`isExtractionArtifact = true` but still included in output.

For `_body` functions, the docstring is inherited by the corresponding
main function (e.g., `foo_body`'s docstring is used for `foo`).
-/
def extractionArtifactSuffixes : List String := [
  "_body",             -- Global/constant body definitions
  "_loop",             -- Loop helper functions
  "_loop0", "_loop1", "_loop2", "_loop3"  -- Numbered loop variants
]

/-!
### Namespace Prefix Filters

Functions whose name starts with any of these prefixes will be EXCLUDED.
-/
def excludedNamespacePrefixes : List String := [
  "curve25519_dalek.core",   -- Rust core library implementations
  "curve25519_dalek.subtle", -- Subtle crate implementations
  -- "_private"                 -- Private/internal definitions
]

/-!
### Hidden Functions

Specific function names that should be marked as hidden (`isHidden = true`).
These are included in output but can be filtered out by consumers.
Use this for functions that are technically relevant but not useful for
verification tracking (e.g., trivial trait implementations).
-/
def hiddenFunctions : List String := [
  -- Other
  "curve25519_dalek.IdentityCurveModelsProjectivePoint",
  "curve25519_dalek.IdentityMontgomeryProjectivePoint",
  "curve25519_dalek.backend.get_selected_backend",
  "curve25519_dalek.window.LookupTable.select",
  -- Clone
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCloneClone",
  "curve25519_dalek.backend.serial.curve_models.CompletedPoint.Insts.CoreCloneClone",
  "curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreCloneClone",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCloneClone",
  "curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreCloneClone",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreCloneClone",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCloneClone",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCloneClone",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCloneClone",
  "curve25519_dalek.montgomery.ProjectivePoint.Insts.CoreCloneClone",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreCloneClone",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCloneClone",
  "curve25519_dalek.scalar.Scalar.Insts.CoreCloneClone",
  -- Copy
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.backend.serial.curve_models.CompletedPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreMarkerCopy",
  "curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreMarkerCopy",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreMarkerCopy",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.montgomery.ProjectivePoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreMarkerCopy",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreMarkerCopy",
  "curve25519_dalek.scalar.Scalar.Insts.CoreMarkerCopy",
  -- StructuralPartialEq
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreMarkerStructuralPartialEq",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreMarkerStructuralPartialEq",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreMarkerStructuralPartialEq",
  -- Eq
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpEq",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpEq",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreCmpEq",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpEq",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpEq",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpEq",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreCmpEq",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpEq",
  "curve25519_dalek.scalar.Scalar.Insts.CoreCmpEq",
  -- PartialEq
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpPartialEqEdwardsPoint",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar",
  -- Zeroize / DefaultIsZeroes
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.ZeroizeZeroize",
  "curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.ZeroizeZeroize",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.ZeroizeZeroize",
  "curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.ZeroizeDefaultIsZeroes",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.ZeroizeZeroize",
  "curve25519_dalek.scalar.Scalar.Insts.ZeroizeZeroize",
  -- ValidityCheck
  "curve25519_dalek.backend.serial.curve_models.ProjectivePoint.Insts.Curve25519_dalekTraitsValidityCheck",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.Curve25519_dalekTraitsValidityCheck",
  -- Default
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreDefaultDefault",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.montgomery.ProjectivePoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreDefaultDefault",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreDefaultDefault",
  "curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault",
  -- Assign ops
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithAddAssignSharedAFieldElement51",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithMulAssignSharedAFieldElement51",
  "curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreOpsArithSubAssignSharedAFieldElement51",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddAssignEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddAssignSharedAEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulAssignScalar",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulAssignSharedAScalar",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithSubAssignEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithSubAssignSharedAEdwardsPoint",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignShared0Scalar",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithAddAssignRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithAddAssignShared0RistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulAssignScalar",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulAssignSharedAScalar",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithSubAssignRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithSubAssignShared0RistrettoPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddAssignSharedAScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubAssignSharedAScalar",
  -- Arithmetic ops (borrow wrappers — all except owned ProjectiveNielsPoint.Neg)
  "curve25519_dalek.Shared0AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAEdwardsPointEdwardsPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAProjectiveNielsPointCompletedPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAEdwardsPointEdwardsPoint",
  "curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAProjectiveNielsPointCompletedPoint",
  "curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51",
  "curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithMulSharedAFieldElement51FieldElement51",
  "curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithNegFieldElement51",
  "curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51",
  "curve25519_dalek.Shared0ProjectiveNielsPoint.Insts.CoreOpsArithNegProjectiveNielsPoint",
  "curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithAddSharedARistrettoPointRistrettoPoint",
  "curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint",
  "curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint",
  "curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithSubSharedARistrettoPointRistrettoPoint",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar",
  "curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar",
  "curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint",
  "curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint",
  "curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint",
  "curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint",
  "curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithSubEdwardsPointEdwardsPoint",
  "curve25519_dalek.SharedAMontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint",
  "curve25519_dalek.SharedARistrettoPoint.Insts.CoreOpsArithAddRistrettoPointRistrettoPoint",
  "curve25519_dalek.SharedARistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint",
  "curve25519_dalek.SharedARistrettoPoint.Insts.CoreOpsArithSubRistrettoPointRistrettoPoint",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar",
  "curve25519_dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar",
  "curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddEdwardsPointEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithAddSharedBEdwardsPointEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithSubEdwardsPointEdwardsPoint",
  "curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithSubSharedBEdwardsPointEdwardsPoint",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulScalarMontgomeryPoint",
  "curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithAddRistrettoPointRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithAddSharedBRistrettoPointRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulSharedBScalarRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithSubRistrettoPointRistrettoPoint",
  "curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithSubSharedBRistrettoPointRistrettoPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAffinePointEdwardsPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulShared0AffinePointEdwardsPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBEdwardsPointEdwardsPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBMontgomeryPointMontgomeryPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBRistrettoPointRistrettoPoint",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar",
  "curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar"
]

end Utils.Config
