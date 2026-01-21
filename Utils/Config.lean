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
  -- Clone implementations
  "curve25519_dalek.backend.serial.curve_models.CloneAffineNielsPoint.clone",
  "curve25519_dalek.backend.serial.curve_models.CloneCompletedPoint.clone",
  "curve25519_dalek.backend.serial.curve_models.CloneProjectiveNielsPoint.clone",
  "curve25519_dalek.backend.serial.u64.field.CloneFieldElement51.clone",
  "curve25519_dalek.backend.serial.u64.scalar.CloneScalar52.clone",
  "curve25519_dalek.montgomery.CloneMontgomeryPoint.clone",
  "curve25519_dalek.montgomery.CloneProjectivePoint.clone",
  "curve25519_dalek.scalar.CloneScalar.clone",
  -- Default implementations
  "curve25519_dalek.backend.serial.curve_models.DefaultAffineNielsPoint.default",
  "curve25519_dalek.backend.serial.curve_models.DefaultProjectiveNielsPoint.default",
  "curve25519_dalek.montgomery.DefaultMontgomeryPoint.default",
  "curve25519_dalek.montgomery.DefaultProjectivePoint.default",
  "curve25519_dalek.scalar.DefaultScalar.default",
  -- Identity trait implementations
  "curve25519_dalek.IdentityCurveModelsProjectivePoint",
  "curve25519_dalek.IdentityMontgomeryProjectivePoint",
  "curve25519_dalek.traits.IdentityAffineNielsPoint",
  "curve25519_dalek.traits.IdentityEdwardsPoint",
  "curve25519_dalek.traits.IdentityMontgomeryPoint",
  "curve25519_dalek.traits.IdentityProjectiveNielsPoint",
  -- Macros
  "curve25519_dalek.edwards.AddEdwardsPointEdwardsPointEdwardsPoint.add",
  "curve25519_dalek.edwards.MulScalarEdwardsPointEdwardsPoint.mul",
  "curve25519_dalek.edwards.MulSharedAScalarEdwardsPointEdwardsPoint.mul",
  "curve25519_dalek.montgomery.MulAssignMontgomeryPointScalar.mul_assign",
  "curve25519_dalek.montgomery.MulMontgomeryPointScalarMontgomeryPoint.mul",
  "curve25519_dalek.montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint.mul",
  "curve25519_dalek.montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul",
  "curve25519_dalek.montgomery.MulScalarSharedBMontgomeryPointMontgomeryPoint.mul",
  "curve25519_dalek.montgomery.MulSharedAMontgomeryPointScalarMontgomeryPoint.mul",
  "curve25519_dalek.montgomery.MulSharedAScalarMontgomeryPointMontgomeryPoint.mul",
  "curve25519_dalek.ristretto.AddRistrettoPointRistrettoPointRistrettoPoint.add",
  "curve25519_dalek.ristretto.AddRistrettoPointRistrettoPointRistrettoPoint.add",
  "curve25519_dalek.scalar.AddAssignScalarScalar.add_assign",
  "curve25519_dalek.scalar.AddScalarScalarScalar.add",
  "curve25519_dalek.scalar.AddScalarSharedBScalarScalar.add",
  "curve25519_dalek.scalar.AddSharedAScalarScalarScalar.add",
  "curve25519_dalek.scalar.MulAssignScalarScalar.mul_assign",
  "curve25519_dalek.scalar.MulScalarScalarScalar.mul",
  "curve25519_dalek.scalar.MulScalarSharedBScalarScalar.mul",
  "curve25519_dalek.scalar.MulSharedAScalarScalarScalar.mul",
  "curve25519_dalek.scalar.SubAssignScalarScalar.sub_assign",
  "curve25519_dalek.scalar.SubScalarScalarScalar.sub",
  "curve25519_dalek.scalar.SubScalarSharedBScalarScalar.sub",
  "curve25519_dalek.scalar.SubSharedAScalarScalarScalar.sub",
  "curve25519_dalek.montgomery.ZeroizeMontgomeryPoint.zeroize",
  "curve25519_dalek.edwards.MulSharedAEdwardsPointScalarEdwardsPoint.mul",
  "curve25519_dalek.ristretto.MulSharedAScalarRistrettoPointRistrettoPoint.mul",
  -- Zeroize
  "curve25519_dalek.backend.serial.curve_models.ZeroizeAffineNielsPoint.zeroize",
  "curve25519_dalek.backend.serial.curve_models.ZeroizeProjectiveNielsPoint.zeroize",
  "curve25519_dalek.backend.serial.u64.field.ZeroizeFieldElement51.zeroize",
  "curve25519_dalek.scalar.ZeroizeScalar.zeroize",
  "curve25519_dalek.zeroize.ZeroizeAffineNielsPoint",
  "curve25519_dalek.zeroize.ZeroizeFieldElement51",
  "curve25519_dalek.zeroize.ZeroizeMontgomeryPoint",
  "curve25519_dalek.zeroize.ZeroizeProjectiveNielsPoint",
  "curve25519_dalek.zeroize.ZeroizeScalar",
  "curve25519_dalek.backend.serial.u64.scalar.ZeroizeScalar52.zeroize",
  "curve25519_dalek.zeroize.ZeroizeScalar52",
  -- Index
  "curve25519_dalek.backend.serial.u64.scalar.IndexMutScalar52UsizeU64.index_mut",
  "curve25519_dalek.backend.serial.u64.scalar.IndexScalar52UsizeU64.index",
  -- Other
  "curve25519_dalek.backend.get_selected_backend",
  "curve25519_dalek.window.FromLookupTableProjectiveNielsPointSharedAEdwardsPoint.from",
  "curve25519_dalek.window.LookupTable.select",
  "curve25519_dalek.backend.serial.curve_models.ValidityCheckProjectivePoint.is_valid",
  "curve25519_dalek.traits.IsIdentity.Blanket",
  "curve25519_dalek.traits.ValidityCheckProjectivePoint",
  "curve25519_dalek.backend.serial.curve_models.ValidityCheckProjectivePoint.is_valid"
]

end Utils.Config
