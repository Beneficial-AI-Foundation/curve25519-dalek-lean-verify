# Verification Status Report

This document tracks the progress of formally verifying functions from the curve25519-dalek library.

## Functions

| Function | Source | Spec Theorem | Extracted | Verified | Notes |
|----------|--------|--------------|-----------|----------|-------|
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L368-L375) | [AsExtended.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/CompletedPoint/AsExtended.lean) | ✅ | ☐ |  |
| `as_projective` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L356-L362) | [AsProjective.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/CompletedPoint/AsProjective.lean) | ✅ | ☐ |  |
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L341-L348) | [AsExtended.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/ProjectivePoint/AsExtended.lean) | ☐ | ☐ |  |
| `double` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L384-L419) | [Double.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/ProjectivePoint/Double.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `identity` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L233-L239) | [Identity.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/ProjectivePoint/Identity.lean) | ☐ | ☐ |  |
| `multiscalar_mul` | [backend/serial/scalar_mul/straus.rs](curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L103-L144) | [MultiscalarMul.lean](Curve25519Dalek/Specs/Backend/Serial/ScalarMul/Straus/Straus/MultiscalarMul.lean) | ☐ | ☐ |  |
| `mul` | [backend/serial/scalar_mul/vartime_double_base.rs](curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L1-L15) | [Mul.lean](Curve25519Dalek/Specs/Backend/Serial/ScalarMul/VartimeDoubleBase/Mul.lean) | ☐ | ☐ |  |
| `EDWARDS_D` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L45-L51) | [EdwardsD.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/EdwardsD.lean) | ✅ | ☐ |  |
| `L` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L127-L133) | [L.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/L.lean) | ✅ | ✅ | Brackets required in extracted Lean; Verified (markus-dablander) |
| `LFACTOR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L136-L136) | [LFACTOR.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/LFACTOR.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `R` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L139-L145) | [R.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/R.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `RR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L148-L154) | [RR.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/RR.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `SQRT_M1` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L99-L105) | [SqrtM1.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/SqrtM1.lean) | ✅ | ☐ |  |
| `add` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L269-L273) | [Add.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `add_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L276-L282) | [AddAssign.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/AddAssign.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `as_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L389-L391) | [AsBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/AsBytes.lean) | ✅ | ✅ | Verified (oliver-butterley) Specified (markus-dablander) |
| `conditional_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L228-L234) | [ConditionalAssign.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ConditionalAssign.lean) | ☐ | ☐ |  |
| `from_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L360-L385) | [FromBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/FromBytes.lean) | ✅ | 📋 | Brackets required in extracted Lean |
| `from_limbs` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L238-L240) | [FromLimbs.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/FromLimbs.lean) | ✅ | ☐ |  |
| `negate` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L256-L262) | [Negate.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Negate.lean) | ✅ | ☐ |  |
| `ONE` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L245-L245) | [One.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/One.lean) | ✅ | ☐ |  |
| `pow22501` | [field.rs](curve25519-dalek/src/field.rs#L170-L204) | - | ✅ | ☐ |  |
| `pow2k` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L482-L587) | [Pow2K.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Pow2K.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `reduce` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L312-L345) | [Reduce.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L590-L592) | [Square.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square.lean) | ✅ | ✅ | Verified (oliver-butterley); Specified (markus-dablander) |
| `square2` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L595-L604) | [Square2.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square2.lean) | ✅ | ✅ | Loop refactored; Specified (markus-dablander); Verified (oliver-butterley) |
| `sub` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L285-L302) | [Sub.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Sub.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `sub_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L305-L308) | [SubAssign.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/SubAssign.lean) | ✅ | ✅ | Specified (markus-dablander); Verified (oliver-butterley) |
| `to_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L396-L478) | [ToBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ToBytes.lean) | ✅ | 📋 |  |
| `m` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L56-L58) | [M.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/M.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `add` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L177-L192) | [Add.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `as_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L338-L340) | [AsMontgomery.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/AsMontgomery.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `conditional_add_l` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L213-L226) | [ConditionalAddL.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ConditionalAddL.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `from_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L66-L93) | [FromBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytes.lean) | ✅ | 📋 | Nested loop refactored; Specified (markus-dablander) |
| `from_bytes_wide` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L97-L132) | [FromBytesWide.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytesWide.lean) | ✅ | 📋 | Nested loop refactored; required shr edit; Specified (markus-dablander) |
| `from_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L345-L353) | [FromMontgomery.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromMontgomery.lean) | ✅ | 📋 | Loop refactored; Specified (markus-dablander) |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1208-L1210) | [Invert.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Invert.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `montgomery_invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1150-L1205) | [MontgomeryInvert.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryInvert.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `montgomery_mul` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L326-L328) | [MontgomeryMul.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `montgomery_reduce` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L274-L307) | [MontgomeryReduce.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `montgomery_square` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L332-L334) | [MontgomerySquare.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomerySquare.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `mul_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L231-L245) | [MulInternal.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MulInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L250-L269) | [SquareInternal.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `sub` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L195-L211) | [Sub.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Sub.lean) | ✅ | 📋 | Loop refactored |
| `to_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L137-L174) | [ToBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ToBytes.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `ZERO` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L62-L62) | [Zero.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Zero.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `straus_multiscalar_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L196-L220) | [StrausMultiscalarMul.lean](Curve25519Dalek/Specs/Backend/StrausMultiscalarMul.lean) | ☐ | ☐ |  |
| `vartime_double_base_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L267-L277) | [VartimeDoubleBaseMul.lean](Curve25519Dalek/Specs/Backend/VartimeDoubleBaseMul.lean) | ☐ | ☐ |  |
| `as_bytes` | [edwards.rs](curve25519-dalek/src/edwards.rs#L189-L191) | [AsBytes.lean](Curve25519Dalek/Specs/Edwards/CompressedEdwardsY/AsBytes.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `decompress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L202-L296) | [Decompress.lean](Curve25519Dalek/Specs/Edwards/CompressedEdwardsY/Decompress.lean) | ✅ | ☐ |  |
| `as_projective` | [edwards.rs](curve25519-dalek/src/edwards.rs#L521-L623) | [AsProjective.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/AsProjective.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `as_projective_niels` | [edwards.rs](curve25519-dalek/src/edwards.rs#L508-L525) | [AsProjectiveNiels.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/AsProjectiveNiels.lean) | ☐ | ☐ |  |
| `compress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L565-L581) | [Compress.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Compress.lean) | ✅ | ☐ |  |
| `double` | [edwards.rs](curve25519-dalek/src/edwards.rs#L613-L626) | [Double.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Double.lean) | ☐ | ☐ |  |
| `identity` | [edwards.rs](curve25519-dalek/src/edwards.rs#L420-L427) | [Identity.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Identity.lean) | ☐ | ☐ |  |
| `is_small_order` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1226-L1258) | [IsSmallOrder.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/IsSmallOrder.lean) | ☐ | ☐ |  |
| `mul_by_cofactor` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1186-L1188) | [MulByCofactor.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulByCofactor.lean) | ✅ | ☐ |  |
| `mul_by_pow_2` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1191-L1199) | [MulByPow2.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulByPow2.lean) | ✅ | ☐ |  |
| `multiscalar_mul` | [edwards.rs](curve25519-dalek/src/edwards.rs#L799-L804) | [MultiscalarMul.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/MultiscalarMul.lean) | ☐ | ☐ |  |
| `to_montgomery` | [edwards.rs](curve25519-dalek/src/edwards.rs#L552-L559) | [ToMontgomery.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/ToMontgomery.lean) | ✅ | ☐ |  |
| `vartime_double_scalar_mul_basepoint` | [edwards.rs](curve25519-dalek/src/edwards.rs#L901-L912) | [VartimeDoubleScalarMulBasepoint.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/VartimeDoubleScalarMulBasepoint.lean) | ☐ | ☐ |  |
| `pow_p58` | [field.rs](curve25519-dalek/src/field.rs#L269-L290) | [PowP58.lean](Curve25519Dalek/Specs/Field/FieldElement/PowP58.lean) | ✅ | ☐ |  |
| `sqrt_ratio_i` | [field.rs](curve25519-dalek/src/field.rs#L292-L331) | [SqrtRatioI.lean](Curve25519Dalek/Specs/Field/FieldElement/SqrtRatioI.lean) | ✅ | ☐ |  |
| `to_edwards` | [montgomery.rs](curve25519-dalek/src/montgomery.rs#L216-L252) | [ToEdwards.lean](Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/ToEdwards.lean) | ☐ | ☐ |  |
| `as_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L234-L236) | [AsBytes.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/AsBytes.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `decompress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L255-L382) | [Decompress.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/Decompress.lean) | ☐ | ☐ |  |
| `from_slice` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L244-L246) | [FromSlice.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/FromSlice.lean) | ☐ | ☐ |  |
| `to_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L229-L231) | [ToBytes.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/ToBytes.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `compress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L488-L522) | [Compress.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/Compress.lean) | ☐ | ☐ |  |
| `default` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L813-L816) | [Default.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/Default.lean) | ☐ | ☐ |  |
| `double_and_compress_batch` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L552-L636) | [DoubleAndCompressBatch.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/DoubleAndCompressBatch.lean) | ☐ | ☐ |  |
| `elligator_ristretto_flavor` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L656-L692) | [ElligatorRistrettoFlavor.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/ElligatorRistrettoFlavor.lean) | ☐ | ☐ |  |
| `from_uniform_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L787-L804) | [FromUniformBytes.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/FromUniformBytes.lean) | ☐ | ☐ |  |
| `identity` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L807-L810) | [Identity.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/Identity.lean) | ☐ | ☐ |  |
| `mul_base` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L951-L962) | [MulBase.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/MulBase.lean) | ☐ | ☐ |  |
| `multiscalar_mul` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L980-L990) | [MultiscalarMul.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/MultiscalarMul.lean) | ☐ | ☐ |  |
| `pack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1141-L1145) | [Pack.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Pack.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `clamp_integer` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1388-L1393) | [ClampInteger.lean](Curve25519Dalek/Specs/Scalar/ClampInteger.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `read_le_u64_into` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1352-L1366) | [ReadLeU64Into.lean](Curve25519Dalek/Specs/Scalar/ReadLeU64Into.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `as_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L706-L708) | [AsBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/AsBytes.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `ct_eq` | [scalar.rs](curve25519-dalek/src/scalar.rs#L301-L303) | [CtEq.lean](Curve25519Dalek/Specs/Scalar/Scalar/CtEq.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `from_bytes_mod_order` | [scalar.rs](curve25519-dalek/src/scalar.rs#L237-L247) | [FromBytesModOrder.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromBytesModOrder.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `from_bytes_mod_order_wide` | [scalar.rs](curve25519-dalek/src/scalar.rs#L250-L253) | [FromBytesModOrderWide.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromBytesModOrderWide.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `from_canonical_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L261-L266) | [FromCanonicalBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromCanonicalBytes.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `from_hash` | [scalar.rs](curve25519-dalek/src/scalar.rs#L670-L678) | [FromHash.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromHash.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `hash_from_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L624-L632) | [HashFromBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/HashFromBytes.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L747-L749) | [Invert.lean](Curve25519Dalek/Specs/Scalar/Scalar/Invert.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `is_canonical` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1134-L1136) | [IsCanonical.lean](Curve25519Dalek/Specs/Scalar/Scalar/IsCanonical.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `non_adjacent_form` | [scalar.rs](curve25519-dalek/src/scalar.rs#L921-L973) | [NonAdjacentForm.lean](Curve25519Dalek/Specs/Scalar/Scalar/NonAdjacentForm.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `ONE` | [scalar.rs](curve25519-dalek/src/scalar.rs#L567-L572) | [One.lean](Curve25519Dalek/Specs/Scalar/Scalar/One.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `reduce` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1125-L1130) | [Reduce.lean](Curve25519Dalek/Specs/Scalar/Scalar/Reduce.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `to_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L691-L693) | [ToBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/ToBytes.lean) | ✅ | ✅ | Verified (markus-dablander) |
| `unpack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1119-L1121) | [Unpack.lean](Curve25519Dalek/Specs/Scalar/Scalar/Unpack.lean) | ✅ | 📋 | Specified (markus-dablander) |
| `ZERO` | [scalar.rs](curve25519-dalek/src/scalar.rs#L564-L564) | [Zero.lean](Curve25519Dalek/Specs/Scalar/Scalar/Zero.lean) | ✅ | ✅ | Verified (oliver-butterley) |

## Legend

### Extracted
- ✅ Extracted - Function has been successfully extracted to Lean
- ☐ Not extracted - Function has not been extracted yet

### Verified
- ✅ Verified - Function has been formally verified with complete proofs
- 📋 Specified - Function has formal specifications but no proofs yet
- ✏️ Draft spec - Function has draft natural language specifications
- ☐ Not verified - No verification work has been done yet

---

*This report is automatically generated from `status.csv`. Run `./scripts/generate-status.py` to update.*
