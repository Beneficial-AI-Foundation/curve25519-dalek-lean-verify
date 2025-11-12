# Verification Status Report

This document tracks the progress of formally verifying functions from the curve25519-dalek library.

## Functions

| Function | Source | Spec Theorem | Extracted | Verified | Notes |
|----------|--------|--------------|-----------|----------|-------|
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L368-L375) | [AsExtended.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/CompletedPoint/AsExtended.lean) | ✅ | ☐ |  |
| `as_projective` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L356-L362) | [AsProjective.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/CompletedPoint/AsProjective.lean) | ✅ | ☐ |  |
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L341-L348) | [AsExtended.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/ProjectivePoint/AsExtended.lean) | ✅ | ☐ |  |
| `double` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L384-L419) | [Double.lean](Curve25519Dalek/Specs/Backend/Serial/CurveModels/ProjectivePoint/Double.lean) | ✅ | 📋 |  |
| `mul` | [backend/serial/scalar_mul/vartime_double_base.rs](curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L1-L15) | [Mul.lean](Curve25519Dalek/Specs/Backend/Serial/ScalarMul/VartimeDoubleBase/Mul.lean) | ☐ | ☐ | Extracts to broken Lean code |
| `EDWARDS_D` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L45-L51) | [EDWARDS_D.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/EDWARDS_D.lean) | ✅ | ✅ |  |
| `EDWARDS_D2` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L54-L60) | [EDWARDS_D2.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/EDWARDS_D2.lean) | ✅ | ✅ |  |
| `INVSQRT_A_MINUS_D` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L90-L96) | [INVSQRT_A_MINUS_D.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/INVSQRT_A_MINUS_D.lean) | ✅ | ✅ |  |
| `ONE_MINUS_EDWARDS_D_SQUARED` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L63-L69) | [ONE_MINUS_EDWARDS_D_SQUARED.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/ONE_MINUS_EDWARDS_D_SQUARED.lean) | ✅ | ✅ |  |
| `EDWARDS_D_MINUS_ONE_SQUARED` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L72-L78) | [EDWARDS_D_MINUS_ONE_SQUARED.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/EDWARDS_D_MINUS_ONE_SQUARED.lean) | ✅ | ✅ |  |
| `L` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L127-L133) | [L.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/L.lean) | ✅ | ✅ | Brackets required in extracted Lean |
| `LFACTOR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L136-L136) | [LFACTOR.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/LFACTOR.lean) | ✅ | ✅ |  |
| `R` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L139-L145) | [R.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/R.lean) | ✅ | ✅ |  |
| `RR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L148-L154) | [RR.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/RR.lean) | ✅ | ✅ |  |
| `SQRT_M1` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L99-L105) | [SQRT_M1.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Constants/SQRT_M1.lean) | ✅ | ✅ |  |
| `add` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L269-L273) | [Add.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean) | ✅ | ✅ |  |
| `add_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L276-L282) | [AddAssign.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/AddAssign.lean) | ✅ | ✅ |  |
| `as_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L389-L391) | [AsBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/AsBytes.lean) | ✅ | ✅ |  |
| `from_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L360-L385) | [FromBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/FromBytes.lean) | ✅ | 📋 | Brackets required in extracted Lean |
| `from_limbs` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L238-L240) | [FromLimbs.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/FromLimbs.lean) | ✅ | ✅ |  |
| `negate` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L256-L262) | [Negate.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Negate.lean) | ✅ | 📋 |  |
| `ONE` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L245-L245) | [ONE.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ONE.lean) | ✅ | ✅ |  |
| `ZERO` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L263-L263) | [ZERO.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ZERO.lean) | ✅ | ✅ |  |
| `MINUS_ONE` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L267-L273) | [MINUS_ONE.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/MINUS_ONE.lean) | ✅ | ✅ |  |
| `pow22501` | [field.rs](curve25519-dalek/src/field.rs#L170-L204) | [Pow22501.lean](Curve25519Dalek/Specs/Field/FieldElement51/Pow22501.lean) | ✅ | 📋 |  |
| `pow2k` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L482-L587) | [Pow2K.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Pow2K.lean) | ✅ | 📋 |  |
| `reduce` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L312-L345) | [Reduce.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) | ✅ | ✅ |  |
| `square` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L590-L592) | [Square.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square.lean) | ✅ | ✅ |  |
| `square2` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L595-L604) | [Square2.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Square2.lean) | ✅ | ✅ | Loop refactored |
| `sub` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L285-L302) | [Sub.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Sub.lean) | ✅ | ✅ | Refactor after problem with progress |
| `sub_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L305-L308) | [SubAssign.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/SubAssign.lean) | ✅ | ✅ | No longer present among extracted functions |
| `to_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L396-L478) | [ToBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/ToBytes.lean) | ✅ | 📋 |  |
| `m` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L56-L58) | [M.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/M.lean) | ✅ | ✅ |  |
| `add` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L177-L192) | [Add.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Add.lean) | ✅ | 📋 |  |
| `as_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L338-L340) | [AsMontgomery.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/AsMontgomery.lean) | ✅ | ✅ | 🤖🏆🌈🎉⭐ |
| `conditional_add_l` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L213-L226) | [ConditionalAddL.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ConditionalAddL.lean) | ✅ | 📋 |  |
| `from_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L66-L93) | [FromBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytes.lean) | ✅ | 📋 | Nested loop refactored |
| `from_bytes_wide` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L97-L132) | [FromBytesWide.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromBytesWide.lean) | ✅ | 📋 | Nested loop refactored; required shr edit |
| `from_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L345-L353) | [FromMontgomery.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/FromMontgomery.lean) | ✅ | 📋 | Loop refactored |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1208-L1210) | [Invert.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Invert.lean) | ✅ | 📋 |  |
| `montgomery_invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1150-L1205) | [MontgomeryInvert.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryInvert.lean) | ✅ | 📋 |  |
| `montgomery_mul` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L326-L328) | [MontgomeryMul.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryMul.lean) | ✅ | 📋 |  |
| `montgomery_reduce` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L274-L307) | [MontgomeryReduce.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryReduce.lean) | ✅ | 📋 |  |
| `montgomery_square` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L332-L334) | [MontgomerySquare.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MontgomerySquare.lean) | ✅ | 📋 |  |
| `mul_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L231-L245) | [MulInternal.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/MulInternal.lean) | ✅ | ✅ |  |
| `square_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L250-L269) | [SquareInternal.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean) | ✅ | ✅ |  |
| `sub` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L195-L211) | [Sub.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Sub.lean) | ✅ | 📋 | Loop refactored |
| `to_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L137-L174) | [ToBytes.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/ToBytes.lean) | ✅ | 📋 |  |
| `ZERO` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L62-L62) | [Zero.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Zero.lean) | ✅ | ✅ |  |
| `straus_multiscalar_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L196-L220) | [StrausMultiscalarMul.lean](Curve25519Dalek/Specs/Backend/StrausMultiscalarMul.lean) | ☐ | ☐ | Problem with extraction |
| `vartime_double_base_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L267-L277) | [VartimeDoubleBaseMul.lean](Curve25519Dalek/Specs/Backend/VartimeDoubleBaseMul.lean) | ☐ | ☐ | Problem with extraction due to nested borrows, uses serial::scalar_mul::vartime_double_base::mul |
| `as_bytes` | [edwards.rs](curve25519-dalek/src/edwards.rs#L189-L191) | [AsBytes.lean](Curve25519Dalek/Specs/Edwards/CompressedEdwardsY/AsBytes.lean) | ✅ | ✅ |  |
| `decompress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L202-L296) | [Decompress.lean](Curve25519Dalek/Specs/Edwards/CompressedEdwardsY/Decompress.lean) | ✅ | ☐ |  |
| `as_projective` | [edwards.rs](curve25519-dalek/src/edwards.rs#L521-L623) | [AsProjective.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/AsProjective.lean) | ✅ | ✅ |  |
| `as_projective_niels` | [edwards.rs](curve25519-dalek/src/edwards.rs#L508-L525) | [AsProjectiveNiels.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/AsProjectiveNiels.lean) | ✅ | ☐ |  |
| `compress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L565-L581) | [Compress.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Compress.lean) | ✅ | 📋 |  |
| `ct_eq` | [edwards.rs](curve25519-dalek/src/edwards.rs#L493-L502) | [CtEq.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/CtEq.lean) | ✅ | 📋 |  |
| `double` | [edwards.rs](curve25519-dalek/src/edwards.rs#L613-L626) | [Double.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Double.lean) | ✅ | 📋 |  |
| `identity` | [edwards.rs](curve25519-dalek/src/edwards.rs#L420-L427) | [Identity.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/Identity.lean) | ✅ | ✅ |  |
| `is_small_order` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1226-L1258) | [IsSmallOrder.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/IsSmallOrder.lean) | ✅ | 📋 |  |
| `mul_by_cofactor` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1186-L1188) | [MulByCofactor.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulByCofactor.lean) | ✅ | ☐ |  |
| `mul_by_pow_2` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1191-L1199) | [MulByPow2.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/MulByPow2.lean) | ✅ | 📋 |  |
| `to_montgomery` | [edwards.rs](curve25519-dalek/src/edwards.rs#L552-L559) | [ToMontgomery.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/ToMontgomery.lean) | ✅ | ☐ |  |
| `vartime_double_scalar_mul_basepoint` | [edwards.rs](curve25519-dalek/src/edwards.rs#L901-L912) | [VartimeDoubleScalarMulBasepoint.lean](Curve25519Dalek/Specs/Edwards/EdwardsPoint/VartimeDoubleScalarMulBasepoint.lean) | ☐ | ☐ | Problem with extraction due to nested borrows, uses serial::scalar_mul::vartime_double_base::mul |
| `pow_p58` | [field.rs](curve25519-dalek/src/field.rs#L269-L290) | [PowP58.lean](Curve25519Dalek/Specs/Field/FieldElement51/PowP58.lean) | ✅ | 📋 |  |
| `sqrt_ratio_i` | [field.rs](curve25519-dalek/src/field.rs#L292-L331) | [SqrtRatioi.lean](Curve25519Dalek/Specs/Field/FieldElement51/SqrtRatioi.lean) | ✅ | 📋 |  |
| `is_zero` | [field.rs](curve25519-dalek/src/field.rs#L160-L165) | [IsZero.lean](Curve25519Dalek/Specs/Field/FieldElement51/IsZero.lean) | ✅ | ✅ | To be refactored when problem with progress is solved |
| `invsqrt` | [field.rs](curve25519-dalek/src/field.rs#L352-L354) | [InvSqrt.lean](Curve25519Dalek/Specs/Field/FieldElement51/InvSqrt.lean) | ✅ | 📋 |  |
| `to_edwards` | [montgomery.rs](curve25519-dalek/src/montgomery.rs#L216-L252) | [ToEdwards.lean](Curve25519Dalek/Specs/Montgomery/MontgomeryPoint/ToEdwards.lean) | ✅ | ☐ |  |
| `as_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L234-L236) | [AsBytes.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/AsBytes.lean) | ✅ | ✅ |  |
| `decompress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L255-L382) | [Decompress.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/Decompress.lean) | ✅ | ☐ |  |
| `to_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L229-L231) | [ToBytes.lean](Curve25519Dalek/Specs/Ristretto/CompressedRistretto/ToBytes.lean) | ✅ | ✅ |  |
| `compress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L488-L522) | [Compress.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/Compress.lean) | ✅ | ☐ |  |
| `elligator_ristretto_flavor` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L656-L692) | [ElligatorRistrettoFlavor.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/ElligatorRistrettoFlavor.lean) | ✅ | ☐ |  |
| `from_uniform_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L787-L804) | [FromUniformBytes.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/FromUniformBytes.lean) | ✅ | ☐ |  |
| `mul_base` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L951-L962) | [MulBase.lean](Curve25519Dalek/Specs/Ristretto/RistrettoPoint/MulBase.lean) | ☐ | ☐ | Aeneas error on extraction |
| `pack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1141-L1145) | [Pack.lean](Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/Pack.lean) | ✅ | ✅ |  |
| `clamp_integer` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1388-L1393) | [ClampInteger.lean](Curve25519Dalek/Specs/Scalar/ClampInteger.lean) | ✅ | ✅ |  |
| `read_le_u64_into` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1352-L1366) | [ReadLeU64Into.lean](Curve25519Dalek/Specs/Scalar/ReadLeU64Into.lean) | ☐ | ✏️ | Extraction problem due to nested borrows |
| `as_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L706-L708) | [AsBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/AsBytes.lean) | ✅ | ✅ |  |
| `ct_eq` | [scalar.rs](curve25519-dalek/src/scalar.rs#L301-L303) | [CtEq.lean](Curve25519Dalek/Specs/Scalar/Scalar/CtEq.lean) | ✅ | ✅ |  |
| `from_bytes_mod_order` | [scalar.rs](curve25519-dalek/src/scalar.rs#L237-L247) | [FromBytesModOrder.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromBytesModOrder.lean) | ✅ | ✅ |  |
| `from_bytes_mod_order_wide` | [scalar.rs](curve25519-dalek/src/scalar.rs#L250-L253) | [FromBytesModOrderWide.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromBytesModOrderWide.lean) | ✅ | ✅ |  |
| `from_canonical_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L261-L266) | [FromCanonicalBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/FromCanonicalBytes.lean) | ✅ | 📋 |  |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L747-L749) | [Invert.lean](Curve25519Dalek/Specs/Scalar/Scalar/Invert.lean) | ✅ | 📋 |  |
| `is_canonical` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1134-L1136) | [IsCanonical.lean](Curve25519Dalek/Specs/Scalar/Scalar/IsCanonical.lean) | ✅ | ✅ |  |
| `non_adjacent_form` | [scalar.rs](curve25519-dalek/src/scalar.rs#L921-L973) | [NonAdjacentForm.lean](Curve25519Dalek/Specs/Scalar/Scalar/NonAdjacentForm.lean) | ☐ | ✏️ | Extraction problem due to nested borrows |
| `ONE` | [scalar.rs](curve25519-dalek/src/scalar.rs#L567-L572) | [One.lean](Curve25519Dalek/Specs/Scalar/Scalar/One.lean) | ✅ | ✅ |  |
| `reduce` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1125-L1130) | [Reduce.lean](Curve25519Dalek/Specs/Scalar/Scalar/Reduce.lean) | ✅ | 📋 |  |
| `to_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L691-L693) | [ToBytes.lean](Curve25519Dalek/Specs/Scalar/Scalar/ToBytes.lean) | ✅ | ✅ |  |
| `unpack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1119-L1121) | [Unpack.lean](Curve25519Dalek/Specs/Scalar/Scalar/Unpack.lean) | ✅ | 📋 |  |
| `ZERO` | [scalar.rs](curve25519-dalek/src/scalar.rs#L564-L564) | [Zero.lean](Curve25519Dalek/Specs/Scalar/Scalar/Zero.lean) | ✅ | ✅ |  |

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
