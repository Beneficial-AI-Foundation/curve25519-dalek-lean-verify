# Verification Status Report

This document tracks the progress of formally verifying functions from the curve25519-dalek library.

## Functions

| Function | Source | Spec Theorem | Extracted | Verified | Notes |
|----------|--------|--------------|-----------|----------|-------|
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L364-L372) | - | ☐ | ☐ |  |
| `as_projective` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L352-L359) | - | ☐ | ☐ |  |
| `as_extended` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L337-L345) | - | ☐ | ☐ |  |
| `double` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L380-L397) | - | ☐ | ☐ |  |
| `identity` | [backend/serial/curve_models/mod.rs](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L229-L237) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [backend/serial/scalar_mul/straus.rs](curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L1-L47) | - | ☐ | ☐ |  |
| `mul` | [backend/serial/scalar_mul/vartime_double_base.rs](curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L1-L15) | - | ☐ | ☐ |  |
| `as_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L367-L369) | - | ✅ | ☐ |  |
| `conditional_assign` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L247-L254) | - | ☐ | ☐ |  |
| `from_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L337-L363) | - | ✅ | ☐ | Brackets required in extracted Lean |
| `pow2k` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L460-L565) | - | ✅ | ☐ |  |
| `reduce` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L290-L323) | [Reduce.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L561-L561) | - | ✅ | ☐ |  |
| `square2` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L566-L570) | - | ✅ | ☐ | Loop refactored |
| `to_bytes` | [backend/serial/u64/field.rs](curve25519-dalek/src/backend/serial/u64/field.rs#L374-L456) | - | ✅ | ☐ |  |
| `L` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L127-L133) | - | ✅ | ☐ | Brackets required in extracted Lean |
| `LFACTOR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L136-L136) | - | ✅ | ☐ |  |
| `R` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L139-L145) | - | ✅ | ☐ |  |
| `RR` | [backend/serial/u64/constants.rs](curve25519-dalek/src/backend/serial/u64/constants.rs#L148-L154) | - | ✅ | ☐ |  |
| `m` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L56-L58) | [M.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/M.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `ZERO` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L62-L62) | - | ✅ | ☐ |  |
| `add` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L159-L174) | - | ✅ | ☐ |  |
| `conditional_add_l` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L195-L208) | - | ✅ | ☐ |  |
| `as_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L317-L323) | - | ✅ | ☐ |  |
| `from_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L64-L85) | - | ✅ | ☐ | Nested loop refactored |
| `from_bytes_wide` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L87-L116) | - | ✅ | ☐ | Nested loop refactored; required shr edit |
| `from_montgomery` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L324-L432) | - | ✅ | ☐ | Loop refactored |
| `montgomery_mul` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L304-L306) | - | ✅ | ☐ |  |
| `montgomery_reduce` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L253-L258) | - | ✅ | ☐ |  |
| `montgomery_square` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L310-L312) | - | ✅ | ☐ |  |
| `mul_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L203-L217) | [MulInternal.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/MulInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square_internal` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L222-L241) | [SquareInternal.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `sub` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L175-L198) | - | ✅ | 📋 | Loop refactored |
| `to_bytes` | [backend/serial/u64/scalar.rs](curve25519-dalek/src/backend/serial/u64/scalar.rs#L129-L166) | - | ✅ | ☐ |  |
| `straus_multiscalar_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L157-L191) | - | ☐ | ☐ |  |
| `vartime_double_base_mul` | [backend/mod.rs](curve25519-dalek/src/backend/mod.rs#L240-L245) | - | ☐ | ☐ |  |
| `as_bytes` | [edwards.rs](curve25519-dalek/src/edwards.rs#L180-L185) | - | ☐ | ☐ |  |
| `decompress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L193-L196) | - | ☐ | ☐ |  |
| `as_projective` | [edwards.rs](curve25519-dalek/src/edwards.rs#L521-L623) | - | ☐ | ☐ |  |
| `as_projective_niels` | [edwards.rs](curve25519-dalek/src/edwards.rs#L508-L525) | - | ☐ | ☐ |  |
| `compress` | [edwards.rs](curve25519-dalek/src/edwards.rs#L565-L581) | - | ☐ | ☐ |  |
| `double` | [edwards.rs](curve25519-dalek/src/edwards.rs#L613-L626) | - | ☐ | ☐ |  |
| `identity` | [edwards.rs](curve25519-dalek/src/edwards.rs#L409-L416) | - | ☐ | ☐ |  |
| `is_small_order` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1226-L1258) | - | ☐ | ☐ |  |
| `mul_by_cofactor` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1186-L1188) | - | ☐ | ☐ |  |
| `mul_by_pow_2` | [edwards.rs](curve25519-dalek/src/edwards.rs#L1191-L1199) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [edwards.rs](curve25519-dalek/src/edwards.rs#L799-L804) | - | ☐ | ☐ |  |
| `to_montgomery` | [edwards.rs](curve25519-dalek/src/edwards.rs#L552-L559) | - | ☐ | ☐ |  |
| `vartime_double_scalar_mul_basepoint` | [edwards.rs](curve25519-dalek/src/edwards.rs#L901-L912) | - | ☐ | ☐ |  |
| `to_edwards` | [montgomery.rs](curve25519-dalek/src/montgomery.rs#L216-L252) | - | ☐ | ☐ |  |
| `as_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L233-L236) | - | ☐ | ☐ |  |
| `decompress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L254-L269) | - | ☐ | ☐ |  |
| `from_slice` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L243-L246) | - | ☐ | ☐ |  |
| `to_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L228-L231) | - | ☐ | ☐ |  |
| `compress` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L488-L522) | - | ☐ | ☐ |  |
| `default` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L812-L816) | - | ☐ | ☐ |  |
| `double_and_compress_batch` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L552-L636) | - | ☐ | ☐ |  |
| `elligator_ristretto_flavor` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L655-L692) | - | ☐ | ☐ |  |
| `from_uniform_bytes` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L786-L803) | - | ☐ | ☐ |  |
| `identity` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L806-L810) | - | ☐ | ☐ |  |
| `mul_base` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L951-L962) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [ristretto.rs](curve25519-dalek/src/ristretto.rs#L980-L990) | - | ☐ | ☐ |  |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1205-L1208) | [Invert.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/Invert.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `montgomery_invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1149-L1203) | [MontgomeryInvert.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/MontgomeryInvert.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `pack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1140-L1145) | [Pack.lean](Curve25519Dalek/Proofs/Scalar/Backend/Serial/U64/Scalar/Scalar52/Pack.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `clamp_integer` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1386-L1391) | [ClampInteger.lean](Curve25519Dalek/Proofs/Scalar/ClampInteger.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `read_le_u64_into` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1349-L1364) | [ReadLeU64Into.lean](Curve25519Dalek/Proofs/Scalar/ReadLeU64Into.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `as_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L705-L708) | [AsBytes.lean](Curve25519Dalek/Proofs/Scalar/Scalar/AsBytes.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `ct_eq` | [scalar.rs](curve25519-dalek/src/scalar.rs#L300-L304) | [CtEq.lean](Curve25519Dalek/Proofs/Scalar/Scalar/CtEq.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `from_bytes_mod_order` | [scalar.rs](curve25519-dalek/src/scalar.rs#L236-L246) | [FromBytesModOrder.lean](Curve25519Dalek/Proofs/Scalar/Scalar/FromBytesModOrder.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `from_bytes_mod_order_wide` | [scalar.rs](curve25519-dalek/src/scalar.rs#L249-L252) | [FromBytesModOrderWide.lean](Curve25519Dalek/Proofs/Scalar/Scalar/FromBytesModOrderWide.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `from_canonical_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L260-L265) | [FromCanonicalBytes.lean](Curve25519Dalek/Proofs/Scalar/Scalar/FromCanonicalBytes.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `from_hash` | [scalar.rs](curve25519-dalek/src/scalar.rs#L670-L678) | [FromHash.lean](Curve25519Dalek/Proofs/Scalar/Scalar/FromHash.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `hash_from_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L624-L632) | [HashFromBytes.lean](Curve25519Dalek/Proofs/Scalar/Scalar/HashFromBytes.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `invert` | [scalar.rs](curve25519-dalek/src/scalar.rs#L746-L749) | [Invert.lean](Curve25519Dalek/Proofs/Scalar/Scalar/Invert.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `is_canonical` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1133-L1136) | [IsCanonical.lean](Curve25519Dalek/Proofs/Scalar/Scalar/IsCanonical.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `non_adjacent_form` | [scalar.rs](curve25519-dalek/src/scalar.rs#L920-L973) | [NonAdjacentForm.lean](Curve25519Dalek/Proofs/Scalar/Scalar/NonAdjacentForm.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `ONE` | [scalar.rs](curve25519-dalek/src/scalar.rs#L567-L572) | - | ✅ | ☐ |  |
| `reduce` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1124-L1130) | [Reduce.lean](Curve25519Dalek/Proofs/Scalar/Scalar/Reduce.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `to_bytes` | [scalar.rs](curve25519-dalek/src/scalar.rs#L690-L693) | [ToBytes.lean](Curve25519Dalek/Proofs/Scalar/Scalar/ToBytes.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `unpack` | [scalar.rs](curve25519-dalek/src/scalar.rs#L1118-L1121) | [Unpack.lean](Curve25519Dalek/Proofs/Scalar/Scalar/Unpack.lean) | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `ZERO` | [scalar.rs](curve25519-dalek/src/scalar.rs#L564-L564) | - | ✅ | ☐ |  |

## Summary

- **Total Functions**: 82
- **Extracted**: 42 / 82 (51%)
- **Draft Spec**: 17 / 82 (20%)
- **Specified**: 1 / 82 (1%)
- **Verified**: 5 / 82 (6%)
- **Pending**: 59 / 82 (71%)

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
