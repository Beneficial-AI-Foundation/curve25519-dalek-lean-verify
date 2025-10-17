# Verification Status Report

This document tracks the progress of formally verifying functions from the curve25519-dalek library.

## Functions

| Function | Source | Spec Theorem | Extracted | Verified | Notes |
|----------|--------|--------------|-----------|----------|-------|
| `as_extended` | [backend/serial/curve_models/mod.rs:L364-L372](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L364-L372) | - | ☐ | ☐ |  |
| `as_projective` | [backend/serial/curve_models/mod.rs:L352-L359](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L352-L359) | - | ☐ | ☐ |  |
| `as_extended` | [backend/serial/curve_models/mod.rs:L337-L345](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L337-L345) | - | ☐ | ☐ |  |
| `double` | [backend/serial/curve_models/mod.rs:L380-L397](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L380-L397) | - | ☐ | ☐ |  |
| `identity` | [backend/serial/curve_models/mod.rs:L229-L237](curve25519-dalek/src/backend/serial/curve_models/mod.rs#L229-L237) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [backend/serial/scalar_mul/straus.rs:L1-L47](curve25519-dalek/src/backend/serial/scalar_mul/straus.rs#L1-L47) | - | ☐ | ☐ |  |
| `mul` | [backend/serial/scalar_mul/vartime_double_base.rs:L1-L15](curve25519-dalek/src/backend/serial/scalar_mul/vartime_double_base.rs#L1-L15) | - | ☐ | ☐ |  |
| `as_bytes` | [backend/serial/u64/field.rs:L367-L369](curve25519-dalek/src/backend/serial/u64/field.rs#L367-L369) | - | ☐ | ☐ |  |
| `conditional_assign` | [backend/serial/u64/field.rs:L247-L254](curve25519-dalek/src/backend/serial/u64/field.rs#L247-L254) | - | ☐ | ☐ |  |
| `from_bytes` | [backend/serial/u64/field.rs:L337-L363](curve25519-dalek/src/backend/serial/u64/field.rs#L337-L363) | - | ✅ | ☐ | Brackets required in extracted Lean |
| `pow2k` | [backend/serial/u64/field.rs:L460-L565](curve25519-dalek/src/backend/serial/u64/field.rs#L460-L565) | - | ☐ | ☐ |  |
| `reduce` | [backend/serial/u64/field.rs:L290-L323](curve25519-dalek/src/backend/serial/u64/field.rs#L290-L323) | [Backend/Serial/U64/Field/FieldElement51/Reduce.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square` | [backend/serial/u64/field.rs:L561-L561](curve25519-dalek/src/backend/serial/u64/field.rs#L561-L561) | - | ☐ | ☐ |  |
| `square2` | [backend/serial/u64/field.rs:L566-L570](curve25519-dalek/src/backend/serial/u64/field.rs#L566-L570) | - | ☐ | ☐ |  |
| `to_bytes` | [backend/serial/u64/field.rs:L374-L456](curve25519-dalek/src/backend/serial/u64/field.rs#L374-L456) | - | ✅ | ☐ |  |
| `L` | [backend/serial/u64/constants.rs:L127-L133](curve25519-dalek/src/backend/serial/u64/constants.rs#L127-L133) | - | ✅ | ☐ | Brackets required in extracted Lean |
| `LFACTOR` | [backend/serial/u64/constants.rs:L136-L136](curve25519-dalek/src/backend/serial/u64/constants.rs#L136-L136) | - | ✅ | ☐ |  |
| `RR` | [backend/serial/u64/constants.rs:L148-L154](curve25519-dalek/src/backend/serial/u64/constants.rs#L148-L154) | - | ✅ | ☐ |  |
| `m` | [backend/serial/u64/scalar.rs:L56-L58](curve25519-dalek/src/backend/serial/u64/scalar.rs#L56-L58) | [Backend/Serial/U64/Scalar/M.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/M.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `ZERO` | [backend/serial/u64/scalar.rs:L62-L62](curve25519-dalek/src/backend/serial/u64/scalar.rs#L62-L62) | - | ✅ | ☐ |  |
| `add` | [backend/serial/u64/scalar.rs:L159-L174](curve25519-dalek/src/backend/serial/u64/scalar.rs#L159-L174) | - | ☐ | ☐ |  |
| `conditional_add_l` | [backend/serial/u64/scalar.rs:L195-L208](curve25519-dalek/src/backend/serial/u64/scalar.rs#L195-L208) | - | ✅ | ☐ |  |
| `as_bytes` | [backend/serial/u64/scalar.rs:L119-L158](curve25519-dalek/src/backend/serial/u64/scalar.rs#L119-L158) | - | ☐ | ☐ |  |
| `as_montgomery` | [backend/serial/u64/scalar.rs:L317-L323](curve25519-dalek/src/backend/serial/u64/scalar.rs#L317-L323) | - | ✅ | ☐ |  |
| `from_bytes` | [backend/serial/u64/scalar.rs:L64-L85](curve25519-dalek/src/backend/serial/u64/scalar.rs#L64-L85) | - | ✅ | ☐ | Nested loop refactored |
| `from_bytes_wide` | [backend/serial/u64/scalar.rs:L87-L116](curve25519-dalek/src/backend/serial/u64/scalar.rs#L87-L116) | - | ☐ | ☐ |  |
| `from_montgomery` | [backend/serial/u64/scalar.rs:L324-L432](curve25519-dalek/src/backend/serial/u64/scalar.rs#L324-L432) | - | ☐ | ☐ |  |
| `montgomery_mul` | [backend/serial/u64/scalar.rs:L304-L306](curve25519-dalek/src/backend/serial/u64/scalar.rs#L304-L306) | - | ✅ | ☐ |  |
| `montgomery_reduce` | [backend/serial/u64/scalar.rs:L253-L258](curve25519-dalek/src/backend/serial/u64/scalar.rs#L253-L258) | - | ✅ | ☐ |  |
| `montgomery_square` | [backend/serial/u64/scalar.rs:L310-L312](curve25519-dalek/src/backend/serial/u64/scalar.rs#L310-L312) | - | ✅ | ☐ |  |
| `mul_internal` | [backend/serial/u64/scalar.rs:L203-L217](curve25519-dalek/src/backend/serial/u64/scalar.rs#L203-L217) | [Backend/Serial/U64/Scalar/Scalar52/MulInternal.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/MulInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `square_internal` | [backend/serial/u64/scalar.rs:L222-L241](curve25519-dalek/src/backend/serial/u64/scalar.rs#L222-L241) | [Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean](Curve25519Dalek/Proofs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `sub` | [backend/serial/u64/scalar.rs:L175-L198](curve25519-dalek/src/backend/serial/u64/scalar.rs#L175-L198) | - | ✅ | ☐ | Minor refactor of loop required |
| `to_bytes` | [backend/serial/u64/scalar.rs:L129-L166](curve25519-dalek/src/backend/serial/u64/scalar.rs#L129-L166) | - | ✅ | ☐ |  |
| `straus_multiscalar_mul` | [backend/mod.rs:L157-L191](curve25519-dalek/src/backend/mod.rs#L157-L191) | - | ☐ | ☐ |  |
| `vartime_double_base_mul` | [backend/mod.rs:L240-L245](curve25519-dalek/src/backend/mod.rs#L240-L245) | - | ☐ | ☐ |  |
| `as_bytes` | [edwards.rs:L180-L185](curve25519-dalek/src/edwards.rs#L180-L185) | - | ☐ | ☐ |  |
| `decompress` | [edwards.rs:L193-L196](curve25519-dalek/src/edwards.rs#L193-L196) | - | ☐ | ☐ |  |
| `as_projective` | [edwards.rs:L521-L623](curve25519-dalek/src/edwards.rs#L521-L623) | - | ☐ | ☐ |  |
| `as_projective_niels` | [edwards.rs:L508-L525](curve25519-dalek/src/edwards.rs#L508-L525) | - | ☐ | ☐ |  |
| `compress` | [edwards.rs:L565-L581](curve25519-dalek/src/edwards.rs#L565-L581) | - | ☐ | ☐ |  |
| `double` | [edwards.rs:L613-L626](curve25519-dalek/src/edwards.rs#L613-L626) | - | ☐ | ☐ |  |
| `identity` | [edwards.rs:L409-L416](curve25519-dalek/src/edwards.rs#L409-L416) | - | ☐ | ☐ |  |
| `is_small_order` | [edwards.rs:L1226-L1258](curve25519-dalek/src/edwards.rs#L1226-L1258) | - | ☐ | ☐ |  |
| `mul_by_cofactor` | [edwards.rs:L1186-L1188](curve25519-dalek/src/edwards.rs#L1186-L1188) | - | ☐ | ☐ |  |
| `mul_by_pow_2` | [edwards.rs:L1191-L1199](curve25519-dalek/src/edwards.rs#L1191-L1199) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [edwards.rs:L799-L804](curve25519-dalek/src/edwards.rs#L799-L804) | - | ☐ | ☐ |  |
| `to_montgomery` | [edwards.rs:L552-L559](curve25519-dalek/src/edwards.rs#L552-L559) | - | ☐ | ☐ |  |
| `vartime_double_scalar_mul_basepoint` | [edwards.rs:L901-L912](curve25519-dalek/src/edwards.rs#L901-L912) | - | ☐ | ☐ |  |
| `to_edwards` | [montgomery.rs:L216-L252](curve25519-dalek/src/montgomery.rs#L216-L252) | - | ☐ | ☐ |  |
| `as_bytes` | [ristretto.rs:L233-L236](curve25519-dalek/src/ristretto.rs#L233-L236) | - | ☐ | ☐ |  |
| `decompress` | [ristretto.rs:L254-L269](curve25519-dalek/src/ristretto.rs#L254-L269) | - | ☐ | ☐ |  |
| `from_slice` | [ristretto.rs:L243-L246](curve25519-dalek/src/ristretto.rs#L243-L246) | - | ☐ | ☐ |  |
| `to_bytes` | [ristretto.rs:L228-L231](curve25519-dalek/src/ristretto.rs#L228-L231) | - | ☐ | ☐ |  |
| `compress` | [ristretto.rs:L488-L522](curve25519-dalek/src/ristretto.rs#L488-L522) | - | ☐ | ☐ |  |
| `default` | [ristretto.rs:L812-L816](curve25519-dalek/src/ristretto.rs#L812-L816) | - | ☐ | ☐ |  |
| `double_and_compress_batch` | [ristretto.rs:L552-L636](curve25519-dalek/src/ristretto.rs#L552-L636) | - | ☐ | ☐ |  |
| `elligator_ristretto_flavor` | [ristretto.rs:L655-L692](curve25519-dalek/src/ristretto.rs#L655-L692) | - | ☐ | ☐ |  |
| `from_uniform_bytes` | [ristretto.rs:L786-L803](curve25519-dalek/src/ristretto.rs#L786-L803) | - | ☐ | ☐ |  |
| `identity` | [ristretto.rs:L806-L810](curve25519-dalek/src/ristretto.rs#L806-L810) | - | ☐ | ☐ |  |
| `mul_base` | [ristretto.rs:L951-L962](curve25519-dalek/src/ristretto.rs#L951-L962) | - | ☐ | ☐ |  |
| `multiscalar_mul` | [ristretto.rs:L980-L990](curve25519-dalek/src/ristretto.rs#L980-L990) | - | ☐ | ☐ |  |
| `invert` | [scalar.rs:L1205-L1208](curve25519-dalek/src/scalar.rs#L1205-L1208) | - | ☐ | ☐ |  |
| `montgomery_invert` | [scalar.rs:L1149-L1203](curve25519-dalek/src/scalar.rs#L1149-L1203) | - | ☐ | ☐ |  |
| `pack` | [scalar.rs:L1140-L1145](curve25519-dalek/src/scalar.rs#L1140-L1145) | - | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `clamp_integer` | [scalar.rs:L1386-L1391](curve25519-dalek/src/scalar.rs#L1386-L1391) | [Scalar/ClampInteger.lean](Curve25519Dalek/Proofs/Scalar/ClampInteger.lean) | ✅ | ✅ | Verified (oliver-butterley) |
| `read_le_u64_into` | [scalar.rs:L1349-L1364](curve25519-dalek/src/scalar.rs#L1349-L1364) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `as_bytes` | [scalar.rs:L705-L708](curve25519-dalek/src/scalar.rs#L705-L708) | - | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `ct_eq` | [scalar.rs:L300-L304](curve25519-dalek/src/scalar.rs#L300-L304) | [Scalar/Scalar/CtEq.lean](Curve25519Dalek/Proofs/Scalar/Scalar/CtEq.lean) | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `from_bytes_mod_order` | [scalar.rs:L236-L246](curve25519-dalek/src/scalar.rs#L236-L246) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `from_bytes_mod_order_wide` | [scalar.rs:L249-L252](curve25519-dalek/src/scalar.rs#L249-L252) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `from_canonical_bytes` | [scalar.rs:L260-L265](curve25519-dalek/src/scalar.rs#L260-L265) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `from_hash` | [scalar.rs:L670-L678](curve25519-dalek/src/scalar.rs#L670-L678) | - | ☐ | ☐ |  |
| `hash_from_bytes` | [scalar.rs:L624-L632](curve25519-dalek/src/scalar.rs#L624-L632) | - | ☐ | ☐ |  |
| `invert` | [scalar.rs:L746-L749](curve25519-dalek/src/scalar.rs#L746-L749) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `is_canonical` | [scalar.rs:L1133-L1136](curve25519-dalek/src/scalar.rs#L1133-L1136) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `non_adjacent_form` | [scalar.rs:L920-L973](curve25519-dalek/src/scalar.rs#L920-L973) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `ONE` | [scalar.rs:L567-L572](curve25519-dalek/src/scalar.rs#L567-L572) | - | ✅ | ☐ |  |
| `reduce` | [scalar.rs:L1124-L1130](curve25519-dalek/src/scalar.rs#L1124-L1130) | - | ☐ | ✏️ | NL-specs written (markus-dablander) |
| `to_bytes` | [scalar.rs:L690-L693](curve25519-dalek/src/scalar.rs#L690-L693) | - | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `unpack` | [scalar.rs:L1118-L1121](curve25519-dalek/src/scalar.rs#L1118-L1121) | - | ✅ | ✏️ | NL-specs written (markus-dablander) |
| `ZERO` | [scalar.rs:L564-L564](curve25519-dalek/src/scalar.rs#L564-L564) | - | ✅ | ☐ |  |

## Summary

- **Total Functions**: 82
- **Extracted**: 25 / 82 (30%)
- **Draft Spec**: 13 / 82 (15%)
- **Specified**: 0 / 82 (0%)
- **Verified**: 5 / 82 (6%)
- **Pending**: 64 / 82 (78%)

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
