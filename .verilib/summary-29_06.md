# Verification report: unknown unknown

## 1. Verified public API functions (0)

None

## 2. Trusted public API functions (0)

None

## 3. Trust base

### 3a. Properties assumed to hold (22 axioms)

Axioms — propositions assumed without proof.

- `probe:curve25519_dalek.Array.Insts.ZeroizeZeroize.zeroize`
- `probe:curve25519_dalek.Slice.Insts.SubtleConstantTimeEq.ct_eq`
- `probe:curve25519_dalek.Slice.Insts.SubtleConstantTimeEq.ct_eq_spec`
- `probe:curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreCmpPartialEqAffineNielsPoint.ne`
- `probe:curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpEq.assert_receiver_is_total_eq`
- `probe:curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.CoreCmpPartialEqFieldElement51.ne`
- `probe:curve25519_dalek.core.fmt.Arguments`
- `probe:curve25519_dalek.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next`
- `probe:curve25519_dalek.core.iter.traits.iterator.Iterator.rev.default`
- `probe:curve25519_dalek.core.ops.range.Range.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator.next_back`
- `probe:curve25519_dalek.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.rev`
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked`
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut`
- `probe:curve25519_dalek.edwards.CompressedEdwardsY.Insts.CoreCmpPartialEqCompressedEdwardsY.ne`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreCmpPartialEqEdwardsPoint.ne`
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpEq.assert_receiver_is_total_eq`
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreCmpPartialEqAffinePoint.ne`
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpPartialEqMontgomeryPoint.ne`
- `probe:curve25519_dalek.ristretto.CompressedRistretto.Insts.CoreCmpPartialEqCompressedRistretto.ne`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreCmpPartialEqRistrettoPoint.ne`

### 3b. External functions assumed correct w.r.t. their specs (56)

- `probe:curve25519_dalek.Array.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.Array.Insts.SubtleConditionallySelectable.conditional_select` (external)
- `probe:curve25519_dalek.Array.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.Bool.Insts.CoreConvertFromChoice.from` (external)
- `probe:curve25519_dalek.Choice.one` (external)
- `probe:curve25519_dalek.Choice.zero` (external)
- `probe:curve25519_dalek.U16.Insts.SubtleConstantTimeEq.ct_eq` (external)
- `probe:curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_select` (external)
- `probe:curve25519_dalek.U64.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.U8.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.U8.Insts.SubtleConditionallySelectable.conditional_select` (external)
- `probe:curve25519_dalek.U8.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.U8.Insts.SubtleConstantTimeEq.ct_eq` (external)
- `probe:curve25519_dalek.alloc.vec.Vec.Insts.ZeroizeZeroize.zeroize` (external)
- `probe:curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap'` (external)
- `probe:curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get` (external)
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get_mut` (external)
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index` (external)
- `probe:curve25519_dalek.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.index_mut` (external)
- `probe:curve25519_dalek.core.result.Result.map` (external)
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_assign'` (external)
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_swap'` (external)
- `probe:curve25519_dalek.instDecidableEqChoice` (external)
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreCmpEq.assert_receiver_is_total_eq` (external)
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.montgomery.ProjectivePoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreCmpEq.assert_receiver_is_total_eq` (external)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreCmpPartialEqScalar.ne` (external)
- `probe:curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.conditional_assign` (external)
- `probe:curve25519_dalek.scalar.Scalar.Insts.SubtleConditionallySelectable.conditional_swap` (external)
- `probe:curve25519_dalek.subtle.Choice` (external)
- `probe:curve25519_dalek.subtle.Choice.Insts.CoreConvertFromU8.from` (external)
- `probe:curve25519_dalek.subtle.Choice.Insts.CoreOpsBitBitAndChoiceChoice.bitand` (external)
- `probe:curve25519_dalek.subtle.Choice.Insts.CoreOpsBitBitOrChoiceChoice.bitor` (external)
- `probe:curve25519_dalek.subtle.Choice.Insts.CoreOpsBitNotChoice.not` (external)
- `probe:curve25519_dalek.subtle.Choice.unwrap_u8` (external)
- `probe:curve25519_dalek.subtle.Choice.val` (external)
- `probe:curve25519_dalek.subtle.ConditionallyNegatable.Blanket.conditional_negate` (external)
- `probe:curve25519_dalek.subtle.ConditionallySelectable.conditional_assign.default` (external)
- `probe:curve25519_dalek.subtle.ConditionallySelectable.conditional_swap.default` (external)
- `probe:curve25519_dalek.subtle.CtOption` (external)
- `probe:curve25519_dalek.subtle.CtOption.is_some` (external)
- `probe:curve25519_dalek.subtle.CtOption.new` (external)
- `probe:curve25519_dalek.subtle.CtOption.value` (external)
- `probe:curve25519_dalek.zeroize.Zeroize.Blanket.zeroize` (external)

## 4. Unverified and failed functions (24)

### 4a. Unverified functions (21)

- `probe:curve25519-dalek/4.2.0/backend/get_selected_backend()`
- `probe:curve25519-dalek/4.2.0/backend/serial/curve_models/AffineNielsPoint#impl<AffineNielsPoint>#[AffineNielsPoint][Neg]neg()`
- `probe:curve25519-dalek/4.2.0/backend/serial/u64/field/impl<&FieldElement51>#[FieldElement51][ConditionallySelectable]conditional_swap()`
- `probe:curve25519-dalek/4.2.0/backend/serial/u64/scalar/&Scalar52#impl#[Scalar52][Zeroize]zeroize()`
- `probe:curve25519-dalek/4.2.0/backend/serial/u64/scalar/&Scalar52#impl<usize>#[Scalar52][`Index<usize>`]index()`
- `probe:curve25519-dalek/4.2.0/backend/serial/u64/scalar/&Scalar52#impl<usize>#[Scalar52][`IndexMut<usize>`]index_mut()`
- `probe:curve25519-dalek/4.2.0/backend/variable_base_mul()`
- `probe:curve25519-dalek/4.2.0/edwards/&CompressedEdwardsY#impl<[u8;/{const}]>#[CompressedEdwardsY]to_bytes()`
- `probe:curve25519-dalek/4.2.0/edwards/EdwardsPoint#impl<EdwardsPoint>#[EdwardsPoint][Neg]neg()`
- `probe:curve25519-dalek/4.2.0/edwards/affine/Scalar#impl<&AffinePoint>#[Scalar][`Mul<&AffinePoint>`]mul()`
- `probe:curve25519-dalek/4.2.0/edwards/affine/Scalar#impl<AffinePoint>#[Scalar][`Mul<AffinePoint>`]mul()`
- `probe:curve25519-dalek/4.2.0/edwards/affine/impl<AffinePoint>#[AffinePoint][Default]default()`
- `probe:curve25519-dalek/4.2.0/montgomery/&MontgomeryPoint#impl<&Scalar>#[MontgomeryPoint][`MulAssign<&Scalar>`]mul_assign()`
- `probe:curve25519-dalek/4.2.0/ristretto/&RistrettoPoint#impl<RistrettoPoint>#[`&RistrettoPoint`][Neg]neg()`
- `probe:curve25519-dalek/4.2.0/ristretto/&RistrettoPoint#impl<[EdwardsPoint;/{const}]>#[RistrettoPoint]coset4()`
- `probe:curve25519-dalek/4.2.0/ristretto/RistrettoPoint#impl<RistrettoPoint>#[RistrettoPoint][Neg]neg()`
- `probe:curve25519-dalek/4.2.0/scalar/&Scalar#impl#[Scalar][Zeroize]zeroize()`
- `probe:curve25519-dalek/4.2.0/scalar/&Scalar#impl<[i8;/{const}]>#[Scalar]non_adjacent_form()`
- `probe:curve25519-dalek/4.2.0/scalar/&Scalar#impl<usize>#[Scalar][`Index<usize>`]index()`
- `probe:curve25519-dalek/4.2.0/scalar/impl<Scalar>#[Scalar][Default]default()`
- `probe:curve25519-dalek/4.2.0/traits/&T#impl<bool>#[T][IsIdentity]is_identity()`

### 4b. Unverified lemmas (2)

- `probe:Edwards.add_assoc_Ed25519`
- `probe:curve25519_dalek.ristretto.IsEven_iff_in_doubling_image_right`

### 4c. Unverified definitions (1)

- `probe:curve25519_dalek.math.elligator_ristretto_flavor_pure`

### 4d. Failed functions (0)

None

## 5. Verified remaining Lean functions (134)

- `probe:Edwards.instAddCommGroupPointCurveFieldEd25519`
- `probe:curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint`
- `probe:curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul` (spec: `probe:curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul_spec`)
- `probe:curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint`
- `probe:curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul` (spec: `probe:curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul_spec`)
- `probe:curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar.add` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar.add_spec`)
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul_spec`)
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul_spec`)
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul_spec`)
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar.neg` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar.neg_spec`)
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub` (spec: `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub_spec`)
- `probe:curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint`
- `probe:curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul` (spec: `probe:curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul_spec`)
- `probe:curve25519_dalek.SharedARistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint`
- `probe:curve25519_dalek.SharedARistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint.mul`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithAddScalarScalar.add`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint.mul`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar.mul` (spec: `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar.mul_spec`)
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithSubScalarScalar.sub`
- `probe:curve25519_dalek.backend.serial.curve_models.AffineNielsPoint.Insts.CoreOpsArithNegAffineNielsPoint`
- `probe:curve25519_dalek.backend.serial.scalar_mul.variable_base.mul` (spec: `probe:curve25519_dalek.backend.serial.scalar_mul.variable_base.mul_spec`)
- `probe:curve25519_dalek.backend.serial.u64.field.FieldElement51.Insts.SubtleConditionallySelectable`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexMutUsizeU64`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.Insts.ZeroizeZeroize`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.add` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.add_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.as_montgomery` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.as_montgomery_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb0` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb0_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb1` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb1_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb2` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb2_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb3` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb3_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb4` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb4_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi0_xfer` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi0_xfer_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi12` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi12_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi3` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi3_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo0` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo0_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo12` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo12_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo34` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo34_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery_loop` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery_loop_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_mul` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_mul_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce.part1`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_square` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_square_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul_internal` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul_internal_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square_internal` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square_internal_spec`)
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.sub` (spec: `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.sub_spec`)
- `probe:curve25519_dalek.backend.variable_base_mul`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithMulSharedBScalarEdwardsPoint.mul`
- `probe:curve25519_dalek.edwards.EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint`
- `probe:curve25519_dalek.edwards.EdwardsPoint.is_small_order` (spec: `probe:curve25519_dalek.edwards.EdwardsPoint.is_small_order_spec`)
- `probe:curve25519_dalek.edwards.EdwardsPoint.is_torsion_free` (spec: `probe:curve25519_dalek.edwards.EdwardsPoint.is_torsion_free_spec`)
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base` (spec: `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base_spec`)
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped` (spec: `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped_spec`)
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_clamped` (spec: `probe:curve25519_dalek.edwards.EdwardsPoint.mul_clamped_spec`)
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.CoreDefaultDefault`
- `probe:curve25519_dalek.edwards.affine.AffinePoint.Insts.ZeroizeDefaultIsZeroes`
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulAssignScalar`
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base` (spec: `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base_spec`)
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped` (spec: `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped_spec`)
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulScalarRistrettoPoint.mul`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulSharedBScalarRistrettoPoint`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithMulSharedBScalarRistrettoPoint.mul`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.Insts.CoreOpsArithNegRistrettoPoint.neg`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.mul_base` (spec: `probe:curve25519_dalek.ristretto.RistrettoPoint.mul_base_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreDefaultDefault`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddScalarScalar.add`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar.add` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar.add_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAffinePointEdwardsPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAffinePointEdwardsPoint.mul`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar.mul_assign` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar.mul_assign_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulRistrettoPointRistrettoPoint.mul`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulShared0AffinePointEdwardsPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulShared0AffinePointEdwardsPoint.mul`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBEdwardsPointEdwardsPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBEdwardsPointEdwardsPoint.mul`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBRistrettoPointRistrettoPoint`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBRistrettoPointRistrettoPoint.mul`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar.mul` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar.mul_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar.neg` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar.neg_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubScalarScalar.sub`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar.sub` (spec: `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar.sub_spec`)
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsIndexIndexUsizeU8`
- `probe:curve25519_dalek.scalar.Scalar.Insts.ZeroizeZeroize`
- `probe:curve25519_dalek.scalar.Scalar.as_radix_16` (spec: `probe:curve25519_dalek.scalar.Scalar.as_radix_16_spec`)
- `probe:curve25519_dalek.scalar.Scalar.as_radix_16_loop0` (spec: `probe:curve25519_dalek.scalar.Scalar.as_radix_16_loop0_spec`)
- `probe:curve25519_dalek.scalar.Scalar.as_radix_2w` (spec: `probe:curve25519_dalek.scalar.Scalar.as_radix_2w_spec`)
- `probe:curve25519_dalek.scalar.Scalar.batch_invert` (spec: `probe:curve25519_dalek.scalar.Scalar.batch_invert_spec`)
- `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order` (spec: `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order_spec`)
- `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order_wide` (spec: `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order_wide_spec`)
- `probe:curve25519_dalek.scalar.Scalar.from_canonical_bytes` (spec: `probe:curve25519_dalek.scalar.Scalar.from_canonical_bytes_spec`)
- `probe:curve25519_dalek.scalar.Scalar.invert` (spec: `probe:curve25519_dalek.scalar.Scalar.invert_spec`)
- `probe:curve25519_dalek.scalar.Scalar.is_canonical` (spec: `probe:curve25519_dalek.scalar.Scalar.is_canonical_spec`)
- `probe:curve25519_dalek.scalar.Scalar.reduce` (spec: `probe:curve25519_dalek.scalar.Scalar.reduce_spec`)
- `probe:curve25519_dalek.scalar.Scalar.unpack` (spec: `probe:curve25519_dalek.scalar.Scalar.unpack_spec`)
- `probe:curve25519_dalek.scalar.Scalar52.invert` (spec: `probe:curve25519_dalek.scalar.Scalar52.invert_spec`)
- `probe:curve25519_dalek.scalar.Scalar52.montgomery_invert` (spec: `probe:curve25519_dalek.scalar.Scalar52.montgomery_invert_spec`)
- `probe:curve25519_dalek.scalar.Scalar52.montgomery_invert.square_multiply` (spec: `probe:curve25519_dalek.scalar.Scalar52.square_multiply_spec`)

## 6. Verified lemmas (79)

- `probe:curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithMulSharedAScalarEdwardsPoint.mul_spec`
- `probe:curve25519_dalek.Shared0RistrettoPoint.Insts.CoreOpsArithMulSharedAScalarRistrettoPoint.mul_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithAddSharedAScalarScalar.add_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAEdwardsPointEdwardsPoint.mul_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedARistrettoPointRistrettoPoint.mul_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithMulSharedAScalarScalar.mul_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithNegScalar.neg_spec`
- `probe:curve25519_dalek.Shared0Scalar.Insts.CoreOpsArithSubSharedAScalarScalar.sub_spec`
- `probe:curve25519_dalek.SharedAEdwardsPoint.Insts.CoreOpsArithMulScalarEdwardsPoint.mul_spec`
- `probe:curve25519_dalek.SharedAScalar.Insts.CoreOpsArithMulScalarScalar.mul_spec`
- `probe:curve25519_dalek.backend.serial.scalar_mul.variable_base.mul_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.add_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.as_montgomery_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.conditional_add_l_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_hi0_xfer`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_hi12`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_hi3`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_lo0`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_lo12`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.fold_from_bytes_wide_lo34`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_eq`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb0_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb1_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb2_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb3_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_limb4_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_eq`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi0_xfer_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi12_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_hi3_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo0_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo12_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_lo34_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_bytes_wide_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery_loop_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.from_montgomery_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_mul_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_reduce_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.montgomery_square_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul_internal_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.mul_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square_internal_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.square_spec`
- `probe:curve25519_dalek.backend.serial.u64.scalar.Scalar52.sub_spec`
- `probe:curve25519_dalek.edwards.EdwardsPoint.is_small_order_spec`
- `probe:curve25519_dalek.edwards.EdwardsPoint.is_torsion_free_spec`
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base_clamped_spec`
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_base_spec`
- `probe:curve25519_dalek.edwards.EdwardsPoint.mul_clamped_spec`
- `probe:curve25519_dalek.math.elligator_pure_val_x`
- `probe:curve25519_dalek.math.elligator_pure_val_y`
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base_clamped_spec`
- `probe:curve25519_dalek.montgomery.MontgomeryPoint.mul_base_spec`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.elligator_ristretto_flavor_spec`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.from_uniform_bytes_spec`
- `probe:curve25519_dalek.ristretto.RistrettoPoint.mul_base_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithAddSharedBScalarScalar.add_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignScalar.mul_assign_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulAssignSharedAScalar.mul_assign_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulEdwardsPointEdwardsPoint.mul_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulScalarScalar.mul_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulSharedBScalarScalar.mul_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithNegScalar.neg_spec`
- `probe:curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithSubSharedBScalarScalar.sub_spec`
- `probe:curve25519_dalek.scalar.Scalar.as_radix_16_loop0_spec`
- `probe:curve25519_dalek.scalar.Scalar.as_radix_16_spec`
- `probe:curve25519_dalek.scalar.Scalar.as_radix_2w_spec`
- `probe:curve25519_dalek.scalar.Scalar.batch_invert_spec`
- `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order_spec`
- `probe:curve25519_dalek.scalar.Scalar.from_bytes_mod_order_wide_spec`
- `probe:curve25519_dalek.scalar.Scalar.from_canonical_bytes_spec`
- `probe:curve25519_dalek.scalar.Scalar.invert_spec`
- `probe:curve25519_dalek.scalar.Scalar.is_canonical_spec`
- `probe:curve25519_dalek.scalar.Scalar.reduce_spec`
- `probe:curve25519_dalek.scalar.Scalar.unpack_spec`
- `probe:curve25519_dalek.scalar.Scalar52.invert_spec`
- `probe:curve25519_dalek.scalar.Scalar52.montgomery_invert_spec`
- `probe:curve25519_dalek.scalar.Scalar52.square_multiply_spec`

## 7. Out-of-scope public API functions (0)

Public API functions that Lean (via Aeneas) did not process.

None

---

## Public API accounting

| Category | Count |
|----------|------:|
| Verified public API | 0 |
| Trusted public API | 0 |
| Out-of-scope public API | 0 |
| **Total public API** | **0** |
