# Comparison of Lean and Verus Verified Functions

## Summary Statistics

- **Total Lean verified functions**: 75
- **Total Verus verified functions**: 91
- **Functions verified in both**: 31
- **Functions verified in Lean but not Verus**: 44
- **Functions verified in Verus but not Lean**: 60

- **Total Lean specified functions (specified/verified)**: 97
- **Total Verus specified functions (has_spec=yes)**: 163
- **Functions specified in both**: 52
- **Functions specified in Lean but not Verus**: 45
- **Functions specified in Verus but not Lean**: 111

## Functions Verified in Lean but Not Verus

Total: 44 functions

### curve25519_dalek::backend::serial::curve_models::CompletedPoint

Total: 3 functions:

- `curve25519_dalek::backend::serial::curve_models::CompletedPoint::add`
- `curve25519_dalek::backend::serial::curve_models::CompletedPoint::as_extended`
- `curve25519_dalek::backend::serial::curve_models::CompletedPoint::as_projective`

### curve25519_dalek::backend::serial::curve_models::ProjectivePoint

Total: 2 functions:

- `curve25519_dalek::backend::serial::curve_models::ProjectivePoint::as_extended`
- `curve25519_dalek::backend::serial::curve_models::ProjectivePoint::double`

### curve25519_dalek::backend::serial::u64::constants

Total: 12 functions:

- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D`
- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D2`
- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D_MINUS_ONE_SQUARED`
- `curve25519_dalek::backend::serial::u64::constants::INVSQRT_A_MINUS_D`
- `curve25519_dalek::backend::serial::u64::constants::L`
- `curve25519_dalek::backend::serial::u64::constants::LFACTOR`
- `curve25519_dalek::backend::serial::u64::constants::MINUS_ONE`
- `curve25519_dalek::backend::serial::u64::constants::ONE_MINUS_EDWARDS_D_SQUARED`
- `curve25519_dalek::backend::serial::u64::constants::R`
- `curve25519_dalek::backend::serial::u64::constants::RR`
- `curve25519_dalek::backend::serial::u64::constants::SQRT_AD_MINUS_ONE`
- `curve25519_dalek::backend::serial::u64::constants::SQRT_M1`

### curve25519_dalek::backend::serial::u64::field::FieldElement51

Total: 7 functions:

- `curve25519_dalek::backend::serial::u64::field::FieldElement51::MINUS_ONE`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ONE`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ZERO`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_select`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ct_eq`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::from_bytes`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::pow2k`

### curve25519_dalek::backend::serial::u64::scalar

Total: 1 functions:

- `curve25519_dalek::backend::serial::u64::scalar::m`

### curve25519_dalek::backend::serial::u64::scalar::Scalar52

Total: 2 functions:

- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::ZERO`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::invert`

### curve25519_dalek::edwards::EdwardsPoint

Total: 5 functions:

- `curve25519_dalek::edwards::EdwardsPoint::as_projective_niels`
- `curve25519_dalek::edwards::EdwardsPoint::ct_eq`
- `curve25519_dalek::edwards::EdwardsPoint::identity`
- `curve25519_dalek::edwards::EdwardsPoint::to_affine`
- `curve25519_dalek::edwards::EdwardsPoint::to_montgomery`

### curve25519_dalek::field::FieldElement51

Total: 6 functions:

- `curve25519_dalek::field::FieldElement51::invert`
- `curve25519_dalek::field::FieldElement51::invsqrt`
- `curve25519_dalek::field::FieldElement51::is_negative`
- `curve25519_dalek::field::FieldElement51::is_zero`
- `curve25519_dalek::field::FieldElement51::pow22501`
- `curve25519_dalek::field::FieldElement51::pow_p58`

### curve25519_dalek::ristretto::CompressedRistretto

Total: 2 functions:

- `curve25519_dalek::ristretto::CompressedRistretto::as_bytes`
- `curve25519_dalek::ristretto::CompressedRistretto::to_bytes`

### curve25519_dalek::scalar

Total: 1 functions:

- `curve25519_dalek::scalar::clamp_integer`

### curve25519_dalek::scalar::Scalar

Total: 2 functions:

- `curve25519_dalek::scalar::Scalar::ONE`
- `curve25519_dalek::scalar::Scalar::ZERO`

### curve25519_dalek::scalar::backend::serial::u64::scalar::Scalar52

Total: 1 functions:

- `curve25519_dalek::scalar::backend::serial::u64::scalar::Scalar52::pack`

## Functions Verified in Verus but Not Lean

Total: 60 functions

### curve25519_dalek::backend::serial::curve_models::AffineNielsPoint

Total: 2 functions:

- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::identity`
- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::zeroize`

### curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint

Total: 2 functions:

- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::identity`
- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::zeroize`

### curve25519_dalek::backend::serial::u64::field::FieldElement51

Total: 2 functions:

- `curve25519_dalek::backend::serial::u64::field::FieldElement51::load8_at`
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::zeroize`

### curve25519_dalek::backend::serial::u64::scalar

Total: 1 functions:

- `curve25519_dalek::backend::serial::u64::scalar::part2`

### curve25519_dalek::backend::serial::u64::scalar::Scalar52

Total: 9 functions:

- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::as_bytes`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::from_bytes`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::from_bytes_wide`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::m`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::mul`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::square`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::sub`
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::zeroize`

### curve25519_dalek::edwards::CompressedEdwardsY

Total: 4 functions:

- `curve25519_dalek::edwards::CompressedEdwardsY::ct_eq`
- `curve25519_dalek::edwards::CompressedEdwardsY::step_2`
- `curve25519_dalek::edwards::CompressedEdwardsY::to_bytes`
- `curve25519_dalek::edwards::CompressedEdwardsY::zeroize`

### curve25519_dalek::edwards::EdwardsPoint

Total: 10 functions:

- `curve25519_dalek::edwards::EdwardsPoint::add_assign`
- `curve25519_dalek::edwards::EdwardsPoint::is_small_order`
- `curve25519_dalek::edwards::EdwardsPoint::mul`
- `curve25519_dalek::edwards::EdwardsPoint::mul_assign`
- `curve25519_dalek::edwards::EdwardsPoint::mul_base`
- `curve25519_dalek::edwards::EdwardsPoint::mul_base_clamped`
- `curve25519_dalek::edwards::EdwardsPoint::neg`
- `curve25519_dalek::edwards::EdwardsPoint::sub_assign`
- `curve25519_dalek::edwards::EdwardsPoint::sum`
- `curve25519_dalek::edwards::EdwardsPoint::zeroize`

### curve25519_dalek::edwards::Scalar

Total: 1 functions:

- `curve25519_dalek::edwards::Scalar::mul`

### curve25519_dalek::field::FieldElement

Total: 6 functions:

- `curve25519_dalek::field::FieldElement::ct_eq`
- `curve25519_dalek::field::FieldElement::invert`
- `curve25519_dalek::field::FieldElement::is_negative`
- `curve25519_dalek::field::FieldElement::is_zero`
- `curve25519_dalek::field::FieldElement::pow22501`
- `curve25519_dalek::field::FieldElement::pow_p58`

### curve25519_dalek::montgomery::MontgomeryPoint

Total: 3 functions:

- `curve25519_dalek::montgomery::MontgomeryPoint::as_bytes`
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_assign`
- `curve25519_dalek::montgomery::MontgomeryPoint::to_bytes`

### curve25519_dalek::montgomery::Scalar

Total: 1 functions:

- `curve25519_dalek::montgomery::Scalar::mul`

### curve25519_dalek::scalar

Total: 1 functions:

- `curve25519_dalek::scalar::square_multiply`

### curve25519_dalek::scalar::Scalar

Total: 13 functions:

- `curve25519_dalek::scalar::Scalar::add_assign`
- `curve25519_dalek::scalar::Scalar::bot_half`
- `curve25519_dalek::scalar::Scalar::index`
- `curve25519_dalek::scalar::Scalar::mul`
- `curve25519_dalek::scalar::Scalar::mul_assign`
- `curve25519_dalek::scalar::Scalar::neg`
- `curve25519_dalek::scalar::Scalar::product`
- `curve25519_dalek::scalar::Scalar::sub`
- `curve25519_dalek::scalar::Scalar::sub_assign`
- `curve25519_dalek::scalar::Scalar::sum`
- `curve25519_dalek::scalar::Scalar::to_radix_2w_size_hint`
- `curve25519_dalek::scalar::Scalar::top_half`
- `curve25519_dalek::scalar::Scalar::zeroize`

### curve25519_dalek::scalar::UnpackedScalar

Total: 1 functions:

- `curve25519_dalek::scalar::UnpackedScalar::pack`

### curve25519_dalek::window::NafLookupTable5<AffineNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable5<AffineNielsPoint>::select`

### curve25519_dalek::window::NafLookupTable5<ProjectiveNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable5<ProjectiveNielsPoint>::select`

### curve25519_dalek::window::NafLookupTable8<AffineNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable8<AffineNielsPoint>::select`

### curve25519_dalek::window::NafLookupTable8<ProjectiveNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable8<ProjectiveNielsPoint>::select`

## Functions Specified in Lean but Not Verus

Total: 45 functions

### curve25519_dalek::backend::serial::curve_models::CompletedPoint

Total: 1 functions:

- `curve25519_dalek::backend::serial::curve_models::CompletedPoint::add` (status: verified)

### curve25519_dalek::backend::serial::u64::constants

Total: 12 functions:

- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D2` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::EDWARDS_D_MINUS_ONE_SQUARED` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::INVSQRT_A_MINUS_D` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::L` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::LFACTOR` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::MINUS_ONE` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::ONE_MINUS_EDWARDS_D_SQUARED` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::R` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::RR` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::SQRT_AD_MINUS_ONE` (status: verified)
- `curve25519_dalek::backend::serial::u64::constants::SQRT_M1` (status: verified)

### curve25519_dalek::backend::serial::u64::field::FieldElement51

Total: 7 functions:

- `curve25519_dalek::backend::serial::u64::field::FieldElement51::MINUS_ONE` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ONE` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ZERO` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::conditional_select` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::ct_eq` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::from_bytes` (status: verified)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::to_bytes` (status: specified)

### curve25519_dalek::backend::serial::u64::scalar

Total: 1 functions:

- `curve25519_dalek::backend::serial::u64::scalar::m` (status: verified)

### curve25519_dalek::backend::serial::u64::scalar::Scalar52

Total: 5 functions:

- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::ZERO` (status: verified)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::conditional_add_l` (status: specified)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::invert` (status: verified)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::montgomery_invert` (status: specified)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::to_bytes` (status: specified)

### curve25519_dalek::edwards::EdwardsPoint

Total: 1 functions:

- `curve25519_dalek::edwards::EdwardsPoint::to_affine` (status: verified)

### curve25519_dalek::edwards::affine::AffinePoint

Total: 1 functions:

- `curve25519_dalek::edwards::affine::AffinePoint::compress` (status: specified)

### curve25519_dalek::field::FieldElement51

Total: 7 functions:

- `curve25519_dalek::field::FieldElement51::invert` (status: verified)
- `curve25519_dalek::field::FieldElement51::invsqrt` (status: verified)
- `curve25519_dalek::field::FieldElement51::is_negative` (status: verified)
- `curve25519_dalek::field::FieldElement51::is_zero` (status: verified)
- `curve25519_dalek::field::FieldElement51::pow22501` (status: verified)
- `curve25519_dalek::field::FieldElement51::pow_p58` (status: verified)
- `curve25519_dalek::field::FieldElement51::sqrt_ratio_i` (status: specified)

### curve25519_dalek::ristretto::CompressedRistretto

Total: 3 functions:

- `curve25519_dalek::ristretto::CompressedRistretto::as_bytes` (status: verified)
- `curve25519_dalek::ristretto::CompressedRistretto::decompress` (status: specified)
- `curve25519_dalek::ristretto::CompressedRistretto::to_bytes` (status: verified)

### curve25519_dalek::ristretto::RistrettoPoint

Total: 3 functions:

- `curve25519_dalek::ristretto::RistrettoPoint::add` (status: specified)
- `curve25519_dalek::ristretto::RistrettoPoint::elligator_ristretto_flavor` (status: specified)
- `curve25519_dalek::ristretto::RistrettoPoint::from_uniform_bytes` (status: specified)

### curve25519_dalek::scalar

Total: 1 functions:

- `curve25519_dalek::scalar::clamp_integer` (status: verified)

### curve25519_dalek::scalar::Scalar

Total: 2 functions:

- `curve25519_dalek::scalar::Scalar::ONE` (status: verified)
- `curve25519_dalek::scalar::Scalar::ZERO` (status: verified)

### curve25519_dalek::scalar::backend::serial::u64::scalar::Scalar52

Total: 1 functions:

- `curve25519_dalek::scalar::backend::serial::u64::scalar::Scalar52::pack` (status: verified)

## Functions Specified in Verus but Not Lean

Total: 111 functions

### curve25519_dalek::backend::serial::curve_models::AffineNielsPoint

Total: 4 functions:

- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::conditional_assign` (no proof)
- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::identity` (with proof)
- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::neg` (no proof)
- `curve25519_dalek::backend::serial::curve_models::AffineNielsPoint::zeroize` (with proof)

### curve25519_dalek::backend::serial::curve_models::EdwardsPoint

Total: 2 functions:

- `curve25519_dalek::backend::serial::curve_models::EdwardsPoint::add` (no proof)
- `curve25519_dalek::backend::serial::curve_models::EdwardsPoint::sub` (no proof)

### curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint

Total: 4 functions:

- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::conditional_assign` (no proof)
- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::identity` (with proof)
- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::neg` (no proof)
- `curve25519_dalek::backend::serial::curve_models::ProjectiveNielsPoint::zeroize` (with proof)

### curve25519_dalek::backend::serial::curve_models::ProjectivePoint

Total: 1 functions:

- `curve25519_dalek::backend::serial::curve_models::ProjectivePoint::is_valid` (no proof)

### curve25519_dalek::backend::serial::scalar_mul::variable_base

Total: 1 functions:

- `curve25519_dalek::backend::serial::scalar_mul::variable_base::mul` (no proof)

### curve25519_dalek::backend::serial::u64::field::FieldElement51

Total: 3 functions:

- `curve25519_dalek::backend::serial::u64::field::FieldElement51::load8_at` (with proof)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::sub_assign` (no proof)
- `curve25519_dalek::backend::serial::u64::field::FieldElement51::zeroize` (with proof)

### curve25519_dalek::backend::serial::u64::scalar

Total: 2 functions:

- `curve25519_dalek::backend::serial::u64::scalar::part1` (no proof)
- `curve25519_dalek::backend::serial::u64::scalar::part2` (with proof)

### curve25519_dalek::backend::serial::u64::scalar::Scalar52

Total: 6 functions:

- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::as_bytes` (with proof)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::index` (with proof)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::m` (with proof)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::mul` (with proof)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::square` (with proof)
- `curve25519_dalek::backend::serial::u64::scalar::Scalar52::zeroize` (with proof)

### curve25519_dalek::edwards::CompressedEdwardsY

Total: 6 functions:

- `curve25519_dalek::edwards::CompressedEdwardsY::ct_eq` (with proof)
- `curve25519_dalek::edwards::CompressedEdwardsY::identity` (no proof)
- `curve25519_dalek::edwards::CompressedEdwardsY::step_1` (no proof)
- `curve25519_dalek::edwards::CompressedEdwardsY::step_2` (with proof)
- `curve25519_dalek::edwards::CompressedEdwardsY::to_bytes` (with proof)
- `curve25519_dalek::edwards::CompressedEdwardsY::zeroize` (with proof)

### curve25519_dalek::edwards::EdwardsBasepointTable

Total: 3 functions:

- `curve25519_dalek::edwards::EdwardsBasepointTable::basepoint` (no proof)
- `curve25519_dalek::edwards::EdwardsBasepointTable::create` (no proof)
- `curve25519_dalek::edwards::EdwardsBasepointTable::mul_base` (no proof)

### curve25519_dalek::edwards::EdwardsPoint

Total: 15 functions:

- `curve25519_dalek::edwards::EdwardsPoint::add_assign` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::as_affine_niels` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::conditional_select` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::is_torsion_free` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::is_valid` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::mul` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::mul_assign` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::mul_base` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::mul_base_clamped` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::mul_clamped` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::neg` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::sub` (no proof)
- `curve25519_dalek::edwards::EdwardsPoint::sub_assign` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::sum` (with proof)
- `curve25519_dalek::edwards::EdwardsPoint::zeroize` (with proof)

### curve25519_dalek::edwards::Scalar

Total: 1 functions:

- `curve25519_dalek::edwards::Scalar::mul` (with proof)

### curve25519_dalek::field::FieldElement

Total: 9 functions:

- `curve25519_dalek::field::FieldElement::batch_invert` (no proof)
- `curve25519_dalek::field::FieldElement::ct_eq` (with proof)
- `curve25519_dalek::field::FieldElement::invert` (with proof)
- `curve25519_dalek::field::FieldElement::invsqrt` (no proof)
- `curve25519_dalek::field::FieldElement::is_negative` (with proof)
- `curve25519_dalek::field::FieldElement::is_zero` (with proof)
- `curve25519_dalek::field::FieldElement::pow22501` (with proof)
- `curve25519_dalek::field::FieldElement::pow_p58` (with proof)
- `curve25519_dalek::field::FieldElement::sqrt_ratio_i` (no proof)

### curve25519_dalek::montgomery::MontgomeryPoint

Total: 13 functions:

- `curve25519_dalek::montgomery::MontgomeryPoint::as_bytes` (with proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::ct_eq` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::elligator_encode` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::hash` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::identity` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_assign` (with proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_base` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_base_clamped` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_bits_be` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::mul_clamped` (no proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::to_bytes` (with proof)
- `curve25519_dalek::montgomery::MontgomeryPoint::zeroize` (no proof)

### curve25519_dalek::montgomery::ProjectivePoint

Total: 3 functions:

- `curve25519_dalek::montgomery::ProjectivePoint::as_affine` (no proof)
- `curve25519_dalek::montgomery::ProjectivePoint::differential_add_and_double` (no proof)
- `curve25519_dalek::montgomery::ProjectivePoint::identity` (no proof)

### curve25519_dalek::montgomery::Scalar

Total: 1 functions:

- `curve25519_dalek::montgomery::Scalar::mul` (with proof)

### curve25519_dalek::scalar

Total: 1 functions:

- `curve25519_dalek::scalar::square_multiply` (with proof)

### curve25519_dalek::scalar::Scalar

Total: 22 functions:

- `curve25519_dalek::scalar::Scalar::add` (no proof)
- `curve25519_dalek::scalar::Scalar::add_assign` (with proof)
- `curve25519_dalek::scalar::Scalar::as_radix_16` (no proof)
- `curve25519_dalek::scalar::Scalar::as_radix_2w` (no proof)
- `curve25519_dalek::scalar::Scalar::batch_invert` (no proof)
- `curve25519_dalek::scalar::Scalar::bits_le` (no proof)
- `curve25519_dalek::scalar::Scalar::bot_half` (with proof)
- `curve25519_dalek::scalar::Scalar::clamp_integer` (no proof)
- `curve25519_dalek::scalar::Scalar::from` (no proof)
- `curve25519_dalek::scalar::Scalar::index` (with proof)
- `curve25519_dalek::scalar::Scalar::mul` (with proof)
- `curve25519_dalek::scalar::Scalar::mul_assign` (with proof)
- `curve25519_dalek::scalar::Scalar::neg` (with proof)
- `curve25519_dalek::scalar::Scalar::non_adjacent_form` (no proof)
- `curve25519_dalek::scalar::Scalar::product` (with proof)
- `curve25519_dalek::scalar::Scalar::read_le_u64_into` (no proof)
- `curve25519_dalek::scalar::Scalar::sub` (with proof)
- `curve25519_dalek::scalar::Scalar::sub_assign` (with proof)
- `curve25519_dalek::scalar::Scalar::sum` (with proof)
- `curve25519_dalek::scalar::Scalar::to_radix_2w_size_hint` (with proof)
- `curve25519_dalek::scalar::Scalar::top_half` (with proof)
- `curve25519_dalek::scalar::Scalar::zeroize` (with proof)

### curve25519_dalek::scalar::UnpackedScalar

Total: 3 functions:

- `curve25519_dalek::scalar::UnpackedScalar::invert` (no proof)
- `curve25519_dalek::scalar::UnpackedScalar::montgomery_invert` (no proof)
- `curve25519_dalek::scalar::UnpackedScalar::pack` (with proof)

### curve25519_dalek::traits

Total: 1 functions:

- `curve25519_dalek::traits::is_identity` (no proof)

### curve25519_dalek::window::LookupTable<AffineNielsPoint>

Total: 2 functions:

- `curve25519_dalek::window::LookupTable<AffineNielsPoint>::from` (no proof)
- `curve25519_dalek::window::LookupTable<AffineNielsPoint>::select` (no proof)

### curve25519_dalek::window::LookupTable<ProjectiveNielsPoint>

Total: 2 functions:

- `curve25519_dalek::window::LookupTable<ProjectiveNielsPoint>::from` (no proof)
- `curve25519_dalek::window::LookupTable<ProjectiveNielsPoint>::select` (no proof)

### curve25519_dalek::window::NafLookupTable5

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable5::from` (no proof)

### curve25519_dalek::window::NafLookupTable5<AffineNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable5<AffineNielsPoint>::select` (with proof)

### curve25519_dalek::window::NafLookupTable5<ProjectiveNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable5<ProjectiveNielsPoint>::select` (with proof)

### curve25519_dalek::window::NafLookupTable8

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable8::from` (no proof)

### curve25519_dalek::window::NafLookupTable8<AffineNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable8<AffineNielsPoint>::select` (with proof)

### curve25519_dalek::window::NafLookupTable8<ProjectiveNielsPoint>

Total: 1 functions:

- `curve25519_dalek::window::NafLookupTable8<ProjectiveNielsPoint>::select` (with proof)

