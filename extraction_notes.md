# Extraction Notes

## Core Problem: Dynamic Array Indexing

Two functions in `scalar.rs` cause Aeneas internal errors due to dynamic array indexing patterns:

- `non_adjacent_form` - computes width-w NAF representation
- `as_radix_2w` - computes radix-2^w representation

### What We Tried

Converting for loops to while loops did not solve the issue. The fundamental problem is the pattern:
```rust
output[i] = some_value;  // where i is computed dynamically
```

Aeneas cannot handle array indexing where the index is not statically known.

### Solution

Use `#[cfg(not(verify))]` to exclude these functions and all their callers from extraction.
The `verify` cfg flag is set in `.cargo/config.toml`.

## Dependency Graph of Excluded Functions

```
non_adjacent_form (scalar.rs)
├── vartime_double_base::mul
│   └── backend::vartime_double_base_mul
│       └── edwards::vartime_double_scalar_mul_basepoint
│           └── ristretto::vartime_double_scalar_mul_basepoint
├── straus::VartimeMultiscalarMul
│   └── backend::straus_optional_multiscalar_mul
│       └── edwards::VartimeMultiscalarMul
│           └── ristretto::VartimeMultiscalarMul
└── precomputed_straus::VartimePrecomputedMultiscalarMul
    └── backend::VartimePrecomputedStraus
        ├── edwards::VartimeEdwardsPrecomputation
        └── ristretto::VartimeRistrettoPrecomputation

as_radix_2w (scalar.rs)
├── to_radix_2w_size_hint (helper)
└── pippenger::VartimeMultiscalarMul
    └── backend::pippenger_optional_multiscalar_mul
        └── (feeds into edwards::VartimeMultiscalarMul above)

bits_le (scalar.rs) [uses iterator .map()]
└── montgomery::Mul<&Scalar> [FIXED - rewritten to avoid iterator]
    ├── montgomery::MulAssign<&Scalar>
    ├── montgomery::Mul<&MontgomeryPoint> for &Scalar
    └── montgomery::mul_clamped

mul_bits_be (montgomery.rs) [impl Iterator parameter]
└── excluded via #[cfg(not(verify))] - superseded by inlined Mul<&Scalar>

Product/Sum impls (scalar.rs) [iterator trait issues]
└── (standalone, no downstream deps)
```

## Fixed: Montgomery Scalar Multiplication

The `montgomery::Mul<&Scalar>` implementation originally called `scalar.bits_le().rev().skip(1)`,
which pulled in iterator trait machinery. This was rewritten to use a direct while loop that
iterates over scalar bits without using iterators:

```rust
// Iterate from bit 254 down to 0 (skip MSB which is 0 by scalar invariant)
let mut i: isize = 254;
while i >= 0 {
    let byte_idx = (i >> 3) as usize;
    let bit_idx = (i & 7) as usize;
    let cur_bit = ((scalar_bytes[byte_idx] >> bit_idx) & 1u8) == 1u8;
    // ... Montgomery ladder step ...
    i -= 1;
}
```

This allows Montgomery point-scalar multiplication to be extracted.

## Precomputed Tables

The `EdwardsBasepointTable` and related types are excluded because they use `non_adjacent_form`.
The `mul_base` functions fall back to using `ED25519_BASEPOINT_POINT` (slower but works).

## What Still Works

Core Scalar arithmetic: Add, Sub, Mul, Neg, from_bytes, to_bytes, reduce, invert, etc.
Core point operations: EdwardsPoint, RistrettoPoint, MontgomeryPoint arithmetic.
Compression/decompression, coordinate conversions, etc.

Only the variable-time optimized scalar multiplication paths are excluded.
