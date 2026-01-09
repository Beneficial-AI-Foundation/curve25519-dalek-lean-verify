# Bounds Comparison Analysis: Lean vs Verus

This document provides a detailed LLM-style analysis comparing the actual bounds specifications between Lean and Verus implementations, based on reading the source files directly.

## Executive Summary

This analysis compares bounds specifications for 5 FieldElement51 functions between Lean and Verus verification efforts. **Key findings**:

### Key Differences Identified

#### 1. **Input Bound**

| Function | Lean Input Bound | Verus Input Bound | Difference |
|----------|------------------|-------------------|------------|
| `as_bytes` | None | None | ✅ Same |
| `neg` | `< 2^54` | `< 2^51` (via negate) | ❌ Lean more permissive |
| `reduce` | None | None (conditional for < 2^51) | ⚠️ Similar |
| `sub` | `a < 2^63`, `b < 2^54` | Both `< 2^54` | ❌ Lean allows larger minuend |
| `add` | Both `< 2^53` | Overflow-based (sum ≤ u64::MAX) | ⚠️ Different style |

**Notable**: Lean's `sub` allows extremely large first operand (`2^63`) because it adds `16*p` to avoid underflow - this reflects implementation strategy.

#### 2. **Output Bound**

| Function | Lean Output Bound | Verus Output Bound | Relationship |
|----------|-------------------|---------------------|--------------|
| `as_bytes` | `< p` (explicit) | `< p` (implicit via `% p()`) | ✅ Equivalent |
| `neg` | `≤ 2^51 + (2^13 - 1) * 19` | `< 2^52` | Lean tighter |
| `reduce` | `≤ 2^51 + (2^13 - 1) * 19` | `< 2^52` (+ `u64_5_as_nat < 2*p`) | Lean tighter; Verus has extra property |
| `sub` | `< 2^52` | `< 2^54` | Lean tighter |
| `add` | `< 2^54` (unconditional) | `< 2^52` (conditional on inputs < 2^51) | Different guarantees |

**Pattern**: Lean tends to provide tighter or unconditional output bounds; Verus sometimes uses conditional bounds based on input quality.

### Function-by-Function Match Status

1. **`as_bytes`**: ✅ **Similar** - Both specify canonical encoding < p
2. **`neg`**: ❌ **Different** - Input (2^54 vs 2^51) and output bounds differ
3. **`reduce`**: ⚠️ **Different** - Same correctness, different bound expressions
4. **`sub`**: ❌ **Different** - Different input requirements and output bounds
5. **`add`**: ❌ **Different** - Different input requirement styles and output bounds

**Summary**: 1/5 similar, 4/5 different.

---

## Analysis Method

For each function, I read:
1. The Lean spec file (from `Curve25519Dalek/Specs/`)
2. The Verus spec (from `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs`)

Then I extract and compare:
- **Input bounds** (requires/preconditions)
- **Output bounds** (ensures/postconditions)
- **Correctness properties** (modular arithmetic, etc.)

---

## Function 1: `FieldElement51::as_bytes`

### Lean Specification
**File**: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/AsBytes.lean`

**Theorem**: `as_bytes_spec`
```lean
theorem as_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    ∃ result, as_bytes self = ok result ∧
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p
```

**Extracted Bounds**:
- **Input bounds**: None (no precondition)
- **Output bounds**: 
  1. `as_bytes self = ok result` (existence - not a bound)
  2. `U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p]` (correctness)
  3. `U8x32_as_Nat result < p` (actual bound: result is canonical, < p)

### Verus Specification
**File**: `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs` (line 992)

**Function**: `as_bytes`
```rust
pub fn as_bytes(self) -> (r: [u8; 32])
    ensures
    // canonical encoding, i.e. mod p value
        u8_32_as_nat(&r) == u64_5_as_nat(self.limbs) % p(),
```

**Extracted Bounds**:
- **Input bounds**: None (no requires clause)
- **Output bounds**:
  1. Comment: "canonical encoding, i.e. mod p value"
  2. `u8_32_as_nat(&r) == u64_5_as_nat(self.limbs) % p()` (correctness)
  3. In the proof block, there's a comment: "The reduce function ensures the limbs are bounded by 2^52" (this is about internal computation, not the output bound)

### Comparison Analysis

**Issue with VERIFICATION_COMPARISON_DETAILED.md**:
The document incorrectly states:
- **Lean bounds**: `as_bytes self = ok result` (this is just existence, not a bound!)
- **Verus bounds**: `// canonical encoding` and `the limbs are bounded by 2^52` (the second is about internal computation, not output)

**Actual Bounds**:
- **Lean**: Output bound is `U8x32_as_Nat result < p` (canonical representation)
- **Verus**: Output bound is implicit - `u8_32_as_nat(&r) == u64_5_as_nat(self.limbs) % p()` implies `u8_32_as_nat(&r) < p()` (since x % p < p for any x)

**Conclusion**: Both specify the same bound (canonical encoding < p), but:
- Lean makes it explicit: `U8x32_as_Nat result < p`
- Verus makes it implicit: follows from `% p()` operation

**Match**: ✅ **Similar** - Both specify canonical encoding < p, just different presentation

---

## Function 2: `FieldElement51::neg`

### Lean Specification
**File**: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Neg.lean`

**Theorem**: `neg_spec`
```lean
theorem neg_spec (r : backend.serial.u64.field.FieldElement51)
    (h : ∀ i < 5, r[i]!.val < 2 ^ 54) :
    ∃ r_inv, neg r = ok r_inv ∧
    (Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0 ∧
    (∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19)
```

**Extracted Bounds**:
- **Input bounds**: `∀ i < 5, r[i]!.val < 2 ^ 54`
- **Output bounds**: 
  1. `neg r = ok r_inv` (existence)
  2. `(Field51_as_Nat r + Field51_as_Nat r_inv) % p = 0` (correctness: additive inverse)
  3. `∀ i < 5, r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19` (limb bound)

Note: `2^51 + (2^13 - 1) * 19 = 2^51 + 8191 * 19 = 2^51 + 155629 ≈ 2^51.0000000001`

### Verus Specification
**File**: `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs` (line 644)

**Function**: `neg` (implements `Neg` trait)
```rust
fn neg(self) -> (output: FieldElement51)
    ensures
        spec_field_element(&output) == math_field_neg(spec_field_element(self)),
        forall|i: int| 0 <= i < 5 ==> output.limbs[i] < (1u64 << 52),
```

**Extracted Bounds**:
- **Input bounds**: None explicit in `neg`, but `neg` calls `negate` which requires:
  - `forall|i: int| 0 <= i < 5 ==> old(self).limbs[i] < (1u64 << 51)` (from `negate`)
- **Output bounds**:
  1. `spec_field_element(&output) == math_field_neg(spec_field_element(self))` (correctness)
  2. `forall|i: int| 0 <= i < 5 ==> output.limbs[i] < (1u64 << 52)` (limb bound)

### Comparison Analysis

**Input Bounds**:
- **Lean**: Requires `r[i]!.val < 2^54` for all limbs
- **Verus**: `neg` itself has no explicit requires, but internally calls `negate` which requires `< 2^51`

**Output Bounds**:
- **Lean**: `r_inv[i]!.val ≤ 2^51 + (2^13 - 1) * 19 ≈ 2^51.0000000001`
- **Verus**: `output.limbs[i] < 2^52`

**Analysis**:
- Lean's bound `2^51 + (2^13 - 1) * 19` is more precise but approximately `2^51.0000000001`
- Verus's bound `2^52` is simpler but looser
- `2^51.0000000001 < 2^52`, so Lean's bound is tighter

**Conclusion**: 
- **Input**: Different (Lean: 2^54, Verus: 2^51 via negate)
- **Output**: Different but related (Lean: ~2^51.0000000001, Verus: 2^52)
- Both specify additive inverse correctness

**Match**: ❌ **Different** - Different input requirements and different output bound expressions

---

## Function 3: `FieldElement51::reduce`

### Lean Specification
**File**: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Reduce.lean`

**Theorem**: `reduce_spec`
```lean
theorem reduce_spec (limbs : Array U64 5#usize) :
    ∃ result, reduce limbs = ok result ∧
    (∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19) ∧
    Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p]
```

**Extracted Bounds**:
- **Input bounds**: None (no precondition)
- **Output bounds**:
  1. `reduce limbs = ok result` (existence)
  2. `∀ i < 5, result[i]!.val ≤ 2^51 + (2^13 - 1) * 19` (limb bound, same as neg)
  3. `Field51_as_Nat limbs ≡ Field51_as_Nat result [MOD p]` (correctness: preserves value mod p)

### Verus Specification
**File**: `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs` (line 845)

**Function**: `reduce`
```rust
fn reduce(mut limbs: [u64; 5]) -> (r: FieldElement51)
    ensures
        r.limbs == spec_reduce(limbs),
        forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52),
        (forall|i: int| 0 <= i < 5 ==> limbs[i] < (1u64 << 51)) ==> (r.limbs =~= limbs),
        u64_5_as_nat(r.limbs) == u64_5_as_nat(limbs) - p() * (limbs[4] >> 51),
        u64_5_as_nat(r.limbs) % p() == u64_5_as_nat(limbs) % p(),
        u64_5_as_nat(r.limbs) < 2 * p(),
```

**Extracted Bounds**:
- **Input bounds**: None explicit, but there's a conditional: if `limbs[i] < 2^51`, then output equals input
- **Output bounds**:
  1. `r.limbs == spec_reduce(limbs)` (specification function)
  2. `forall|i: int| 0 <= i < 5 ==> r.limbs[i] < (1u64 << 52)` (limb bound)
  3. `u64_5_as_nat(r.limbs) % p() == u64_5_as_nat(limbs) % p()` (correctness)
  4. `u64_5_as_nat(r.limbs) < 2 * p()` (additional bound)

### Comparison Analysis

**Input Bounds**:
- **Lean**: None
- **Verus**: None explicit, but conditional property for inputs < 2^51

**Output Bounds**:
- **Lean**: `result[i]!.val ≤ 2^51 + (2^13 - 1) * 19 ≈ 2^51.0000000001`
- **Verus**: `r.limbs[i] < 2^52` and `u64_5_as_nat(r.limbs) < 2 * p()`

**Analysis**:
- Lean's bound is more precise: `2^51 + (2^13 - 1) * 19 ≈ 2^51.0000000001`
- Verus's bound is simpler: `2^52`
- Both specify correctness (preserves value mod p)
- Verus additionally specifies `u64_5_as_nat(r.limbs) < 2 * p()` which is a stronger property about the total value

**Conclusion**:
- **Input**: Both have no explicit bounds
- **Output**: Different expressions but related (Lean: ~2^51.0000000001, Verus: 2^52)
- Both specify correctness mod p

**Match**: ⚠️ **Different** - Same correctness property, different bound expressions (Lean more precise, Verus simpler)

---

## Function 4: `FieldElement51::sub`

### Lean Specification
**File**: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Sub.lean`

**Theorem**: `sub_spec`
```lean
theorem sub_spec (a b : Array U64 5#usize)
    (h_bounds_a : ∀ i < 5, a[i]!.val < 2 ^ 63)
    (h_bounds_b : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    ∃ d, sub a b = ok d ∧
    (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
    (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p
```

**Extracted Bounds**:
- **Input bounds**: 
  1. `∀ i < 5, a[i]!.val < 2^63`
  2. `∀ i < 5, b[i]!.val < 2^54`
- **Output bounds**:
  1. `sub a b = ok d` (existence)
  2. `∀ i < 5, d[i]!.val < 2^52` (limb bound)
  3. `(Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p` (correctness: field subtraction)

### Verus Specification
**File**: `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs` (line 339)

**Function**: `sub` (implements `Sub` trait)
```rust
fn sub(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    ensures
        output == spec_sub_limbs(self, _rhs),
        spec_field_element(&output) == math_field_sub(
            spec_field_element(self),
            spec_field_element(_rhs),
        ),
        fe51_limbs_bounded(&output, 54),
```

**Extracted Bounds**:
- **Input bounds**: From `sub_req` (line 326): `fe51_limbs_bounded(self, 54) && fe51_limbs_bounded(_rhs, 54)`
  - This means: `forall|i: int| 0 <= i < 5 ==> self.limbs[i] < (1u64 << 54)`
- **Output bounds**:
  1. `output == spec_sub_limbs(self, _rhs)` (specification function)
  2. `spec_field_element(&output) == math_field_sub(...)` (correctness)
  3. `fe51_limbs_bounded(&output, 54)` which means `output.limbs[i] < 2^54`

### Comparison Analysis

**Input Bounds**:
- **Lean**: 
  - `a[i]!.val < 2^63` (very loose for first operand)
  - `b[i]!.val < 2^54` (for second operand)
- **Verus**: 
  - Both operands: `limbs[i] < 2^54`

**Output Bounds**:
- **Lean**: `d[i]!.val < 2^52`
- **Verus**: `output.limbs[i] < 2^54`

**Analysis**:
- Lean allows much larger first operand (2^63 vs 2^54) - this is because Lean's implementation adds 16*p to avoid underflow
- Lean's output bound is tighter (2^52 vs 2^54)
- Both specify field subtraction correctness

**Conclusion**:
- **Input**: Different (Lean allows larger first operand)
- **Output**: Different (Lean: 2^52, Verus: 2^54)
- Both specify correctness

**Match**: ❌ **Different** - Different input requirements and different output bounds

---

## Function 5: `FieldElement51::add`

### Lean Specification
**File**: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/Add.lean`

**Theorem**: `add_spec`
```lean
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 53) :
    ∃ result, add a b = ok result ∧
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^54)
```

**Extracted Bounds**:
- **Input bounds**: 
  1. `∀ i < 5, a[i]!.val < 2^53`
  2. `∀ i < 5, b[i]!.val < 2^53`
- **Output bounds**:
  1. `add a b = ok result` (existence)
  2. `∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val` (element-wise addition)
  3. `∀ i < 5, result[i]!.val < 2^54` (limb bound)

### Verus Specification
**File**: `dalek-lite/curve25519-dalek/src/backend/serial/u64/field.rs` (line 225)

**Function**: `add` (implements `Add` trait)
```rust
fn add(self, _rhs: &'a FieldElement51) -> (output: FieldElement51)
    ensures
        output == spec_add_fe51_limbs(self, _rhs),
        spec_field_element_as_nat(&output) == spec_field_element_as_nat(self)
            + spec_field_element_as_nat(_rhs),
        spec_field_element(&output) == math_field_add(
            spec_field_element(self),
            spec_field_element(_rhs),
        ),
        // Bound propagation: tighter inputs give tighter output
        fe51_limbs_bounded(self, 51) && fe51_limbs_bounded(_rhs, 51) ==> fe51_limbs_bounded(
            &output,
            52,
        ),
```

**Extracted Bounds**:
- **Input bounds**: From `add_req` (line 212): `sum_of_limbs_bounded(self, rhs, u64::MAX)`
  - This is about sum not overflowing u64, not explicit bit bounds
- **Output bounds**:
  1. `output == spec_add_fe51_limbs(self, _rhs)` (specification)
  2. `spec_field_element(&output) == math_field_add(...)` (correctness)
  3. Conditional: if inputs are `< 2^51`, then output is `< 2^52`

### Comparison Analysis

**Input Bounds**:
- **Lean**: Both operands: `limbs[i] < 2^53`
- **Verus**: `sum_of_limbs_bounded(self, rhs, u64::MAX)` - about overflow, not explicit bit bounds
  - Conditional property: if inputs `< 2^51`, then output `< 2^52`

**Output Bounds**:
- **Lean**: `result[i]!.val < 2^54` (unconditional)
- **Verus**: Conditional: `if inputs < 2^51 then output < 2^52`

**Analysis**:
- Lean specifies explicit input bounds (2^53) and explicit output bound (2^54)
- Verus uses overflow-based input requirement and conditional output bound
- Both specify element-wise addition correctness

**Conclusion**:
- **Input**: Different approaches (Lean: explicit 2^53, Verus: overflow-based)
- **Output**: Different (Lean: unconditional 2^54, Verus: conditional 2^52)
- Both specify correctness

**Match**: ❌ **Different** - Different input requirement styles and different output bounds