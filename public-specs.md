# Public Functions — Spec Statements

## `curve25519-dalek/src/backend/serial/curve_models/mod.rs`

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (result : backend.serial.curve_models.ProjectivePoint) =>
      Field51_as_Nat result.X = 0 ∧
      Field51_as_Nat result.Y = 1 ∧
      Field51_as_Nat result.Z = 1 ⦄ := by ...
```

### ✓ `neg`

```lean
theorem neg_spec
    (self : backend.serial.curve_models.AffineNielsPoint)
    (self_bound : ∀ i < 5, self.xy2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : AffineNielsPoint) =>
      result.y_plus_x = self.y_minus_x ∧
      result.y_minus_x = self.y_plus_x ∧
      (Field51_as_Nat self.xy2d + Field51_as_Nat result.xy2d) % p = 0 ⦄ := by ...
```

### ✓ `add`

```lean
theorem add_spec
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.AffineNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
    (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
    Shared0EdwardsPoint.Insts.CoreOpsArithAddSharedAAffineNielsPointCompletedPoint.add self other
      ⦃ (c : CompletedPoint) =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let T := Field51_as_Nat self.T
      let YpX := Field51_as_Nat other.y_plus_x
      let YmX := Field51_as_Nat other.y_minus_x
      let XY2D := Field51_as_Nat other.xy2d
      let X' := Field51_as_Nat c.X
      let Y' := Field51_as_Nat c.Y
      let Z' := Field51_as_Nat c.Z
      let T' := Field51_as_Nat c.T
      (X' + Y * YmX) % p = (((Y + X) * YpX) + X * YmX) % p ∧
      (Y' + X * YmX) % p = (((Y + X) * YpX) + Y  * YmX) % p ∧
      Z' % p = ((2 * Z) + (T * XY2D)) % p ∧
      (T' + (T * XY2D)) % p = (2 * Z) % p ⦄ := by ...
```

### ✓ `add`

```lean
theorem add_spec
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    add self other ⦃ (c : CompletedPoint) =>
      c.IsValid ∧ c.toPoint = self.toPoint + other.toPoint ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec
    (self : edwards.EdwardsPoint)
    (other : backend.serial.curve_models.AffineNielsPoint)
    (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
    (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
    (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
    (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
    (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
    (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
    (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
    Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub self other
      ⦃ (c : CompletedPoint) =>
      let X := Field51_as_Nat self.X
      let Y := Field51_as_Nat self.Y
      let Z := Field51_as_Nat self.Z
      let T := Field51_as_Nat self.T
      let YpX := Field51_as_Nat other.y_plus_x
      let YmX := Field51_as_Nat other.y_minus_x
      let XY2D := Field51_as_Nat other.xy2d
      let X' := Field51_as_Nat c.X
      let Y' := Field51_as_Nat c.Y
      let Z' := Field51_as_Nat c.Z
      let T' := Field51_as_Nat c.T
      (X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
      (Y' + X * YpX) % p = (((Y + X) * YmX) + Y  * YpX) % p ∧
      (Z' + (T * XY2D)) % p = (2 * Z) % p ∧
      T' % p = ((2 * Z) + (T * XY2D)) % p ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec
    (self : curve25519_dalek.edwards.EdwardsPoint) (hself : self.IsValid)
    (other : ProjectiveNielsPoint) (hother : other.IsValid) :
    sub self other ⦃ (c : CompletedPoint) =>
      c.IsValid ∧
      c.toPoint = self.toPoint - other.toPoint ⦄ := by ...
```

### ✓ `neg`

```lean
theorem neg_spec
    (self : ProjectiveNielsPoint) (self_bound : ∀ i < 5, self.T2d[i]!.val < 2 ^ 54) :
    neg self ⦃ (result : ProjectiveNielsPoint) =>
      result.Y_plus_X = self.Y_minus_X ∧
      result.Y_minus_X = self.Y_plus_X ∧
      result.Z = self.Z ∧
      (Field51_as_Nat self.T2d + Field51_as_Nat result.T2d) % p = 0 ⦄ := by ...
```

### ✓ `assert_receiver_is_total_eq`

```lean
theorem assert_receiver_is_total_eq_spec
    (self : backend.serial.curve_models.AffineNielsPoint) :
    assert_receiver_is_total_eq self ⦃ (result : Unit) => result = () ⦄ := by ...
```

### ✓ `eq`

```lean
theorem eq_spec
    (self other : backend.serial.curve_models.AffineNielsPoint) :
    eq self other ⦃ (b : Bool) =>
      b = true ↔
        self.y_plus_x.to_bytes = other.y_plus_x.to_bytes ∧
        self.y_minus_x.to_bytes = other.y_minus_x.to_bytes ∧
        self.xy2d.to_bytes = other.xy2d.to_bytes ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (q : AffineNielsPoint) =>
      Field51_as_Nat q.y_plus_x = 1 ∧
      Field51_as_Nat q.y_minus_x = 1 ∧
      Field51_as_Nat q.xy2d = 0 ⦄ := by ...
```

### ✓ `conditional_assign`

```lean
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result :
        backend.serial.curve_models.AffineNielsPoint) =>
      (∀ i < 5, result.y_plus_x[i]!.val =
        if choice.val = 1#u8 then other.y_plus_x[i]!.val else self.y_plus_x[i]!.val) ∧
      (∀ i < 5, result.y_minus_x[i]!.val =
        if choice.val = 1#u8 then other.y_minus_x[i]!.val else self.y_minus_x[i]!.val) ∧
      (∀ i < 5, result.xy2d[i]!.val =
        if choice.val = 1#u8 then other.xy2d[i]!.val else self.xy2d[i]!.val) ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : backend.serial.curve_models.AffineNielsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : backend.serial.curve_models.AffineNielsPoint) =>
      (∀ i < 5, result.y_plus_x[i]!.val =
        if choice.val = 1#u8 then b.y_plus_x[i]!.val else a.y_plus_x[i]!.val) ∧
      (∀ i < 5, result.y_minus_x[i]!.val =
        if choice.val = 1#u8 then b.y_minus_x[i]!.val else a.y_minus_x[i]!.val) ∧
      (∀ i < 5, result.xy2d[i]!.val =
        if choice.val = 1#u8 then b.xy2d[i]!.val else a.xy2d[i]!.val) ⦄ := by ...
```

### ✓ `as_extended`

```lean
theorem as_extended_spec (q : CompletedPoint)
    (h_q_Valid : q.IsValid) :
    as_extended q ⦃ (e : edwards.EdwardsPoint) =>
      let X := Field51_as_Nat q.X
      let Y := Field51_as_Nat q.Y
      let Z := Field51_as_Nat q.Z
      let T := Field51_as_Nat q.T
      let X' := Field51_as_Nat e.X
      let Y' := Field51_as_Nat e.Y
      let Z' := Field51_as_Nat e.Z
      let T' := Field51_as_Nat e.T
      X' % p = (X * T) % p ∧
      Y' % p = (Y * Z) % p ∧
      Z' % p = (Z * T) % p ∧
      T' % p = (X * Y) % p ∧
      (∀ i < 5, e.X[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.Y[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.Z[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, e.T[i]!.val < 2 ^ 52) ∧
      e.IsValid ∧
      e.toPoint = q.toPoint ⦄ := by ...
```

### ✓ `as_projective`

```lean
theorem as_projective_spec
    (q : CompletedPoint) (hq_valid : q.IsValid) :
    ∃ proj, as_projective q = ok proj ∧
    proj.IsValid ∧ proj.toPoint = q.toPoint := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (result : ProjectiveNielsPoint) =>
      Field51_as_Nat result.Y_plus_X = 1 ∧
      Field51_as_Nat result.Y_minus_X = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T2d = 0 ⦄ := by ...
```

### ✓ `conditional_assign`

```lean
theorem conditional_assign_spec
    (self other : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (result : ProjectiveNielsPoint) =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_plus_X[i]!.val else self.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then other.Y_minus_X[i]!.val else self.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then other.Z[i]!.val else self.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then other.T2d[i]!.val else self.T2d[i]!.val) ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : backend.serial.curve_models.ProjectiveNielsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : ProjectiveNielsPoint) =>
      (∀ i < 5, result.Y_plus_X[i]!.val =
        if choice.val = 1#u8 then b.Y_plus_X[i]!.val else a.Y_plus_X[i]!.val) ∧
      (∀ i < 5, result.Y_minus_X[i]!.val =
        if choice.val = 1#u8 then b.Y_minus_X[i]!.val else a.Y_minus_X[i]!.val) ∧
      (∀ i < 5, result.Z[i]!.val =
        if choice.val = 1#u8 then b.Z[i]!.val else a.Z[i]!.val) ∧
      (∀ i < 5, result.T2d[i]!.val =
        if choice.val = 1#u8 then b.T2d[i]!.val else a.T2d[i]!.val) ⦄ := by ...
```

### ✓ `as_extended`

```lean
theorem as_extended_spec
    (q : ProjectivePoint)
    (h_qX_bounds : ∀ i, i < 5 → (q.X[i]!).val < 2 ^ 54)
    (h_qY_bounds : ∀ i, i < 5 → (q.Y[i]!).val < 2 ^ 54)
    (h_qZ_bounds : ∀ i, i < 5 → (q.Z[i]!).val < 2 ^ 54) :
    as_extended q ⦃ (e : curve25519_dalek.edwards.EdwardsPoint) =>
      let X := Field51_as_Nat q.X
      let Y := Field51_as_Nat q.Y
      let Z := Field51_as_Nat q.Z
      let X' := Field51_as_Nat e.X
      let Y' := Field51_as_Nat e.Y
      let Z' := Field51_as_Nat e.Z
      let T' := Field51_as_Nat e.T
      X' % p = (X * Z) % p ∧
      Y' % p = (Y * Z) % p ∧
      Z' % p = (Z^2) % p ∧
      T' % p = (X * Y) % p ⦄ := by ...
```

### ✓ `double`

```lean
theorem double_spec
    (q : ProjectivePoint) (hq_valid : q.IsValid) :
    ∃ c, ProjectivePoint.double q = ok c ∧
    c.IsValid ∧ c.toPoint = q.toPoint + q.toPoint := by ...
```

## `curve25519-dalek/src/backend/serial/u64/constants.rs`

### ✓ `ED25519_BASEPOINT_POINT`

```lean
theorem ED25519_BASEPOINT_POINT_spec :
    ED25519_BASEPOINT_POINT ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      _root_.L • result.toPoint = 0 ∧
      result.toPoint ≠ 0 ∧
      4 • result.toPoint ≠ 0 ∧
      result.Z.toField ^ 2 - result.Y.toField ^ 2 =
        34737626771194858627071295502606372355980995399692169211837275202373938891970 ^ 2 ∧
      result.toPoint = _root_.Edwards.basepoint ⦄ := by ...
```

### ✓ `EIGHT_TORSION`

```lean
theorem EIGHT_TORSION_spec :
    EIGHT_TORSION ⦃ result =>
      let P := result.val[1]
      P.IsValid ∧ 4 • P.toPoint ≠ 0 ∧ 8 • P.toPoint = 0 ∧
      (∀ (i : Fin 8), result.val[i].IsValid) ∧
      (∀ (i : Fin 8), result.val[i].toPoint = (i : ℕ) • P.toPoint) ⦄ := by ...
```

## `curve25519-dalek/src/backend/serial/u64/field.rs`

### ✓ `add`

```lean
theorem add_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 53) (hb : ∀ i < 5, b[i]!.val < 2 ^ 53) :
    add a b ⦃ result =>
    (∀ i < 5, result[i]!.val = a[i]!.val + b[i]!.val) ∧
    (∀ i < 5, result[i]!.val < 2^54) ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (self _rhs : Array U64 5#usize) (hself : ∀ i < 5, self[i]!.val < 2 ^ 54)
    (hrhs : ∀ i < 5, _rhs[i]!.val < 2 ^ 54) :
    mul self _rhs ⦃ (r : FieldElement51) =>
      Field51_as_Nat r ≡ (Field51_as_Nat self) * (Field51_as_Nat _rhs) [MOD p] ∧
      (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by ...
```

### ✓ `neg`

```lean
theorem neg_spec (self : FieldElement51)
    (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    neg self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val ≤ 2 ^ 52 ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 63) (hb : ∀ i < 5, b[i]!.val < 2 ^ 54) :
    sub a b ⦃ (d : FieldElement51) =>
      (∀ i < 5, d[i]!.val < 2 ^ 52) ∧
      (Field51_as_Nat d + Field51_as_Nat b) % p = Field51_as_Nat a % p ⦄ := by ...
```

### ✓ `add_assign`

```lean
theorem add_assign_spec (self _rhs : Array U64 5#usize)
    (ha : ∀ i < 5, self[i]!.val < 2 ^ 53) (hb : ∀ i < 5, _rhs[i]!.val < 2 ^ 53) :
    add_assign self _rhs ⦃ (result : FieldElement51) =>
      (∀ i < 5, (result[i]!).val = (self[i]!).val + (_rhs[i]!).val) ∧
      (∀ i < 5, result[i]!.val < 2 ^ 54) ⦄ := by ...
```

### ✓ `add_assign`

```lean
theorem add_assign_loop_spec (self _rhs : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (hab : ∀ j < 5, i.val ≤ j → self[j]!.val + _rhs[j]!.val ≤ U64.max) :
    add_assign_loop self _rhs i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = self[j]!.val + _rhs[j]!.val) ∧
      (∀ j < 5, j < i.val → result[j]! = self[j]!) ⦄ := by ...
```

### ✓ `conditional_assign`

```lean
theorem conditional_assign_spec (self other : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_assign self other choice ⦃ (res : FieldElement51) =>
      (∀ i < 5, res[i]! = (if choice.val = 1#u8 then other[i]! else self[i]!)) ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : backend.serial.u64.field.FieldElement51)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ res =>
      ∀ i < 5,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!) ⦄ := by ...
```

### ✓ `MINUS_ONE`

```lean
theorem MINUS_ONE_spec : MINUS_ONE ⦃ result => Field51_as_Nat result = p - 1 ⦄ := by ...
```

### ✓ `ONE`

```lean
theorem ONE_spec :
    ONE ⦃ result =>
    Field51_as_Nat result = 1 ∧
    (∀ i < 5, result[i]!.val < 2^51) ⦄ := by ...
```

### ✓ `ZERO`

```lean
theorem ZERO_spec : ZERO ⦃ (result : FieldElement51) =>
    Field51_as_Nat result = 0 ∧
    (∀ i< 5, (result[i]!.val) < 2^51 )⦄ := by ...
```

### ✓ `as_bytes`

```lean
theorem as_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    as_bytes self ⦃ result =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p ⦄ := by ...
```

### ✓ `from_bytes`

```lean
theorem from_bytes_spec (bytes : Array U8 32#usize) :
    from_bytes bytes ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (U8x32_as_Nat bytes % 2^255) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2^51) ⦄ := by ...
```

### ✓ `negate`

```lean
theorem negate_spec (self : FieldElement51) (h : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    negate self ⦃ (neg : FieldElement51) =>
      Field51_as_Nat self + Field51_as_Nat neg ≡ 0 [MOD p] ∧
      ∀ i < 5, neg[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `pow2k`

```lean
theorem pow2k_spec (self : Array U64 5#usize) (k : U32) (_ : 0 < k.val)
    (_ : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    pow2k self k ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (Field51_as_Nat self) ^ (2 ^ k.val) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by ...
```

### ✓ `pow2k`

```lean
theorem pow2k_loop_spec (k : U32) (a : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    pow2k_loop k a ⦃ (result : Std.Array U64 5#usize) =>
      Field51_as_Nat result ≡ (Field51_as_Nat a)^(2^k.val) [MOD p] ∧
      (if k.val = 0 then result = a else ∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by ...
```

### ✓ `square`

```lean
theorem square_spec (a : Array U64 5#usize) (ha : ∀ i < 5, a[i]!.val < 2 ^ 54) :
    square a ⦃ r =>
    Field51_as_Nat r ≡ (Field51_as_Nat a)^2 [MOD p] ∧ (∀ i < 5, r[i]!.val < 2 ^ 52) ⦄ := by ...
```

### ✓ `square2`

```lean
theorem square2_spec (self : Array U64 5#usize) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 54) :
    square2 self ⦃ (result : FieldElement51) =>
      Field51_as_Nat result ≡ (2 * (Field51_as_Nat self) ^ 2) [MOD p] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 53) ⦄ := by ...
```

### ✓ `square2`

```lean
theorem square2_loop_spec (square : Array U64 5#usize) (i : Usize) (hi : i.val ≤ 5)
    (h_no_overflow : ∀ j < 5, i.val ≤ j → square[j]!.val * 2 ≤ U64.max) :
    square2_loop square i ⦃ (result : FieldElement51) =>
      (∀ j < 5, i.val ≤ j → result[j]!.val = square[j]!.val * 2) ∧
      (∀ j < 5, j < i.val → result[j]! = square[j]!) ⦄ := by ...
```

### ✓ `to_bytes`

```lean
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    to_bytes self ⦃ result =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p ⦄ := by ...
```

## `curve25519-dalek/src/backend/serial/u64/scalar.rs`

### ✓ `ZERO`

```lean
theorem ZERO_spec : Scalar52_as_Nat ZERO = 0 := by ...
```

### ✓ `add`

```lean
theorem add_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52) (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < L) (hb' : Scalar52_as_Nat b ≤ L) :
    add a b ⦃ (v : Scalar52) =>
      Scalar52_as_Nat v ≡ Scalar52_as_Nat a + Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat v < L ∧ ∀ i < 5, v[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `add`

```lean
theorem add_loop_spec (a b sum : Scalar52) (mask carry : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52) (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < 2 ^ 259) (hb' : Scalar52_as_Nat b < 2 ^ 259)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5)
    (hcarry : i.val = 5 → carry.val < 2 ^ 52)
    (hcarry' : ∀ i < 5, carry.val < 2 ^ 53)
    (hsum : ∀ j < 5, sum[j]!.val < 2 ^ 52)
    (hsum' : ∀ j < 5, i.val ≤ j → sum[j]!.val = 0) :
    add_loop { start := i, «end» := 5#usize } a b sum mask carry ⦃ (sum' : Scalar52) =>
      (∀ j < 5, sum'[j]!.val < 2 ^ 52) ∧
      (∀ j < i.val, sum'[j]!.val = sum[j]!.val) ∧
      ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * sum'[j]!.val =
        ∑ j ∈ Finset.Ico i.val 5, 2 ^ (52 * j) * (a[j]!.val + b[j]!.val) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) ⦄ := by ...
```

### ✓ `as_montgomery`

```lean
theorem as_montgomery_spec (u : Scalar52) (h : ∀ i < 5, u[i]!.val < 2 ^ 52) :
    as_montgomery u ⦃ m =>
    Scalar52_as_Nat m ≡ (Scalar52_as_Nat u * R) [MOD L] ∧
    (∀ i < 5, m[i]!.val < 2 ^ 52) ∧
    Scalar52_as_Nat m < L ⦄ := by ...
```

### ✓ `from_bytes`

```lean
theorem from_bytes_spec (b : Array U8 32#usize) :
    from_bytes b ⦃ u =>
    Scalar52_as_Nat u = U8x32_as_Nat b ∧
    ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄
 := by ...
```

### ✓ `from_bytes`

```lean
theorem from_bytes_loop_spec (bytes : Array U8 32#usize)
    (words : Array U64 4#usize) (i : Usize) (hi : i.val ≤ 4)
    (h_prev : ∀ j, j < i.val → words[j]!.val = word_of_bytes bytes j) :
    from_bytes_loop bytes words i ⦃ words' =>
      words_as_Nat words' = U8x32_as_Nat bytes ⦄ := by ...
```

### ✓ `from_bytes_wide`

```lean
theorem from_bytes_wide_spec
    (b : Array U8 64#usize) :
    from_bytes_wide b ⦃ (u : Scalar52) =>
      Scalar52_as_Nat u = U8x64_as_Nat b % L ∧
      Scalar52_as_Nat u < L ∧
      ∀ i < 5, u[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `from_montgomery`

```lean
theorem from_montgomery_spec (self : Scalar52) (h_bounds : ∀ i < 5, self[i]!.val < 2 ^ 62) :
    from_montgomery self ⦃ (result : Scalar52) =>
      (Scalar52_as_Nat result * R) % L = Scalar52_as_Nat self % L ∧
      Scalar52_as_Nat result < L ∧ ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `from_montgomery`

```lean
theorem from_montgomery_loop_spec (self : Scalar52) (limbs : Array U128 9#usize) (i : Usize)
    (hi : i.val ≤ 5) :
    from_montgomery_loop self limbs i ⦃ (result : Std.Array U128 9#usize) =>
      (∀ j < 5, i.val ≤ j → result[j]! = UScalar.cast .U128 self[j]!) ∧
      (∀ j < 9, 5 ≤ j → result[j]! = limbs[j]!) ∧
      (∀ j < i.val, result[j]! = limbs[j]!) ⦄ := by ...
```

### ✓ `montgomery_mul`

```lean
theorem montgomery_mul_spec (m m' : Scalar52)
    (hm : ∀ i < 5, m[i]!.val < 2 ^ 62) (hm' : ∀ i < 5, m'[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat m * Scalar52_as_Nat m' < R * L) :
    montgomery_mul m m' ⦃ w =>
    (Scalar52_as_Nat m * Scalar52_as_Nat m') ≡ (Scalar52_as_Nat w * R) [MOD L] ∧
    (∀ i < 5, w[i]!.val < 2 ^ 52) ∧
    Scalar52_as_Nat w < L ⦄ := by ...
```

### ✓ `montgomery_square`

```lean
theorem montgomery_square_spec (m : Scalar52)
    (hm : ∀ i < 5, m[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat m * Scalar52_as_Nat m < R * L) :
    montgomery_square m ⦃ w =>
    (Scalar52_as_Nat m * Scalar52_as_Nat m) % L = (Scalar52_as_Nat w * R) % L ∧
    (∀ i < 5, w[i]!.val < 2 ^ 52) ∧
    Scalar52_as_Nat w < L ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat a * Scalar52_as_Nat b < R * L) :
    mul a b ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat a * Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat result < L ∧ ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `square`

```lean
theorem square_spec (self : Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat self * Scalar52_as_Nat self < R * L) :
    square self ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat self * Scalar52_as_Nat self [MOD L] ∧
      Scalar52_as_Nat result < L ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 52)
    (hb : ∀ i < 5, b[i]!.val < 2 ^ 52)
    (ha' : Scalar52_as_Nat a < Scalar52_as_Nat b + L)
    (hb' : Scalar52_as_Nat b ≤ L) :
    sub a b ⦃ result =>
    Scalar52_as_Nat result + Scalar52_as_Nat b ≡ Scalar52_as_Nat a [MOD L] ∧
    Scalar52_as_Nat result < L ∧
    (∀ i < 5, result[i]!.val < 2 ^ 52) ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_loop_spec (a b difference : Scalar52) (mask borrow : U64) (i : Usize)
    (ha : ∀ j < 5, a[j]!.val < 2 ^ 52)
    (hb : ∀ j < 5, b[j]!.val < 2 ^ 52)
    (hdiff : ∀ j < i.val, difference[j]!.val < 2 ^ 52)
    (hdiff_rest : ∀ j, i.val ≤ j → j < 5 → difference[j]!.val = 0)
    (hmask : mask.val = 2 ^ 52 - 1)
    (hi : i.val ≤ 5)
    (hborrow : borrow.val / 2 ^ 63 ≤ 1)
    (hinv : Scalar52_partial_as_Nat a i.val + borrow.val / 2 ^ 63 * 2 ^ (52 * i.val) =
            Scalar52_partial_as_Nat b i.val + Scalar52_partial_as_Nat difference i.val) :
    sub_loop a b difference mask borrow i ⦃ result =>
    (∀ j < 5, result.1[j]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat a + result.2.val / 2 ^ 63 * 2 ^ 260 =
     Scalar52_as_Nat b + Scalar52_as_Nat result.1) ⦄ := by ...
```

### ✓ `to_bytes`

```lean
theorem to_bytes_spec (self : Scalar52) (h : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (h' : Scalar52_as_Nat self < L) :
    to_bytes self ⦃ (result : Std.Array U8 32#usize) =>
      U8x32_as_Nat result = Scalar52_as_Nat self ∧ U8x32_as_Nat result < L ⦄ := by ...
```

## `curve25519-dalek/src/constants.rs`

### ✓ `RISTRETTO_BASEPOINT_POINT`

```lean
theorem RISTRETTO_BASEPOINT_POINT_spec :
    RISTRETTO_BASEPOINT_POINT ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧ _root_.L • result.toPoint = 0 ∧
      result.toPoint ≠ 0 ∧ 4 • result.toPoint ≠ 0 ∧
      result.toPoint = _root_.Edwards.basepoint ⦄ := by ...
```

## `curve25519-dalek/src/edwards.rs`

### ✓ `add`

```lean
theorem add_spec
    (self other : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    add self other ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by ...
```

### ○ `mul`

```lean
theorem mul_spec (e : edwards.EdwardsPoint) (s : scalar.Scalar)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
    mul e s ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint ⦄ := by ...
```

### ✓ `neg`

```lean
theorem neg_spec
    (self : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid) :
    neg self ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = -self.toPoint ⦄ := by ...
```

### ✓ `sub`

```lean
-- proven in Verus
theorem sub_spec
    (self other : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    sub self other ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint - other.toPoint ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (s : scalar.Scalar) (e : edwards.EdwardsPoint)
    (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255)
    (h_e_valid : e.IsValid) :
    mul s e ⦃ result =>
    result.IsValid ∧
    result.toPoint = (U8x32_as_Nat s.bytes) • e.toPoint ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (q : edwards.CompressedEdwardsY) =>
      U8x32_as_Nat q = 1 ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec
    (self other : CompressedEdwardsY) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔ self = other ⦄ := by ...
```

### ✓ `as_bytes`

```lean
theorem as_bytes_spec
    (self : edwards.CompressedEdwardsY) :
    as_bytes self ⦃ result =>
    result = self ⦄ := by ...
```

### ○ `decompress`

```lean
theorem decompress_spec (cey : edwards.CompressedEdwardsY) :
    edwards.CompressedEdwardsY.decompress cey ⦃ result =>
      let y : CurveField := (U8x32_as_Nat cey % 2 ^ 255 : CurveField)
      let x_sign_bit := cey[31]!.val.testBit 7
      -- Decompression succeeds iff y is a valid Edwards y-coordinate
      (result.isSome ↔ ∃ pt : Point Ed25519, pt.y = y) ∧
      -- When successful:
      (∀ ep, result = some ep →
        -- is_well_formed_edwards_point
        ep.IsValid ∧
        -- Y matches the encoded y-coordinate (ZMod and Nat levels)
        ep.Y.toField = y ∧
        Field51_as_Nat ep.Y ≡ (U8x32_as_Nat cey % 2 ^ 255) [MOD p] ∧
        -- Z = 1 (ZMod and Nat levels)
        ep.Z.toField = 1 ∧
        Field51_as_Nat ep.Z % p = 1 ∧
        ep.T.toField = ep.X.toField * ep.Y.toField ∧
        -- X sign matches bit 255
        -- (when y² ≠ 1, i.e. the non-degenerate case where x ≠ 0)
        (y ^ 2 ≠ 1 →
          (x_sign_bit ↔ (Field51_as_Nat ep.X % p) % 2 = 1))) ⦄ := by ...
```

### ✓ `from_slice`

```lean
theorem from_slice_spec
    (bytes : Slice U8) :
    from_slice bytes ⦃ (result : core.result.Result CompressedEdwardsY core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ cey : CompressedEdwardsY, result = .Ok cey ∧ cey.val = bytes.val) ∧
      (bytes.length ≠ 32 → result = .Err ()) ⦄ := by ...
```

### ✓ `eq`

```lean
theorem eq_spec (self other : EdwardsPoint) (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    eq self other ⦃ result =>
    result = true ↔ self.toPoint = other.toPoint ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (q : EdwardsPoint) =>
      Field51_as_Nat q.X = 0 ∧ Field51_as_Nat q.Y = 1 ∧
      Field51_as_Nat q.Z = 1 ∧ Field51_as_Nat q.T = 0 ∧
      q.IsValid ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : EdwardsPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : EdwardsPoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec (e1 e2 : EdwardsPoint)
  -- Bounds are needed for the internal field multiplications
  (h_e1_X : ∀ i, i < 5 → e1.X.val[i]!.val ≤ 2 ^ 53)
  (h_e1_Y : ∀ i, i < 5 → e1.Y.val[i]!.val ≤ 2 ^ 53)
  (h_e1_Z : ∀ i, i < 5 → e1.Z.val[i]!.val ≤ 2 ^ 53)
  (h_e2_X : ∀ i, i < 5 → e2.X.val[i]!.val ≤ 2 ^ 53)
  (h_e2_Y : ∀ i, i < 5 → e2.Y.val[i]!.val ≤ 2 ^ 53)
  (h_e2_Z : ∀ i, i < 5 → e2.Z.val[i]!.val ≤ 2 ^ 53) :
  ct_eq e1 e2 ⦃ c =>
  (c = Choice.one ↔
    (Field51_as_Nat e1.X * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.X * Field51_as_Nat e1.Z) [MOD p] ∧
    (Field51_as_Nat e1.Y * Field51_as_Nat e2.Z) ≡ (Field51_as_Nat e2.Y * Field51_as_Nat e1.Z) [MOD p]) ∧
  (e1.IsValid → e2.IsValid → (c = Choice.one ↔ e1.toPoint = e2.toPoint)) ⦄ := by ...
```

### ○ `compress`

```lean
theorem compress_spec (self : EdwardsPoint) (hX : ∀ i < 5, self.X[i]!.val < 2 ^ 54)
      (hY : ∀ i < 5, self.Y[i]!.val < 2 ^ 54) (hZ : ∀ i < 5, self.Z[i]!.val < 2 ^ 54)
      -- (hself : self.IsValid)
      :
    compress self ⦃ result => True ⦄ := by ...
```

### ✓ `is_small_order`

```lean
theorem is_small_order_spec (self : EdwardsPoint) (hself : self.IsValid) :
    is_small_order self ⦃ result =>
    (result ↔ h • self.toPoint = 0) ⦄ := by ...
```

### ✓ `is_torsion_free`

```lean
theorem is_torsion_free_spec (self : EdwardsPoint) (hself : self.IsValid) :
    is_torsion_free self ⦃ result =>
    (result ↔ L • self.toPoint = 0) ⦄ := by ...
```

### ○ `mul_base`

```lean
theorem mul_base_spec (scalar : scalar.Scalar) :
    mul_base scalar ⦃ res =>
    EdwardsPoint.IsValid res ∧
    res.toPoint = (U8x32_as_Nat scalar.bytes) • _root_.Edwards.basepoint ⦄ := by ...
```

### ✓ `mul_base_clamped`

```lean
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ (result : EdwardsPoint) =>
      EdwardsPoint.IsValid result ∧
      (∃ clamped_scalar,
      h ∣ U8x32_as_Nat clamped_scalar ∧
      U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
      2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
      result.toPoint = ((U8x32_as_Nat clamped_scalar) • _root_.Edwards.basepoint)) ⦄ := by ...
```

### ✓ `mul_by_cofactor`

```lean
theorem mul_by_cofactor_spec (self : EdwardsPoint) (hself : self.IsValid) :
    mul_by_cofactor self ⦃ result =>
    result.IsValid ∧
    result.toPoint = h • self.toPoint ⦄ := by ...
```

### ✓ `mul_clamped`

```lean
theorem mul_clamped_spec (self : EdwardsPoint) (bytes : Array U8 32#usize)
    (h_self_valid : self.IsValid) :
    mul_clamped self bytes ⦃ (result : EdwardsPoint) =>
      EdwardsPoint.IsValid result ∧
      (∃ clamped_scalar,
      h ∣ U8x32_as_Nat clamped_scalar ∧
      U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
      2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
      result.toPoint = (((U8x32_as_Nat clamped_scalar)) • self.toPoint)) ⦄ := by ...
```

### ○ `to_montgomery`

```lean
theorem to_montgomery_spec (e : EdwardsPoint)
    (h_Y_bounds : ∀ i < 5, e.Y[i]!.val < 2 ^ 53) (h_Z_bounds : ∀ i < 5, e.Z[i]!.val < 2 ^ 53) :
    to_montgomery e ⦃ mp =>
    (let Y := Field51_as_Nat e.Y
    let Z := Field51_as_Nat e.Z
    let u := U8x32_as_Nat mp
    if Z % p = Y % p then
      u % p = 0
    else
      (u * Z) % p = (u * Y + (Z + Y)) % p) ∧
    (∀ n : ℕ, fromEdwards (n • e.toPoint) = n • (MontgomeryPoint.mkPoint mp)) ⦄ := by ...
```

## `curve25519-dalek/src/edwards/affine.rs`

### ✓ `eq`

```lean
theorem eq_spec (self other : AffinePoint) (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    eq self other ⦃ result =>
    result = true ↔ self.toPoint = other.toPoint ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (q : AffinePoint) =>
      Field51_as_Nat q.x = 0 ∧ Field51_as_Nat q.y = 1 ∧
      q.IsValid ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : edwards.affine.AffinePoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : edwards.affine.AffinePoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec (self other : AffinePoint) :
  ct_eq self other ⦃ c =>
  (c = Choice.one ↔
    (Field51_as_Nat self.x) ≡ (Field51_as_Nat other.x) [MOD p] ∧
    (Field51_as_Nat self.y) ≡ (Field51_as_Nat other.y) [MOD p]) ∧
  (self.IsValid → other.IsValid → (c = Choice.one ↔ self.toPoint = other.toPoint)) ⦄ := by ...
```

### ○ `compress`

```lean
theorem compress_spec (self : AffinePoint) -- (hself : self.IsValid)
    (h : Field51_as_Nat self.y < 2 ^ 255) :
    compress self ⦃ result =>
    True -- result.IsValid ∧ result.toPoint = self.toPoint
     ⦄ := by ...
```

### ✓ `to_edwards`

```lean
theorem to_edwards_spec (self : AffinePoint) (hself : self.IsValid)
  (hx53 : ∀ i < 5, self.x[i]!.val < 2 ^ 53)
  (hy53 : ∀ i < 5, self.y[i]!.val < 2 ^ 53) :
    to_edwards self ⦃ result =>
      result.X = self.x ∧ result.Y = self.y ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T % p = (Field51_as_Nat self.x * Field51_as_Nat self.y) % p ∧
      (∀ i < 5, result.T[i]!.val < 2 ^ 52) ∧
      (∀ i < 5, result.Z[i]!.val < 2 ^ 53) ∧
      result.IsValid ⦄ := by ...
```

## `curve25519-dalek/src/field.rs`

### ✓ `ct_eq`

```lean
theorem ct_eq_spec (a b : backend.serial.u64.field.FieldElement51) :
    ct_eq a b ⦃ c =>
    (c = Choice.one ↔ a.to_bytes = b.to_bytes ) ⦄ := by ...
```

## `curve25519-dalek/src/montgomery.rs`

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (q : montgomery.ProjectivePoint) =>
      Field51_as_Nat q.U = 1 ∧
      Field51_as_Nat q.W = 0 ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (P : montgomery.MontgomeryPoint) (scalar : scalar.Scalar) :
    mul P scalar ⦃ res =>
      let m:= (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄ := by ...
```

### ○ `mul`

```lean
theorem mul_loop_spec
    (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 x1 : montgomery.ProjectivePoint)
    (scalar_bytes : Array U8 32#usize)
    (prev_bit : Bool)
    (i : Isize)
    (idx0W : Field51_as_Nat x0.W = 0)
    (idx1W : Field51_as_Nat x1.W = 1)
    (idx0U : Field51_as_Nat x0.U = 1)
    :
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i ⦃ res =>
    (res.2.2 =true →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
        +  2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
        + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.2.1.U.toField
      let w_out := res.2.1.W.toField
      let u_ord := u_out/w_out
      res.2.1.U.IsValid ∧
      res.2.1.W.IsValid ∧
      res.1.U.IsValid ∧
      res.1.W.IsValid ∧
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ∧
    (res.2.2 = false →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
      + 2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
      + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.1.U.toField
      let w_out := res.1.W.toField
      let u_ord := u_out/w_out
      res.2.1.U.IsValid ∧
      res.2.1.W.IsValid ∧
      res.1.U.IsValid ∧
      res.1.W.IsValid ∧
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ⦄
 := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (scalar : scalar.Scalar) (P : montgomery.MontgomeryPoint) :
    mul scalar P ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by ...
```

### ✓ `eq`

```lean
theorem eq_spec (u v : MontgomeryPoint) :
    eq u v ⦃ b =>
    (b = true ↔
      (U8x32_as_Nat u % 2 ^ 255) ≡ (U8x32_as_Nat v % 2 ^ 255) [MOD p]) ⦄ := by ...
```

### ✓ `mul_assign`

```lean
theorem mul_assign_spec (P : MontgomeryPoint) (scalar : scalar.Scalar) :
    mul_assign P scalar ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    spec identity (fun q =>
    (∀ i : Fin 32, q[i]! = 0#u8) ∧
    U8x32_as_Nat q = 0) := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : montgomery.MontgomeryPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ res =>
      ∀ i < 32,
        res[i]! = (if choice.val = 1#u8 then b[i]! else a[i]!) ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec (u v : MontgomeryPoint) :
    ct_eq u v ⦃ c =>
    (c = Choice.one ↔
      (U8x32_as_Nat u % 2 ^ 255) ≡ (U8x32_as_Nat v % 2 ^ 255) [MOD p]) ⦄ := by ...
```

### ✓ `as_bytes`

```lean
theorem as_bytes_spec (mp : montgomery.MontgomeryPoint) :
    montgomery.MontgomeryPoint.as_bytes mp ⦃ result =>
    result = mp ⦄ := by ...
```

### ✓ `mul_base`

```lean
theorem mul_base_spec (scalar : scalar.Scalar) :
    mul_base scalar ⦃ result =>
    Montgomery.MontgomeryPoint.mkPoint result = (U8x32_as_Nat scalar.bytes) • (fromEdwards _root_.Edwards.basepoint) ⦄
 := by ...
```

### ✓ `mul_base_clamped`

```lean
theorem mul_base_clamped_spec (bytes : Array U8 32#usize) :
    mul_base_clamped bytes ⦃ result =>
    (∃ clamped_scalar_nat,
    h ∣ clamped_scalar_nat ∧
    clamped_scalar_nat < 2 ^ 255 ∧
    2 ^ 254 ≤ clamped_scalar_nat ∧
     MontgomeryPoint.mkPoint result = clamped_scalar_nat • (fromEdwards _root_.Edwards.basepoint)) ⦄ := by ...
```

### ✓ `mul_clamped`

```lean
theorem mul_clamped_spec (P : MontgomeryPoint) (bytes : Array U8 32#usize) :
    mul_clamped P bytes ⦃ res =>
      (∃ clamped_scalar,
      h ∣ U8x32_as_Nat clamped_scalar ∧
      U8x32_as_Nat clamped_scalar < 2 ^ 255 ∧
      2 ^ 254 ≤ U8x32_as_Nat clamped_scalar ∧
      let m:= (U8x32_as_Nat clamped_scalar)
      MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P)) ⦄ := by ...
```

### ✓ `to_bytes`

```lean
theorem to_bytes_spec (mp : montgomery.MontgomeryPoint) :
    montgomery.MontgomeryPoint.to_bytes mp ⦃ result =>
    result = mp ⦄ := by ...
```

### ✓ `to_edwards`

```lean
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
      to_edwards mp sign ⦃ result =>
        (∀ ep, result = some ep →
          ∃ Z_inv,
            field.FieldElement51.invert ep.Z = ok Z_inv ∧
            let u := U8x32_as_Nat mp % 2^255
            let y := Field51_as_Nat ep.Y * Field51_as_Nat Z_inv % p
            (y * ((u + 1) % p)) % p = ((u + p - 1) % p) % p ∧ ep.IsValid )
      ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : montgomery.ProjectivePoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ res =>
      (∀ i < 5, res.U[i]! = (if choice.val = 1#u8 then b.U[i]! else a.U[i]!)) ∧
      (∀ i < 5, res.W[i]! = (if choice.val = 1#u8 then b.W[i]! else a.W[i]!)) ⦄ := by ...
```

### ✓ `as_affine`

```lean
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : self.U.IsValid)
    (hW : self.W.IsValid)
    (h_valid : self.W.toField ≠ 0) :
    as_affine self ⦃ res => (U8x32_as_Field res = self.U.toField  / self.W.toField) ∧
    (U8x32_as_Nat res < 2 ^255)  ⦄ := by ...
```

## `curve25519-dalek/src/ristretto.rs`

### ✓ `add`

```lean
theorem add_spec (self other : RistrettoPoint) (h_self_valid : self.IsValid) (h_other_valid : other.IsValid) :
    add self other ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint + other.toPoint ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (self : RistrettoPoint) (scalar : scalar.Scalar)
    (hscalar : U8x32_as_Nat scalar.bytes < 2 ^ 255) (hself : self.IsValid) :
    mul self scalar ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat scalar.bytes) • self.toPoint ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    sub self other ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = self.toPoint - other.toPoint ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (self : scalar.Scalar) (point : RistrettoPoint)
    (hself : U8x32_as_Nat self.bytes < 2 ^ 255) (hpoint : point.IsValid) :
    mul self point ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧ result.toPoint = (U8x32_as_Nat self.bytes) • point.toPoint ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (result : CompressedRistretto) =>
      ∀ i : Fin 32, result[i]! = 0#u8 ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec
    (self other : CompressedRistretto) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔ self = other ⦄ := by ...
```

### ✓ `as_bytes`

```lean
theorem as_bytes_spec (cr : CompressedRistretto) :
    as_bytes cr ⦃ b =>
    b = cr ⦄ := by ...
```

### ✓ `decompress`

```lean
theorem decompress_spec (comp : CompressedRistretto) :
    decompress comp ⦃ result =>
    (¬comp.IsValid → result = none) ∧
    (comp.IsValid →
        ∃ rist,
        result = some rist ∧
        RistrettoPoint.IsValid rist ∧
        decompress_pure comp = some rist.toPoint) ⦄ := by ...
```

### ✓ `from_slice`

```lean
theorem from_slice_spec
    (bytes : Slice U8) :
    from_slice bytes ⦃ (result : core.result.Result CompressedRistretto core.array.TryFromSliceError) =>
      (bytes.length = 32 → ∃ cr : CompressedRistretto, result = .Ok cr ∧ cr.val = bytes.val) ∧
      (bytes.length ≠ 32 → result = .Err ()) ⦄ := by ...
```

### ✓ `to_bytes`

```lean
theorem to_bytes_spec (cr : CompressedRistretto) :
    to_bytes cr ⦃ b =>
    b = cr ⦄ := by ...
```

### ✓ `eq`

```lean
theorem eq_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    eq self other ⦃ (result : Bool) =>
      (result = true ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p]) ⦄ := by ...
```

### ✓ `identity`

```lean
theorem identity_spec :
    identity ⦃ (result : RistrettoPoint) =>
      Field51_as_Nat result.X = 0 ∧
      Field51_as_Nat result.Y = 1 ∧
      Field51_as_Nat result.Z = 1 ∧
      Field51_as_Nat result.T = 0 ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : RistrettoPoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : RistrettoPoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec
    (self other : RistrettoPoint)
    (h_self_valid : self.IsValid)
    (h_other_valid : other.IsValid) :
    ct_eq self other ⦃ (result : subtle.Choice) =>
      result = Choice.one ↔
        (Field51_as_Nat self.X * Field51_as_Nat other.Y) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.X) [MOD p] ∨
        (Field51_as_Nat self.X * Field51_as_Nat other.X) ≡ (Field51_as_Nat self.Y * Field51_as_Nat other.Y) [MOD p] ⦄ := by ...
```

### ✓ `compress`

```lean
theorem compress_spec (self : RistrettoPoint) (h : self.IsValid) :
    compress self ⦃ (result : CompressedRistretto) =>
      result.IsValid ∧
      math.compress_pure self.toPoint = U8x32_as_Nat result ⦄ := by ...
```

### ✓ `from_uniform_bytes`

```lean
theorem from_uniform_bytes_spec (bytes : Array U8 64#usize) :
    from_uniform_bytes bytes ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint =
        (elligator_ristretto_flavor_pure (field_from_bytes (bytes_lower bytes))).val +
        (elligator_ristretto_flavor_pure (field_from_bytes (bytes_upper bytes))).val
      ⦄ := by ...
```

### ✓ `mul_base`

```lean
theorem mul_base_spec (s : scalar.Scalar) (h_s_canonical : U8x32_as_Nat s.bytes < 2 ^ 255) :
    mul_base s ⦃ (result : RistrettoPoint) =>
      result.IsValid ∧
      result.toPoint = (U8x32_as_Nat s.bytes) • _root_.Edwards.basepoint ⦄ := by ...
```

## `curve25519-dalek/src/scalar.rs`

### ✓ `add`

```lean
theorem add_spec (self _rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat _rhs.bytes < L) :
    add self _rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes + U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `mul`

```lean
theorem mul_spec (self _rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat _rhs.bytes < L) :
    mul self _rhs ⦃ (result : scalar.Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `neg`

```lean
theorem neg_spec (self : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L) :
    neg self ⦃ result =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat self.bytes ≡ 0 [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `sub`

```lean
theorem sub_spec (self rhs : scalar.Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat rhs.bytes < L) :
    sub self rhs ⦃ result =>
      U8x32_as_Nat result.bytes + U8x32_as_Nat rhs.bytes ≡
        U8x32_as_Nat self.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `eq`

```lean
theorem eq_spec (self other : scalar.Scalar) :
    eq self other ⦃ result =>
    result = true ↔ self.bytes = other.bytes ⦄ := by ...
```

### ✓ `from`

```lean
theorem from_spec (x : Std.U128) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by ...
```

### ✓ `from`

```lean
theorem from_spec (x : Std.U16) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by ...
```

### ✓ `from`

```lean
theorem from_spec (x : Std.U32) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by ...
```

### ✓ `from`

```lean
theorem from_spec (x : Std.U64) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by ...
```

### ✓ `from`

```lean
theorem from_spec (x : Std.U8) :
    «from» x ⦃ result =>
    U8x32_as_Nat result.bytes = x.val ⦄ := by ...
```

### ✓ `mul_assign`

```lean
theorem mul_assign_spec (self _rhs : Scalar)
    (h_self : U8x32_as_Nat self.bytes < L)
    (h_rhs : U8x32_as_Nat _rhs.bytes < L) :
    mul_assign self _rhs ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x32_as_Nat self.bytes * U8x32_as_Nat _rhs.bytes [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_spec
    (a b : scalar.Scalar)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : scalar.Scalar) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by ...
```

### ✓ `conditional_select`

```lean
theorem conditional_select_loop_spec
    (iter : core.ops.range.Range Usize) (a b : scalar.Scalar)
    (choice : subtle.Choice) (bytes : Array U8 32#usize)
    (hend : iter.end = 32#usize)
    (hstart : iter.start ≤ 32#usize)
    (hinv : ∀ j : Nat, j < iter.start.val →
      bytes[j]! = (if choice.val = 1#u8 then b else a).bytes[j]!) :
    conditional_select_loop iter a b choice bytes ⦃ result =>
      ∀ j : Nat, j < 32 →
        result[j]! = (if choice.val = 1#u8 then b else a).bytes[j]! ⦄ := by ...
```

### ✓ `ct_eq`

```lean
theorem ct_eq_spec (self other : scalar.Scalar) :
    ct_eq self other ⦃ (c : subtle.Choice) =>
      c = Choice.one ↔ self.bytes = other.bytes ⦄ := by ...
```

### ✓ `ONE`

```lean
theorem ONE_spec : U8x32_as_Nat ONE.bytes = 1 := by ...
```

### ✓ `ZERO`

```lean
theorem ZERO_spec : U8x32_as_Nat ZERO.bytes = 0 := by ...
```

### ✓ `as_bytes`

```lean
theorem as_bytes_spec (s : Scalar) :
    as_bytes s ⦃ b =>
    b = s.bytes ∧ mk b = s ⦄ := by ...
```

### ✓ `from_bytes_mod_order`

```lean
theorem from_bytes_mod_order_spec (b : Array U8 32#usize) :
    from_bytes_mod_order b ⦃ s =>
    U8x32_as_Nat s.bytes ≡ U8x32_as_Nat b [MOD L] ∧ U8x32_as_Nat s.bytes < L ⦄ := by ...
```

### ✓ `from_bytes_mod_order_wide`

```lean
theorem from_bytes_mod_order_wide_spec (input : Array U8 64#usize) :
    from_bytes_mod_order_wide input ⦃ (result : Scalar) =>
      U8x32_as_Nat result.bytes ≡ U8x64_as_Nat input [MOD L] ∧
      U8x32_as_Nat result.bytes < L ⦄ := by ...
```

### ✓ `from_canonical_bytes`

```lean
theorem from_canonical_bytes_spec (b : Array U8 32#usize) :
    from_canonical_bytes b ⦃ s =>
    (U8x32_as_Nat b < L → s.is_some = Choice.one ∧ s.value.bytes = b) ∧
    (L ≤ U8x32_as_Nat b → s.is_some = Choice.zero) ⦄ := by ...
```

### ✓ `invert`

```lean
theorem invert_spec (self : Scalar) (h : U8x32_as_Nat self.bytes % L ≠ 0) :
    invert self ⦃ (result : Scalar) =>
      U8x32_as_Nat self.bytes * U8x32_as_Nat result.bytes ≡ 1 [MOD L] ⦄ := by ...
```

### ✓ `to_bytes`

```lean
theorem to_bytes_spec (s : Scalar) :
    to_bytes s ⦃ a =>
    a = s.bytes ∧ mk a = s ⦄ := by ...
```

### ✓ `invert`

```lean
theorem invert_spec (self : Scalar52) (h : Scalar52_as_Nat self % L ≠ 0)
    (hu : ∀ i < 5, self[i]!.val < 2 ^ 52) :
    invert self ⦃ (result : Scalar52) =>
      (Scalar52_as_Nat self * Scalar52_as_Nat result) ≡ 1 [MOD L] ∧
      (∀ i < 5, result[i]!.val < 2 ^ 52) ∧ Scalar52_as_Nat result < L ⦄ := by ...
```

### ✓ `montgomery_invert`

```lean
theorem montgomery_invert_spec (u : Scalar52) (h : Scalar52_as_Nat u % L ≠ 0)
    (h_bounds : ∀ i < 5, u[i]!.val < 2 ^ 62)
    (h_value : Scalar52_as_Nat u * Scalar52_as_Nat u < R * L) :
    montgomery_invert u ⦃ u' =>
    (Scalar52_as_Nat u * Scalar52_as_Nat u') % L = (R * R) % L ∧
    (∀ i < 5, u'[i]!.val < 2 ^ 52) ∧
    Scalar52_as_Nat u' < L ⦄ := by ...
```

### ✓ `clamp_integer`

```lean
theorem clamp_integer_spec (bytes : Array U8 32#usize) :
    clamp_integer bytes ⦃ (result : Std.Array U8 32#usize) =>
      h ∣ U8x32_as_Nat result ∧
      U8x32_as_Nat result < 2^255 ∧
      2^254 ≤ U8x32_as_Nat result ⦄ := by ...
```
