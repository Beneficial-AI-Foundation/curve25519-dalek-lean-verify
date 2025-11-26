# Tutorial on proving square_internal 

It is very difficult to one-shot a proof. 
A better strategy is to iteratively build up a proof based on feedback from lean.

Example:
```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    sorry
```

The first step is to unfold the definition, use progress*, and put in trace_state to see the goals.
This is a standard approach which will be helpful in the vast majority of cases.

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal
    progress*
    trace_state
    sorry
```


Result of running lake build (abridged to just the info box):
```
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:34:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
⊢ ∃ result,
    (do
          let i ← Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index a 0#usize
          let i1 ← i * 2#u64
          let i2 ← Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index a 1#usize
          let i3 ← i2 * 2#u64
          let i4 ← Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index a 2#usize
          let i5 ← i4 * 2#u64
          let i6 ← Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index a 3#usize
          let i7 ← i6 * 2#u64
          let i8 ← m i i
          let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize
          let i10 ← m i9 i2
          let i11 ← m i9 i4
          let i12 ← m i2 i2
          let i13 ← i11 + i12
          let i14 ← m i9 i6
          let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize
          let i16 ← m i15 i4
          let i17 ← i14 + i16
          let i18 ← Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index a 4#usize
          let i19 ← m i9 i18
          let i20 ← m i15 i6
          let i21 ← i19 + i20
          let i22 ← m i4 i4
          let i23 ← i21 + i22
          let i24 ← m i15 i18
          let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize
          let i26 ← m i25 i6
          let i27 ← i24 + i26
          let i28 ← m i25 i18
          let i29 ← m i6 i6
          let i30 ← i28 + i29
          let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize
          let i32 ← m i31 i18
          let i33 ← m i18 i18
          ok (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4)) =
        ok result ∧
      Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a
```

`progress*` was supposed to split the do monad into many ordinary lean goals, but it didn't work.
`Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index` 
looks like something defined in this repo 
(since it's a curve-dalek specific name, and looks machine-generated). 
Let's unfold it too before running progress:

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    trace_state
    sorry
```

Result:
```
✖ [7594/7596] Building Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
trace: .> LEAN_PATH=/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/Cli/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/batteries/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/Qq/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/aesop/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/proofwidgets/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/importGraph/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/LeanSearchClient/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/plausible/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/mathlib/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/packages/aeneas/backends/lean/.lake/build/lib/lean:/home/theo/projects/curve25519-dalek-lean-verify/.lake/build/lib/lean /home/theo/.elan/toolchains/leanprover--lean4---v4.24.0/bin/lean /home/theo/projects/curve25519-dalek-lean-verify/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean -o /home/theo/projects/curve25519-dalek-lean-verify/.lake/build/lib/lean/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.olean -i /home/theo/projects/curve25519-dalek-lean-verify/.lake/build/lib/lean/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.ilean -c /home/theo/projects/curve25519-dalek-lean-verify/.lake/build/ir/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.c --setup /home/theo/projects/curve25519-dalek-lean-verify/.lake/build/ir/Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.setup.json --json
error: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:31:75: unsolved goals
case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
⊢ ↑i2 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝² : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
⊢ ↑i4 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
⊢ ↑i6 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
⊢ ↑i11 + ↑i12 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
⊢ ↑i14 + ↑i16 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁸ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁷ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁶ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁵ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁴ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹³ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹² : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹¹ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁰ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁸ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁷ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁶ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁵ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁴ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝³ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝² : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
⊢ ↑i19 + ↑i20 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁰ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁹ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁸ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁷ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁶ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁵ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁴ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝³ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝² : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
⊢ ↑i21 + ↑i22 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁰ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁹ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁸ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝⁷ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁶ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁵ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁴ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝³ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝² : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝¹ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
⊢ ↑i24 + ↑i26 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁸ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁷ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²⁶ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁵ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁴ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²³ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²² : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²¹ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁰ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁹ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁸ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁷ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹⁶ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁵ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁴ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹³ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹² : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹¹ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁰ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁹ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁸ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁷ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝⁶ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁵ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁴ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝³ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝² : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝¹ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
⊢ ↑i28 + ↑i29 ≤ U128.max

a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:34:4: case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
⊢ ↑i2 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝² : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
⊢ ↑i4 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
⊢ ↑i6 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
⊢ ↑i11 + ↑i12 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
⊢ ↑i14 + ↑i16 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁸ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁷ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁶ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁵ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁴ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹³ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹² : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹¹ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁰ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁸ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁷ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁶ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁵ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁴ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝³ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝² : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
⊢ ↑i19 + ↑i20 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁰ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁹ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁸ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁷ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁶ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁵ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁴ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝³ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝² : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
⊢ ↑i21 + ↑i22 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁰ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁹ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁸ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝⁷ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁶ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁵ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁴ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝³ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝² : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝¹ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
⊢ ↑i24 + ↑i26 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁸ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁷ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²⁶ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁵ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁴ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²³ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²² : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²¹ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁰ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁹ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁸ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁷ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹⁶ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁵ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁴ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹³ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹² : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹¹ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁰ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁹ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁸ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁷ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝⁶ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁵ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁴ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝³ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝² : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝¹ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
⊢ ↑i28 + ↑i29 ≤ U128.max

a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
error: Lean exited with code 1
Some required targets logged failures:
- Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
error: build failed
```

This is a little hard to read. But this is a step forward: 
progress* has converted the one monad goal into many non-monad goals, and `sorry` is only
handling one of the goals.

Let's temporarily cheat at all the goals:
```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    trace_state
    all_goals try sorry
```
Of course the final answer can't use sorry, but this makes trace_state give a better output:

```
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:34:4: case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
⊢ ↑i2 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝² : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
⊢ ↑i4 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
⊢ ↑i6 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
⊢ ↑i11 + ↑i12 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
⊢ ↑i14 + ↑i16 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁸ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁷ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁶ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁵ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁴ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹³ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹² : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹¹ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁰ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁸ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁷ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁶ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁵ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁴ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝³ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝² : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
⊢ ↑i19 + ↑i20 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁰ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁹ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁸ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁷ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁶ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁵ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁴ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝³ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝² : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
⊢ ↑i21 + ↑i22 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁰ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁹ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁸ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝⁷ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁶ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁵ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁴ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝³ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝² : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝¹ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
⊢ ↑i24 + ↑i26 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁸ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁷ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²⁶ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁵ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁴ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²³ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²² : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²¹ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁰ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁹ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁸ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁷ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹⁶ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁵ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁴ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹³ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹² : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹¹ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁰ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁹ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁸ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁷ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝⁶ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁵ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁴ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝³ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝² : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝¹ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
⊢ ↑i28 + ↑i29 ≤ U128.max

a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:29:8: declaration uses 'sorry'
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:34:4: The following tactic starts with 11 goals and ends with 11 goals, 11 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").

Note: This linter can be disabled with `set_option linter.style.multiGoal false`
```

Aha, now we know that there are 11 goals.
A lot of these goals are simple, and a tactic that works for one will work for many.

The first goal is:
```
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max
```

This involves a comparison between machine types, which suggests `scalar_tac` 
(a custom aeneas tactic for machine types).

Note how we keep the trace_state just before the sorry so it's useful:

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try scalar_tac
    trace_state
    all_goals try sorry
```

```
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
⊢ ↑i2 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝² : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
⊢ ↑i4 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
⊢ ↑i6 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
⊢ ↑i11 + ↑i12 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
⊢ ↑i14 + ↑i16 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁸ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁷ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁶ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁵ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁴ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹³ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹² : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹¹ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁰ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁸ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁷ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁶ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁵ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁴ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝³ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝² : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
⊢ ↑i19 + ↑i20 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁰ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁹ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁸ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁷ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁶ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁵ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁴ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝³ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝² : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
⊢ ↑i21 + ↑i22 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁰ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁹ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁸ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝⁷ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁶ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁵ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁴ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝³ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝² : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝¹ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
⊢ ↑i24 + ↑i26 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁸ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁷ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²⁶ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁵ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁴ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²³ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²² : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²¹ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁰ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁹ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁸ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁷ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹⁶ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁵ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁴ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹³ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹² : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹¹ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁰ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁹ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁸ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁷ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝⁶ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁵ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁴ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝³ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝² : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝¹ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
⊢ ↑i28 + ↑i29 ≤ U128.max

a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:29:8: declaration uses 'sorry'
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: The following tactic starts with 11 goals and ends with 11 goals, 11 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").
```

This didn't work for any goals. Looking more closely at the first goal:
```
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max
```
We need to substitute in that definition, and then apply scalar_tac:
```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; scalar_tac
    trace_state
    all_goals try sorry
```

Again we're not getting anywhere:
```
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
⊢ ↑i * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
⊢ ↑i2 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝² : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
⊢ ↑i4 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
⊢ ↑i6 * ↑2#u64 ≤ U64.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
⊢ ↑i11 + ↑i12 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
⊢ ↑i14 + ↑i16 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝¹⁹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝¹⁸ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁷ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁶ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁵ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁴ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹³ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹² : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹¹ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁰ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝⁹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝⁸ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁷ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁶ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁵ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁴ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝³ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝² : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
⊢ ↑i19 + ↑i20 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²¹ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁰ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝¹⁹ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝¹⁸ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝¹⁷ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝¹⁶ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁵ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁴ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹³ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹² : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹¹ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁰ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝⁹ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝⁸ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝⁷ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝⁶ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁵ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁴ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝³ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝² : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
⊢ ↑i21 + ↑i22 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁵ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁴ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²³ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²² : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²¹ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁰ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝¹⁹ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝¹⁸ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝¹⁷ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁶ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁵ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁴ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹³ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹² : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹¹ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁰ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝⁹ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝⁸ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝⁷ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁶ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁵ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁴ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝³ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝² : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝¹ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
⊢ ↑i24 + ↑i26 ≤ U128.max

case hmax
a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝²⁸ : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝²⁷ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝²⁶ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁵ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁴ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²³ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²² : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²¹ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁰ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝¹⁹ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝¹⁸ : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝¹⁷ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝¹⁶ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁵ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁴ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹³ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹² : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹¹ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁰ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝⁹ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝⁸ : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝⁷ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝⁶ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁵ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁴ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝³ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝² : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝¹ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
⊢ ↑i28 + ↑i29 ≤ U128.max

a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:29:8: declaration uses 'sorry'
warning: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: The following tactic starts with 11 goals and ends with 11 goals, 11 of which are not operated on.
  trace_state
Please focus on the current goal, for instance using `·` (typed as "\.").
```

We know the first goal is true because of `ha : ∀ i < 5, ↑a[i]! < 2 ^ 62`. 
But aeneas is bad at automatically changing this forall into a[0] < 2 ^ 62.
Fortunately we have a tactic that does that:

```
/--
Expand a universal quantifier hypothesis `h : ∀ i < n, P i` into individual hypotheses
`h_0 : P 0`, `h_1 : P 1`, ..., `h_{n-1} : P (n-1)`.

Usage: `expand h with 5` creates hypotheses `h_0`, `h_1`, `h_2`, `h_3`, `h_4`.

The bound `n` must be provided explicitly. Each hypothesis is proven using `omega`.

Example:

h : ∀ i < 5, a[i]! < 100
expand h with 5
-- Now have h_0 : a[0]! < 100, h_1 : a[1]! < 100, ..., h_4 : a[4]! < 100

-/
elab "expand " h:ident " with " n:num : tactic => do
  let n := n.getNat
  for i in [:n] do
    let newName := h.getId.appendAfter s!"_{i}"
    evalTactic (← `(tactic| have $(mkIdent newName) := $h $(quote i) (by omega)))
```

So we try this:
```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    trace_state
    all_goals try sorry
```

Success---now only one goal remains:
```
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
```

This goal will be more work; it's not just an easy bounds check. If we can automate, we should,
so let's try `grind`. Note I've taken out `all_goals try sorry` because we're down
to one goal, so no need for goal counting.

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    trace_state
    grind
```

```
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.getElem_of_getElem? ↦ 90
    [thm] getElem?_neg ↦ 10
    [thm] getElem?_pos ↦ 10
    [thm] List.getElem?_eq_none ↦ 10
    [thm] getElem!_neg ↦ 9
    [thm] getElem!_pos ↦ 9
    [thm] List.getElem!_eq_getElem?_getD ↦ 9
    [thm] Option.getD_some ↦ 9
    [thm] GetElem?.match_1.congr_eq_1 ↦ 5
    [thm] GetElem?.match_1.congr_eq_2 ↦ 1
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:35:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ Scalar52_wide_as_Nat (Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4) =
    Scalar52_as_Nat a * Scalar52_as_Nat a
error: Lean exited with code 1
Some required targets logged failures:
- Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
error: build failed
```


`grind` fails. Let's leave it in because eventually we'll make the goal easy enough for it.
Let's get rid of `Scalar52_wide_as_Nat` and `Scalar52_as_Nat` (custom definitions in Defs.lean.
If you didn't know this, you'd use `rg` to find where they're defined).
Since we're using simp, for good measure we'll also try any hypothesis from the goal:

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, *]
    trace_state
    grind
```

Again `grind` fails:
```
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.getElem_of_getElem? ↦ 90
    [thm] getElem?_neg ↦ 10
    [thm] getElem?_pos ↦ 10
    [thm] List.getElem?_eq_none ↦ 10
    [thm] getElem!_neg ↦ 9
    [thm] getElem!_pos ↦ 9
    [thm] List.getElem!_eq_getElem?_getD ↦ 9
    [thm] Option.getD_some ↦ 9
    [thm] GetElem?.match_1.congr_eq_1 ↦ 5
    [thm] GetElem?.match_1.congr_eq_2 ↦ 1
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:36:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ ∑ x ∈ Finset.range 9,
      2 ^ (52 * x) *
        ↑((↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] squ
are_internal._proof_4))[x]?.getD
            default) =
    (∑ x ∈ Finset.range 5, 2 ^ (52 * x) * ↑((↑a)[x]?.getD default)) *
      ∑ x ∈ Finset.range 5, 2 ^ (52 * x) * ↑((↑a)[x]?.getD default)
error: Lean exited with code 1
```

`grind` would likely be happier if it had an expanded expression to work with, not ∑.
So we'll toss in Finset.sum_range_succ 

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, *, Finset.sum_range_succ]
    trace_state
    grind
```

Another failure, but at least the expression is expanded now:
```
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.getElem_of_getElem? ↦ 90
    [thm] getElem?_neg ↦ 10
    [thm] getElem?_pos ↦ 10
    [thm] List.getElem?_eq_none ↦ 10
    [thm] getElem!_neg ↦ 9
    [thm] getElem!_pos ↦ 9
    [thm] List.getElem!_eq_getElem?_getD ↦ 9
    [thm] Option.getD_some ↦ 9
    [thm] GetElem?.match_1.congr_eq_1 ↦ 5
    [thm] GetElem?.match_1.congr_eq_2 ↦ 1
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:36:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[0] +
                    2 ^ 52 *
                      ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33]
                              square_internal._proof_4))[1] +
                  2 ^ 104 *
                    ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[2] +
                2 ^ 156 *
                  ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[3] +
              2 ^ 208 *
                ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[4] +
            2 ^ 260 *
              ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[5] +
          2 ^ 312 * ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[6] +
        2 ^ 364 * ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[7] +
      2 ^ 416 * ↑(↑(Array.make 9#usize [i8, i10, i13, i17, i23, i27, i30, i32, i33] square_internal._proof_4))[8] =
    (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4]) *
      (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4])
error: Lean exited with code 1
```

What if `grind` can't handle `Array.make`? Let's unfold it

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, *, Finset.sum_range_succ]
    unfold Array.make
    trace_state
    grind
```

Doesn't work:
```
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.getElem_of_getElem? ↦ 90
    [thm] List.getElem_cons ↦ 44
    [thm] List.getElem_cons_succ ↦ 36
    [thm] getElem?_neg ↦ 10
    [thm] getElem?_pos ↦ 10
    [thm] List.getElem?_eq_none ↦ 10
    [thm] getElem!_neg ↦ 9
    [thm] getElem!_pos ↦ 9
    [thm] List.getElem!_eq_getElem?_getD ↦ 9
    [thm] Option.getD_some ↦ 9
    [thm] List.getElem_cons_zero ↦ 8
    [thm] List.length_cons ↦ 8
    [thm] GetElem?.match_1.congr_eq_1 ↦ 5
    [thm] GetElem?.match_1.congr_eq_2 ↦ 1
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:37:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 0#usize <]
i9_post : i9 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 1#usize <]
i15_post : i15 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 2#usize <]
i25_post : i25 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← (Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2).index_usize 3#usize <]
i31_post : i31 = (↑(Array.make 4#usize [i1, i3, i5, i7] square_internal._proof_2))[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[0] +
                    2 ^ 52 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[1] +
                  2 ^ 104 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[2] +
                2 ^ 156 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[3] +
              2 ^ 208 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[4] +
            2 ^ 260 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[5] +
          2 ^ 312 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[6] +
        2 ^ 364 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[7] +
      2 ^ 416 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[8] =
    (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4]) *
      (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4])
error: Lean exited with code 1
```

One notable thing is that there still are some `Array.make`s in the hypotheses. 
Maybe `grind` can only use those hypotheses if they don't have `Array.make`?

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, *, Finset.sum_range_succ]
    unfold Array.make at *
    trace_state
    grind
```

Again a failure:
```
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] List.getElem_cons_succ ↦ 2783
    [thm] List.getElem_of_getElem? ↦ 1868
    [thm] List.getElem_cons ↦ 684
    [thm] List.getElem_cons_zero ↦ 180
    [thm] List.length_cons ↦ 138
    [thm] Option.getD_some ↦ 117
    [thm] GetElem?.match_1.congr_eq_1 ↦ 71
    [thm] List.length_nil ↦ 43
    [thm] Option.getD_none ↦ 20
    [thm] getElem?_neg ↦ 16
    [thm] getElem?_pos ↦ 16
    [thm] List.getElem?_eq_none ↦ 16
    [thm] List.getElem?_cons ↦ 10
    [thm] getElem!_neg ↦ 9
    [thm] getElem!_pos ↦ 9
    [thm] List.getElem!_eq_getElem?_getD ↦ 9
    [thm] List.getElem?_singleton ↦ 1
    [thm] GetElem?.match_1.congr_eq_2 ↦ 1
info: Curve25519Dalek/Specs/Backend/Serial/U64/Scalar/Scalar52/SquareInternal.lean:37:4: a : Aeneas.Std.Array U64 5#usize
ha : ∀ i < 5, ↑a[i]! < 2 ^ 62
i : U64
_✝³² : [> let i ← a.index_usize 0#usize <]
i_post : i = (↑a)[0]!
i1 : U64
_✝³¹ : [> let i1 ← i * 2#u64 <]
i1_post : ↑i1 = ↑i * 2
i2 : U64
_✝³⁰ : [> let i2 ← a.index_usize 1#usize <]
i2_post : i2 = (↑a)[1]!
i3 : U64
_✝²⁹ : [> let i3 ← i2 * 2#u64 <]
i3_post : ↑i3 = ↑i2 * 2
i4 : U64
_✝²⁸ : [> let i4 ← a.index_usize 2#usize <]
i4_post : i4 = (↑a)[2]!
i5 : U64
_✝²⁷ : [> let i5 ← i4 * 2#u64 <]
i5_post : ↑i5 = ↑i4 * 2
i6 : U64
_✝²⁶ : [> let i6 ← a.index_usize 3#usize <]
i6_post : i6 = (↑a)[3]!
i7 : U64
_✝²⁵ : [> let i7 ← i6 * 2#u64 <]
i7_post : ↑i7 = ↑i6 * 2
i8 : U128
_✝²⁴ : [> let i8 ← m i i <]
i8_post : ↑i8 = ↑i * ↑i
i9 : U64
_✝²³ : [> let i9 ← Array.index_usize ⟨[i1, i3, i5, i7], square_internal._proof_2⟩ 0#usize <]
i9_post : i9 = (↑⟨[i1, i3, i5, i7], square_internal._proof_2⟩)[0]!
i10 : U128
_✝²² : [> let i10 ← m i9 i2 <]
i10_post : ↑i10 = ↑i9 * ↑i2
i11 : U128
_✝²¹ : [> let i11 ← m i9 i4 <]
i11_post : ↑i11 = ↑i9 * ↑i4
i12 : U128
_✝²⁰ : [> let i12 ← m i2 i2 <]
i12_post : ↑i12 = ↑i2 * ↑i2
i13 : U128
_✝¹⁹ : [> let i13 ← i11 + i12 <]
i13_post : ↑i13 = ↑i11 + ↑i12
i14 : U128
_✝¹⁸ : [> let i14 ← m i9 i6 <]
i14_post : ↑i14 = ↑i9 * ↑i6
i15 : U64
_✝¹⁷ : [> let i15 ← Array.index_usize ⟨[i1, i3, i5, i7], square_internal._proof_2⟩ 1#usize <]
i15_post : i15 = (↑⟨[i1, i3, i5, i7], square_internal._proof_2⟩)[1]!
i16 : U128
_✝¹⁶ : [> let i16 ← m i15 i4 <]
i16_post : ↑i16 = ↑i15 * ↑i4
i17 : U128
_✝¹⁵ : [> let i17 ← i14 + i16 <]
i17_post : ↑i17 = ↑i14 + ↑i16
i18 : U64
_✝¹⁴ : [> let i18 ← a.index_usize 4#usize <]
i18_post : i18 = (↑a)[4]!
i19 : U128
_✝¹³ : [> let i19 ← m i9 i18 <]
i19_post : ↑i19 = ↑i9 * ↑i18
i20 : U128
_✝¹² : [> let i20 ← m i15 i6 <]
i20_post : ↑i20 = ↑i15 * ↑i6
i21 : U128
_✝¹¹ : [> let i21 ← i19 + i20 <]
i21_post : ↑i21 = ↑i19 + ↑i20
i22 : U128
_✝¹⁰ : [> let i22 ← m i4 i4 <]
i22_post : ↑i22 = ↑i4 * ↑i4
i23 : U128
_✝⁹ : [> let i23 ← i21 + i22 <]
i23_post : ↑i23 = ↑i21 + ↑i22
i24 : U128
_✝⁸ : [> let i24 ← m i15 i18 <]
i24_post : ↑i24 = ↑i15 * ↑i18
i25 : U64
_✝⁷ : [> let i25 ← Array.index_usize ⟨[i1, i3, i5, i7], square_internal._proof_2⟩ 2#usize <]
i25_post : i25 = (↑⟨[i1, i3, i5, i7], square_internal._proof_2⟩)[2]!
i26 : U128
_✝⁶ : [> let i26 ← m i25 i6 <]
i26_post : ↑i26 = ↑i25 * ↑i6
i27 : U128
_✝⁵ : [> let i27 ← i24 + i26 <]
i27_post : ↑i27 = ↑i24 + ↑i26
i28 : U128
_✝⁴ : [> let i28 ← m i25 i18 <]
i28_post : ↑i28 = ↑i25 * ↑i18
i29 : U128
_✝³ : [> let i29 ← m i6 i6 <]
i29_post : ↑i29 = ↑i6 * ↑i6
i30 : U128
_✝² : [> let i30 ← i28 + i29 <]
i30_post : ↑i30 = ↑i28 + ↑i29
i31 : U64
_✝¹ : [> let i31 ← Array.index_usize ⟨[i1, i3, i5, i7], square_internal._proof_2⟩ 3#usize <]
i31_post : i31 = (↑⟨[i1, i3, i5, i7], square_internal._proof_2⟩)[3]!
i32 : U128
_✝ : [> let i32 ← m i31 i18 <]
i32_post : ↑i32 = ↑i31 * ↑i18
i33 : U128
_ : [> let i33 ← m i18 i18 <]
i33_post : ↑i33 = ↑i18 * ↑i18
⊢ ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[0] +
                    2 ^ 52 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[1] +
                  2 ^ 104 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[2] +
                2 ^ 156 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[3] +
              2 ^ 208 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[4] +
            2 ^ 260 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[5] +
          2 ^ 312 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[6] +
        2 ^ 364 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[7] +
      2 ^ 416 * ↑(↑⟨[i8, i10, i13, i17, i23, i27, i30, i32, i33], square_internal._proof_4⟩)[8] =
    (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4]) *
      (↑(↑a)[0] + 2 ^ 52 * ↑(↑a)[1] + 2 ^ 104 * ↑(↑a)[2] + 2 ^ 156 * ↑(↑a)[3] + 2 ^ 208 * ↑(↑a)[4])
error: Lean exited with code 1
```

We did just unfold, so maybe things have changed. Let's toss in another `simp [*]` 
after the unfold in case it can make a little more progress:

```
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    ∃ result, square_internal a = ok (result) ∧
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a := by
    unfold square_internal Indexcurve25519_dalekbackendserialu64scalarScalar52UsizeU64.index
    progress*
    all_goals try subst_vars; expand ha with 5; scalar_tac
    simp [Scalar52_wide_as_Nat, Scalar52_as_Nat, *, Finset.sum_range_succ]
    unfold Array.make at *
    simp [*]
    trace_state
    grind
```

And that works:
```
Build completed successfully (7596 jobs).
```

No need to clean up the proof. Because of time constraints, submit it now.
