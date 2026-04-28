# Plausible Testing Support — Implementation Plan

## Goal

Create `Curve25519Dalek/Plausible.lean`: a single file that provides `Plausible.Arbitrary`,
`Plausible.Shrinkable`, `Repr`, and a `WP.spec` `Decidable` instance for all types used in
the project, enabling property-based testing across spec files.

---

## Step 1 — Research Aeneas primitive type constructors

Before writing instances, inspect `.lake/packages/aeneas/backends/lean/` to confirm:

- The exact definition of `Std.U8`, `Std.U16`, `Std.U32`, `Std.U64`, `Std.USize`.
- Whether `⟨m⟩` (single-field constructor from `Nat`) works, or if a bounds proof is required.
- The definition of `Aeneas.Std.Array T n` and its `Array.make` / `Array.repeat` constructors.
- The definition of `WP.spec`, `theta`, and `wp_return` (needed for the `Decidable` proof).

---

## Step 2 — Create `Curve25519Dalek/Plausible.lean`

```lean
import Plausible
import Curve25519Dalek.Funs
open Plausible Arbitrary
open Aeneas Aeneas.Std Result
open curve25519_dalek
```

---

## Step 3 — Primitive type instances

Use `Gen.frequency` to bias toward edge cases (0, max, and random interior values).

```lean
instance : Arbitrary Std.U64 where
  arbitrary := do
    let m ← Gen.frequency (α := ℕ)
      (Gen.choose Nat 0 (2^64 - 1) (by omega))
      [(90, Gen.choose Nat 0 (2^64 - 1) (by omega)),
       (1,  pure 0),
       (1,  pure (2^64 - 1))]
    return ⟨m⟩   -- adjust if bounds proof is required (Step 1)
```

Repeat the same pattern for `Std.U8` (max `2^8 - 1`), `Std.U16`, `Std.U32`, `Std.USize`.

Add trivial `Shrinkable` instances as a first pass — proper numeric shrinking (halving toward 0)
is a planned follow-up:

```lean
instance : Shrinkable Std.U64 where shrink _ := []
-- repeat for U8, U16, U32, USize
```

---

## Step 4 — Generic `Aeneas.Std.Array T n` instance

```lean
instance {T : Type} {n : Usize} [Arbitrary T] [Inhabited T] :
    Arbitrary (Aeneas.Std.Array T n) where
  arbitrary := do
    let A ← List.ofFnM (n := n) fun _ ↦ arbitrary
    if h : A.length = n then
      return Array.make _ A h
    else
      return Array.repeat n default

instance {T : Type} {n : Usize} :
    Shrinkable (Aeneas.Std.Array T n) where
  shrink _ := []

instance {T : Type} {n : Usize} [Repr T] :
    Repr (Aeneas.Std.Array T n) where
  reprPrec A := reprPrec A.val
```

---

## Step 5 — Domain type instances

### Types that reduce to arrays

For `@[reducible]` aliases (or single-field structs) wrapping arrays, delegate to the array instance:

```lean
instance : Arbitrary field.FieldElement51 where
  arbitrary := do
    let inner ← arbitrary (α := Aeneas.Std.Array Std.U64 5#usize)
    return ⟨inner⟩

instance : Shrinkable field.FieldElement51 where shrink _ := []
instance : Repr field.FieldElement51 where reprPrec fe := reprPrec fe.val
```

Apply the same pattern to:

| Type | Inner type |
|------|------------|
| `backend.serial.u64.scalar.Scalar52` | `Array Std.U64 5#usize` |
| `scalar.Scalar` | `Array Std.U8 32#usize` |
| `montgomery.MontgomeryPoint` | `Array Std.U8 32#usize` |
| `edwards.CompressedEdwardsY` | `Array Std.U8 32#usize` |
| `ristretto.CompressedRistretto` | `Array Std.U8 32#usize` |

### Struct types composed of `FieldElement51` fields

For structures with multiple `FieldElement51` fields, generate each field independently:

```lean
instance : Arbitrary edwards.EdwardsPoint where
  arbitrary := return { X := ← arbitrary, Y := ← arbitrary,
                        Z := ← arbitrary, T := ← arbitrary }

instance : Arbitrary edwards.affine.AffinePoint where
  arbitrary := return { x := ← arbitrary, y := ← arbitrary }

instance : Arbitrary montgomery.ProjectivePoint where
  arbitrary := return { U := ← arbitrary, W := ← arbitrary }
```

Apply the same pattern to:

| Type | Fields |
|------|--------|
| `ristretto.RistrettoPoint` | wraps `EdwardsPoint` |
| `ProjectiveNielsPoint` | FE51 fields (Y_plus_X, Y_minus_X, Z, T2d) |
| `AffineNielsPoint` | FE51 fields (y_plus_x, y_minus_x, xy2d) |
| `CompletedPoint` | FE51 fields (X, Y, Z, T) |

Add `Shrinkable` (returning `[]`) and `Repr` for each.

---

## Step 6 — `WP.spec` Decidable instance

```lean
instance {α : Type*} (x : Result α) (p : Post α) [∀ x, Decidable (p x)] :
    Decidable (WP.spec x p) := by
  unfold WP.spec theta
  split
  · unfold wp_return; infer_instance
  · infer_instance
  · infer_instance
```

---

## Step 7 — Register in the main module

Add to `Curve25519Dalek.lean`:

```lean
import Curve25519Dalek.Plausible
```

The file is automatically covered by the existing `[[lean_lib]] name = "Curve25519Dalek"` target
in `lakefile.toml` — no lakefile changes needed.

---

## Step 8 — Smoke test

Add a small example at the bottom of `Curve25519Dalek/Plausible.lean` (or a dedicated
`Curve25519Dalek/PlausibleTest.lean`) to confirm the chain compiles end-to-end:

```lean
-- Confirm Arbitrary works for FieldElement51
#check (inferInstance : Arbitrary field.FieldElement51)

-- Confirm WP.spec is decidable for a simple post-condition
example : Decidable (WP.spec (Result.ret (0 : Std.U64)) (fun x => x = ⟨0⟩)) :=
  inferInstance
```

---

## Risks and notes

| Risk | Mitigation |
|------|------------|
| `Std.U64` constructor may require bounds proof | Check Aeneas source in Step 1; wrap with `⟨m, by omega⟩` if needed |
| `List.ofFnM` expects `n : ℕ`, but `Usize` may need coercion | Check coercion path; use `(n : ℕ)` explicitly if needed |
| `Gen.frequency` signature may differ from the issue snippet | Verify against installed Plausible version in `.lake/packages/plausible/` |
| Reducible aliases vs. structs with `.val` | Confirm with `#print` whether `⟨inner⟩` or `{ val := inner }` is correct |

## Follow-up (not in scope here)

- **Better `Shrinkable`**: Implement numeric shrinking for primitives (halve toward 0) and
  element-wise shrinking for arrays, using patterns from `Plausible/Sampleable.lean`.
- **Upstream to Aeneas**: Once clean and tested, open a PR to AeneasVerif/aeneas so these
  instances benefit all Aeneas users.
