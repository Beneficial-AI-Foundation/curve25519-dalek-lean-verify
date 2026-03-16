# TODO: Proving `to_bytes_spec` hlimb statements

## Current state

The bridge theorem `scalar52_eq_of_bitList_limbs` is proved. The 5 `hlimb` haves are still `sorry`'d.
The core difficulty is resolving `result[j]!` through the 32-deep `Array.set` chain left by `progress*`.

## Plan: byte-level experiment

### Step 1: Prove a single byte-level BitList statement

Pick the simplest case — e.g. `result[0]!` (byte 0, from `self[0] >>> 0` cast to U8):

```lean
have hbyte0 : ofU8 result[0]! ≈ₗ (ofU64 self[0]).take 8 := by ...
```

Understand what proof infrastructure is needed:
- **Resolving `result[0]!`**: After `progress*`, result is a 32-deep `Array.set` chain.
  Try: `simp only [Array.getElem!_Nat_eq, Array.set_val_eq]` then `simp_lists` to collapse the `List.set` chain.
  `simp_lists` uses `getElem!_set'` (tagged `@[simp_lists_simps↓]`, eager) to efficiently resolve `(l.set i x)[j]!`.
- **Connecting to the shift/cast**: After resolving `result[0]!`, we should get the concrete value
  `UScalar.cast .U8 (self[0] >>> 0)`. Then we need BitList specs:
  - `u64_shr_bitList_spec` exists in FromBytes.lean (gives `ofU64 (x >>> k) ≈ₗ (ofU64 x).drop k`)
    — but this is a `@[progress]` spec, not a rewrite lemma. May need a pure version.
  - Cast to U8: `UScalar.cast .U8` uses `bv.zeroExtend 8`, which is `% 2^8` on Nat.
    Need a BitList spec: `ofU8 (cast .U8 x) ≈ₗ (ofU64 x).take 8` or similar.
- **Alternatively**: Skip BitList entirely for the byte level and just use Nat arithmetic
  (`result[0]!.val = self[0].val % 2^8`), then show this implies the BitList equivalence.

### Step 2: Understand the proof chain

Once byte 0 works, check:
- Does the same approach work for simple shift bytes (bytes 1–5, 7–12, 13–18, 20–25, 26–31)?
- What extra is needed for shared bytes 6 and 19 (involve `|||` and `<<<`)?
- How expensive is `simp_lists` on the 32-deep chain? Does it need help (e.g. `subst_vars` first)?

### Step 3: Can 32 byte-level statements replace the 5 hlimb statements?

Investigate whether proving all 32 byte statements:
```lean
have hbyte0  : ofU8 result[0]!  ≈ₗ (ofU64 self[0]).take 8
have hbyte1  : ofU8 result[1]!  ≈ₗ ((ofU64 self[0]).drop 8).take 8
...
have hbyte31 : ofU8 result[31]! ≈ₗ ((ofU64 self[4]).drop 40).take 8
```

could feed directly into the bridge theorem (or a variant of it), bypassing the 5 hlimb
statements entirely. This might be cleaner since each byte statement is small and independent.

Alternatively, the 32 byte statements might make the 5 hlimb proofs trivial — each hlimb
is just concatenating the relevant byte statements.

### Key resources

- `simp_lists` tactic: `.lake/packages/aeneas/backends/lean/Aeneas/SimpLists/SimpLists.lean`
- `getElem!_set'`: `.lake/packages/aeneas/backends/lean/Aeneas/List/List.lean:280`
- `u64_shr_bitList_spec`: `Curve25519Dalek/Specs/Backend/Serial/U64/Field/FieldElement51/FromBytes.lean:173`
- `UScalar.cast`: `.lake/packages/aeneas/backends/lean/Aeneas/Std/Casts.lean:18` (`@[progress_pure_def]`)
- User suggestions to try: `subst_vars` early (before byte proofs), avoid `Nat.reducePow` in simp
