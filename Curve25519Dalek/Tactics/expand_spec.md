# `expand_array` tactic -- desired behavior specification

## Purpose

`expand_array` produces per-index `.val`-level hypotheses for an Aeneas array
built through a chain of `.set` operations. It is designed for use after
`step*` in proofs about Aeneas-generated code, where arrays are built
incrementally (one `Array.update` per element) and scalar operations have
`_post` hypotheses describing their values.

The key use case is the `reduce` proof and similar multi-pass array
computations, where `step*` leaves a final array (e.g. `limbs10`) defined
through a chain of `.set` calls, with intermediate scalar values described by
`_post` hypotheses involving shifts, bitwise AND, and additions.

## Syntax

```
expand_array <name>          -- expand all indices
expand_array <name> <k>      -- expand only index k
```

## Input

- `<name>`: the name of a local variable of type `Aeneas.Std.Array alpha n`
  where `n` is a `Usize` literal. The variable must be the final result of a
  chain of `.set` operations visible through defining equalities in the local
  context, i.e. hypotheses of the form:
  ```
  hlimbs1 : limbs1 = limbs.set 0#usize v0
  hlimbs2 : limbs2 = limbs1.set 1#usize v1
  ...
  hlimbs10 : limbs10 = limbs9.set 4#usize v25
  ```

- `<k>` (optional): a natural number literal. When provided, only index `k`
  is expanded.

## Output

For each index `k` in `0 ..< n` (or just the single requested index), the
tactic introduces a hypothesis:

```
h<name><k> : (↑<name>)[k]!.val = <fully expanded formula>
```

For example, after `expand_array limbs10` (in the `reduce` proof with
`attribute [local simp_lists_safe] UScalar.val_and`):

```
hlimbs100 : ↑(↑limbs10)[0]! = (↑(↑limbs)[0]! &&& ↑mask) + ↑(↑limbs)[4]! >>> 51 * 19
hlimbs101 : ↑(↑limbs10)[1]! = (↑(↑limbs)[1]! &&& ↑mask) + ↑(↑limbs)[0]! >>> 51
hlimbs102 : ↑(↑limbs10)[2]! = (↑(↑limbs)[2]! &&& ↑mask) + ↑(↑limbs)[1]! >>> 51
hlimbs103 : ↑(↑limbs10)[3]! = (↑(↑limbs)[3]! &&& ↑mask) + ↑(↑limbs)[2]! >>> 51
hlimbs104 : ↑(↑limbs10)[4]! = (↑(↑limbs)[4]! &&& ↑mask) + ↑(↑limbs)[3]! >>> 51
```

where every reference is to the original input array `limbs` and all
intermediate arrays and scalars have been eliminated.

## What "fully expanded" means

The hypothesis for each index must be resolved through ALL of the following
layers:

### 1. `.set` chain resolution (CURRENTLY IMPLEMENTED)

The `.set` chain is inlined via `rw` using the defining equalities, then the
index comparisons (`getElem!_Nat_set_eq` / `getElem!_Nat_set_ne`) are resolved
via `simp (discharger := norm_num)`. After this step, each hypothesis has the
form:

```
h<name><k> : (↑<name>)[k]!.val = <intermediate scalar>.val
```

where `<intermediate scalar>` is a variable introduced by `step*` (e.g.
`a0`, `a2`).

### 2. `_post` hypothesis chaining (CURRENTLY IMPLEMENTED)

The current tactic applies `simp only [*]` to the generated hypotheses,
which chains through `_post` hypotheses. For example:

- `a0_post : a0.val = a0_base.val + carry_mult.val` gets substituted, and
- `a0_base_post : a0_base = (↑arr3)[0]!` introduces a `.val` coercion of
  an intermediate array read.

After this step, hypotheses look like:

```
harr60 : ↑(↑arr6)[0]! = ↑(((limbs.set 0#usize m0).set 1#usize m1).set 2#usize m2)[0]!
           + ↑(↑limbs)[2]! >>> 51 * 19
```

The scalar operations are fully resolved, but intermediate array reads
(like `(arr3)[0]!` expanded into the `.set` chain) remain.

### 3. `simp_lists` normalization (NOT YET IMPLEMENTED -- DESIRED)

After `_post` chaining, the hypotheses contain expressions like
`(((limbs.set 0#usize m0).set 1#usize m1).set 2#usize m2)[0]!`
which are nested `getElem!`/`set` combinations from intermediate arrays.
These must be resolved via `simp_lists`, which simplifies them to the
appropriate value (e.g. `m0` for index 0).

### 4. Second `_post` chaining pass (NOT YET IMPLEMENTED -- DESIRED)

After `simp_lists` resolves intermediate array reads to scalar names (e.g.
`m0`, `m1`), a second `simp only [*]` pass chains through the remaining
`_post` hypotheses for those scalars (e.g. `m0_post : m0.val = (i0 &&& mask).val`).

### 5. Final `simp_lists` pass (NOT YET IMPLEMENTED -- DESIRED)

A final `simp_lists` pass normalizes any remaining list-level indexing.
If `UScalar.val_and` is tagged `simp_lists_safe` locally, this pass also
distributes `.val` over `&&&` to produce the final natural-number form.

## What the tactic replaces

Currently, in the `reduce` proof, the user writes:

```lean
rw [UScalar.val_and] at *
expand_array limbs10
simp_lists at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104
simp only [*] at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104
simp_lists at hlimbs100 hlimbs101 hlimbs102 hlimbs103 hlimbs104
```

The desired behavior is that `expand_array limbs10` alone produces the same
fully expanded hypotheses, absorbing all five lines into one.

Note: the `rw [UScalar.val_and] at *` may be unnecessary if `UScalar.val_and`
is locally tagged `simp_lists_safe` (as it is in Reduce.lean), since the
`simp_lists` passes would then handle `.val` distribution automatically.

## Current behavior summary

The current implementation (in `ExpandArray.lean`) performs:

1. Introduces `h<name><k> : x[k]!.val = x[k]!.val` via `rfl`.
2. Rewrites the RHS using the `.set` chain equalities.
3. Resolves `getElem!`/`set` via `simp (discharger := norm_num)`.
4. Applies `simp only [*]` to chain through `_post` hypotheses.
5. Clears the defining equality for the target array.

Steps 1-5 work correctly for single-pass `.set` chains where no intermediate
array reads occur. For two-pass patterns (like `reduce`), step 4 introduces
intermediate array expressions that steps 1-3 cannot resolve.

## What needs to be added

After step 4 (existing `simp only [*]`), add:

- **`simp_lists` on generated hypotheses**: Resolves intermediate array reads
  like `(arr3.set ...)[0]!` to their scalar values.
- **Another `simp only [*]` pass**: Chains through scalar `_post` hypotheses
  for values revealed by `simp_lists`.
- **Final `simp_lists` pass**: Normalizes any remaining list-level indexing.

The implementation should iterate `simp_lists` and `simp only [*]` on the
generated hypotheses for a bounded number of rounds (2-3 rounds suffice for
all known use cases).

## Naming convention

- For `expand_array foo`, hypotheses are named `hfoo0`, `hfoo1`, ..., `hfoo(n-1)`.
- For `expand_array foo k`, only `hfook` is introduced.

## Performance requirements

- Must work in contexts with 40+ hypotheses from `step*` (the `reduce` proof
  has approximately 50 hypotheses after `step*`).
- The `.set` chain resolution (step 1) uses `norm_num` as a discharger for
  index comparisons, which is fast. This approach must be preserved.
- The `simp_lists` and `simp only [*]` passes should be scoped to only the
  generated hypotheses (`at harr60 harr61 ...`), NOT `at *`, to avoid
  touching unrelated context and to keep performance predictable.
- The tactic should complete within a reasonable heartbeat budget (no more
  than a few hundred thousand heartbeats for a 5-element array with a
  10-deep `.set` chain).

## Compatibility requirements

- **Aeneas step markers**: Expressions of the form `[> ... <]` must not be
  touched or simplified. The tactic should never apply `simp` or `rw` at `*`
  in a way that could affect these markers.
- **Unrelated hypotheses**: Hypotheses not part of the `.set` chain or
  `_post` chain must not be modified. The tactic operates only on the
  hypotheses it creates (`h<name><k>`).
- **Defining equality cleanup**: After expansion, the defining equality for
  the target array (e.g. `limbs10 = limbs9.set 4#usize i25`) should be
  cleared from the context, as it is fully absorbed into the per-index
  hypotheses. Intermediate chain equalities should also be cleared if safe.
- **`simp_lists_safe` attributes**: The tactic should respect locally
  declared `simp_lists_safe` attributes (e.g.
  `attribute [local simp_lists_safe] UScalar.val_and`). When
  `UScalar.val_and` is tagged `simp_lists_safe`, the `simp_lists` passes
  should automatically distribute `.val` over `&&&`.

## Two-pass patterns (carry propagation)

In `reduce`, the array is built in two passes over the same indices:

- **Pass 1** (mask): Sets indices 0-4 with masked values (`limbs[k] &&& mask`).
  Produces `limbs1` through `limbs5`.
- **Pass 2** (carry add): Sets indices 0-4 again with carry additions
  (`limbs5[k] + carry_k`). Produces `limbs6` through `limbs10`.

The final array `limbs10` has a 10-deep `.set` chain. The tactic must handle
this correctly: for each index, the `.set` resolution finds the LAST write
(from pass 2), whose value depends on a read from an intermediate array
(from pass 1), which in turn requires `simp_lists` to resolve through the
pass-1 `.set` chain.

## Test file

See `Curve25519Dalek/Tactics/ExpandArrayTest.lean` for self-contained tests
that exercise the current and desired behavior. The key tests are:

- **Test 1** (CurrentBehavior): Single-pass chain. Works with current tactic.
- **Test 2** (TwoPassCurrentGap): Two-pass chain showing the gap. Demonstrates
  the manual steps (`simp_lists`, `simp only [*]`, `simp_lists`) needed after
  the current `expand_array`.
- **Test 3** (TwoPassDesired): Same context, showing the desired one-call usage.
  Currently uses the manual workaround; should be updated when the tactic is
  improved.
- **Test 4** (Compatibility): Verifies unrelated hypotheses are untouched.
- **Test 5** (SingleIndex): Verifies single-index expansion works.
