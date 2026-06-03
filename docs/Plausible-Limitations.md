# Limitations of Plausible for Random Data Generation

This note documents where Plausible's random-data generation falls short for the
specifications in `Curve25519Dalek/Specs`, and which limitations our
`Decidable` instances do or do not address.

## Background: guards vs. sampling

Plausible can treat a hypothesis in two ways:

- **As a generated value to *sample*.** It draws random inputs and hopes they
  satisfy the hypothesis. For a hypothesis like `∀ i < 5, a[i]!.val < 2^53`,
  blind sampling of `a : Array U64 5` almost never produces an array all of
  whose limbs are below `2^53`, so essentially every sample is discarded and the
  property is never meaningfully exercised.
- **As a *guard* to *decide*.** If the hypothesis is `Decidable`, Plausible uses
  `decGuardTestable` to *check* it on each candidate rather than trying to
  generate inputs satisfying it. This collapses an astronomically unlikely
  sampling event into a cheap boolean test.

The three `Decidable` instances we ship (the `NamedBinder` bridge, the bounded-
hypothesis body instance, and the plain `∀ i < n, P i` instance) exist to push
bounded quantifiers onto the guard path. They work, but only for a specific
syntactic and type shape. The limitations below are the cases that fall outside
that shape, or that no instance can rescue.

## What the instances cover

The guard path fires only when **all** of these hold:

- the index type is `Nat` (not `Fin`, `USize`, `Int`);
- the **leading** guard after the binder is a strict `i < n` (`LT.lt` on `Nat`),
  with `n` any `Nat` term (it need not be a literal);
- the body is `DecidablePred`;
- the quantifier is **universal**.

The crucial subtlety is *leading* guard: instance 2 matches
`∀ i, NamedBinder s (i < n → Q i)`, so `i < n` must be the head of the
implication. Everything else must live inside the decidable body `Q i`.

For the dominant pattern — `∀ i < n, <decidable body on Nat>` with a small
literal `n` (e.g. `n ∈ {5, 8, 32, 64}`) — this is complete and cost-optimal:
`decide` enumerates exactly the `n` relevant indices via `Fin n`.

## Cases that are fine (common false alarms)

- **`≤` in the body, or as a *later* guard.** `∀ i, i < 5 → … ≤ 2^52 - 1`
  (`Field/FieldElement51/PowP58.lean:43`) and
  `∀ j < 5, i.val ≤ j → …` (`Backend/Serial/U64/Field/FieldElement51/Square2.lean:33`)
  are **covered**: the leading guard is `<`, and the trailing `≤` is just part of
  a decidable `Q`.
- **`Fin`-typed quantifiers** (`Montgomery/MontgomeryPoint/Identity.lean:31`,
  `Window/LookupTable/From.lean:82`, `Backend/Serial/U64/Constants/EightTorsion.lean:42`)
  are decided by Mathlib's `Fintype.decidableForallFintype` on a separate
  synthesis path — **no custom instance needed** — provided the body is
  `DecidablePred` *and computable*. See [Fin-typed quantifiers](#fin-typed-quantifiers)
  below; the decidability of the body, not the `Fin` quantifier, is what decides
  whether Plausible is useful.
- **Nested / independent `∀ i < n, ∀ j < m, …`** (including `∀ j < i`). Synthesis
  recurses: the inner quantifier becomes the outer's `DecidablePred` body. This
  works *provided Plausible wraps each level in the expected
  `NamedBinder (· < · → ·)` shape*.

## Genuine limitations

### 1. Lower bound precedes the upper bound (occurs in our specs)

`Scalar/Scalar/AsRadix16.lean:176` — `∀ j, 2*(i+1) ≤ j → j < 64 → …`
and `Scalar/Scalar/BatchInvert.lean:188` — `∀ j, i ≤ j → j < n → …`.

The **leading** guard is `≤` (a lower bound); the `<` upper bound is the second,
nested guard. The instances require `i < n` first, so they do not fire — and
with no finite bound at the head, `∀ j : ℕ, …` ranges over an infinite domain
and is not decidable as written.

Fixable with a dedicated instance:

```lean
instance {lo hi : Nat} {Q : Nat → Prop} [DecidablePred Q] {s : String} :
    Decidable (∀ j : Nat, Plausible.NamedBinder s (lo ≤ j → j < hi → Q j)) :=
  decidable_of_iff (∀ j : Fin hi, lo ≤ j.val → Q j.val) ⟨…, …⟩
-- plus a plain (no-NamedBinder) variant for postconditions
```

### 2. Pure `≤` bound, no `<` anywhere

`∀ i ≤ n, P i` / `∀ i, i ≤ n → P i`. Same root cause — the leading guard is
`LE.le`. Needs an analogous instance enumerating `Fin (n + 1)`.

### 3. Unbounded universal with only a disequality guard (occurs in our specs)

`Scalar/ReadLeU64Into.lean:185` — `∀ k, k ≠ j.val → result[k]! = s[k]!`.

There is **no** upper bound, so this ranges over all of `ℕ`. No instance can
decide it. This is a spec smell: it should likely read `∀ k < SIZE, k ≠ j.val → …`
to become testable.

### 4. `USize` / `UInt64`-typed bounded quantifiers — decidable but explosive

A hypothesis like `∀ k : USize, k < n → P k` is *technically* decidable via the
`Fintype` instance, but `decide` would enumerate 2⁶⁴ elements. The `Nat` + `Fin n`
trick is exactly what avoids this; there is no equivalent that restricts a
`UIntX` quantifier to the `< n` window. (Latent rather than confirmed present —
worth a targeted grep.)

### 5. Bounded and unbounded existentials — out of scope

`∃ i < n, …` has no instance. The concrete existentials in the specs
(`Field/FieldElement51/InvSqrt.lean:56` `∃ x : ℕ, x^2 * v % p = 1`;
`Edwards/CompressedEdwardsY/Decompress.lean:60` `∃ pt : Point Ed25519, …`) are
genuinely non-decidable mathematical statements, so no instance would help. A
bounded-existential instance (`decidable_of_iff (∃ i : Fin n, …)`) would help
only the rare `∃ i < n, <decidable>` shape.

### 6. Non-decidable or non-computable bodies — out of scope

Two distinct failure modes here; the first is subtler than it looks.

- **Genuinely non-decidable bodies.** Anything quantifying over `ℝ` / `ℚ`
  (`Montgomery/ProjectivePoint/DifferentialAddAndDouble.lean:110`), or bodies
  that unfold to existence statements. The quantifier instance may fire, but
  `DecidablePred` on the body fails, so the whole statement is not decidable.
- **Decidable but `noncomputable`.** `MontgomeryPoint.IsValid`'s decidability
  instance is `noncomputable` (`Math/Montgomery/Representation.lean:57`), so any
  spec quantifying it (`∀ i, … .IsValid` over Montgomery points) cannot be
  *evaluated* by Plausible even though it type-checks as `Decidable`.

Note what is **not** in this category: `EdwardsPoint.IsValid` and
`ProjectiveNielsPoint.IsValid` *are* decidable **and** computable
(`Math/Edwards/Representation.lean:206`, `:528`), and `Point Ed25519` has a
computable `DecidableEq` (`Math/Edwards/Curve.lean:68`) with computable
`Add`/`Zero`/`Neg`/`SMul`/`AddCommGroup` instances. So Edwards-side `IsValid`
and `toPoint = k • P.toPoint` bodies *are* decidable — see
[Fin-typed quantifiers](#fin-typed-quantifiers) for why that still doesn't always
make Plausible useful.

### 7. Shape brittleness (the meta-risk)

Everything hinges on Plausible emitting exactly `NamedBinder s (i < n → Q i)`.
If a Plausible version wraps the *conjunction* of two binders, wraps differently
per nesting level, or normalizes `n > i` / `i.val < n` into a form that does not
`whnf`-match `i < n`, instance 2 silently stops firing and Plausible falls back
to sampling — **with no error**, only a slower and less effective search.

## Fin-typed quantifiers

`∀ i : Fin n, P i` is **not** a limitation of the kind above: it is decided by
Mathlib's `Fintype.decidableForallFintype` with **no custom instance needed**,
enumerating exactly `n` cases. Our three `Nat` instances are irrelevant here.
Whether Plausible is *useful* then turns on two independent questions:

1. **Is the body `DecidablePred` *and computable*?** (See limitation 6 — decidable
   is not enough; a `noncomputable` instance cannot be evaluated.)
2. **Are there free inputs that must be *generated*?** A closed proposition (a
   spec about a constant or nullary function) needs no sampling at all — it is
   just a decidable check. A spec with generated inputs constrained by
   curve-relating preconditions hits the same "decide-but-can't-generate" wall as
   the `2^53` limb bounds, often worse.

The three `Fin`-quantifier specs illustrate all three outcomes:

| File | Body decidable + computable? | Free inputs to generate? | Verdict |
|------|------------------------------|--------------------------|---------|
| `Montgomery/MontgomeryPoint/Identity.lean:31` | yes (`U8`/`Nat` equality) | none (nullary) | **Works** — closed, cheap |
| `Backend/Serial/U64/Constants/EightTorsion.lean:42` | yes (`IsValid` + `Point Ed25519` equality, both computable) | none (constant) | **Works** — but evaluation is full `ZMod (2²⁵⁵−19)` curve arithmetic: fine under Plausible's *compiled* evaluation, painfully slow under kernel `decide` |
| `Window/LookupTable/From.lean:82` | yes (guards decidable) | `P`, `points`, `iter` + curve-relating hypotheses | **Ineffective** — preconditions `hP : P.IsValid` and `h_prefix_point : … = (k+1) • P.toPoint` are decidable guards, but a *random* `P`/`points` satisfies them with ~zero probability, so almost every sample is discarded |

`From.lean` is the instructive case: the `Fin` quantifiers in the *postcondition*
are perfectly decidable guards, but Plausible is still ineffective because the
*hypotheses* pin one generated input (`points`) to a measure-zero set relative to
another generated input (`P`). Decidability buys nothing when generation can't
reach the satisfying region — and unlike the limb-bound case there is no cheap
guard rewrite that fixes it.

## Summary

| # | Limitation | Status | Fix |
|---|------------|--------|-----|
| 1 | Lower bound before upper bound (`lo ≤ j → j < hi → …`) | Real, in specs | Add `lo ≤ j → j < hi` instance |
| 2 | Pure `≤` bound | Real if present | Add `i ≤ n` instance (`Fin (n+1)`) |
| 3 | Unbounded `∀ k, k ≠ j → …` | Real, in specs | Bound by array size in the spec |
| 4 | `USize`/`UInt64` bounded quantifier | Latent | Add window-restricting instance |
| 5 | Existentials | Mostly inherent | Bounded-existential instance for the decidable subset |
| 6 | Non-decidable (ℝ/ℚ) or `noncomputable`-decidable (`MontgomeryPoint.IsValid`) bodies | Inherent | None — out of scope for Plausible |
| 7 | Dependence on exact `NamedBinder` shape | Brittleness | Keep instances in sync with Plausible output |
| 8 | Generation can't reach a precondition's satisfying region (`From.lean:82`) | Inherent to random sampling | Test with hand-built witnesses, not random inputs |

For the dominant `∀ i < n, <decidable body on Nat>` pattern the three instances
are complete and cost-optimal. `Fin`-typed universals need no instance at all
(`Fintype.decidableForallFintype`) — for those, the body's decidability *and
computability* and the generability of any free inputs decide whether Plausible
helps. The limitations above bite, in rough order of how often they occur in the
current specs: lower-bound-first ranges (1), unbounded disequality guards (3),
then the more occasional pure-`≤` (2), `USize` (4), existential (5), the
non-decidable / non-computable bodies (6), and the generation wall (8).
