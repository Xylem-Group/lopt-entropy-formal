# Codomain decision: `StieltjesFunction.generalizedInverse : ℝ → ?`

Should the generalized inverse `g(y) = sInf {x : ℝ | y ≤ f x}` of a
`StieltjesFunction` return `ℝ` or `EReal`? Our position, with the reasoning
to defend it on Zulip. Short version: **`EReal` is the correct primitive**,
with real-valued specialization lemmas for the CDF / Φ⁻¹ use case. It's not
a genuine toss-up.

## Why it's a real question, not bikeshedding

`g(y) = sInf {x : ℝ | y ≤ f x}` is total only if `sInf` is meaningful on
the two degenerate level-sets:

| level-set `{x | y ≤ f x}` | when | `sInf` in `ℝ` | `sInf` in `EReal` | correct value |
|---|---|---|---|---|
| empty | `y > sup f` | `0` (junk) | `⊤` | `+∞` |
| all of `ℝ` (unbdd below) | `y ≤ inf f` | `0` (junk) | `⊥` | `−∞` |
| nonempty, bdd below | otherwise | genuine `inf` | same | the real |

In `ℝ`, the only way to keep the API honest is to bolt `Nonempty` +
`BddBelow` hypotheses onto every lemma to exclude the junk rows. That is
exactly the `(hne …) (hbdd …)` pair that currently proliferates through
`Inverse.lean`. In `EReal` the function is **total and correct with no
hypotheses** — the junk rows become `⊤` / `⊥`, which are the right answers.

## The decisive argument: the central theorem is unconditional in `EReal`

The load-bearing result is the Galois connection
`g(y) ≤ x ↔ y ≤ f x`. Everything else (monotonicity, left-continuity,
inversion) is downstream of it.

**In `EReal` it holds for all `y : ℝ`, `x : ℝ` with no side conditions:**

- `(←)` `y ≤ f x ⟹ x ∈ {x | y ≤ f x} ⟹ g(y) ≤ x`. The `sInf`-is-a-lower-
  bound step needs no `BddBelow` in `EReal` (every set has an `sInf`).
- `(→)` `{x | y ≤ f x}` is a **closed up-set** (closed from right-continuity
  — our `isClosed_le_preimage`; up-set from monotonicity). A closed up-set in
  `ℝ` is `[a, ∞)`, `∅`, or `ℝ`. So `g(y) ≤ x ⟺ x` is in the set `⟺ y ≤ f x`.
- Degenerate rows are handled *by the same statement*: empty set → `g(y)=⊤`,
  and both `⊤ ≤ x` (false for real `x`) and `y ≤ f x` (false, set empty) —
  iff holds vacuously. Unbounded → `g(y)=⊥`, both sides true. ✓

In `ℝ` the same theorem needs `Nonempty` + `BddBelow` *and still degrades at
the boundary*. When your central theorem gets strictly cleaner in one
formulation, that formulation is the right primitive. This is the line we'd
defend with: *"the Galois connection is unconditional over `EReal` and
hypothesis-encumbered over `ℝ`."*

## This is mathlib house style, not our taste

mathlib systematically picks the extended/junk-free type for monotone and
measure-theoretic objects precisely to keep the basic API hypothesis-free:

- measures land in `ℝ≥0∞` (`ENNReal`) so `μ` is total — no
  "measurable ∧ finite" guards on the core lemmas;
- `essSup` / `essInf`, lower/upper integrals, and `∫⁻` use `EReal` / `ENNReal`
  for the same reason;
- `sInf` / `sSup` are *defined* total on `EReal`.

A `StieltjesFunction` lives in `MeasureTheory`; its generalized inverse
composes with that ecosystem. An `EReal` codomain is the locally consistent
choice, and reviewers steeped in that convention will recognize it.

## The honest cost of `EReal` (and how we pay it)

The one real downside: the *application* — CDF quantiles, our Φ⁻¹ — wants a
genuine real back, and an `EReal` result forces a `.toReal` / `≠ ⊤ ∧ ≠ ⊥`
discharge downstream. We don't think this sinks `EReal`; we pay it the way
mathlib pays it elsewhere — **define the general primitive in the extended
type, then provide real-valued specialization under the hypotheses that
hold for the application:**

- `generalizedInverse : ℝ → EReal` — the total, unconditional primitive
  (Galois connection, monotone, left-continuous, all hypothesis-free).
- characterization lemmas: `g y ≠ ⊤ ↔ {x | y ≤ f x}.Nonempty`,
  `g y ≠ ⊥ ↔ BddBelow …`, so finiteness is a clean side-lemma not a
  pervasive hypothesis.
- for the CDF case where `0 < p ∧ p ≤ 1` makes both automatic, a
  `(f.generalizedInverse p).toReal` wrapper (or a `realGeneralizedInverse`
  abbreviation) with the `toReal` lemmas. Φ⁻¹ then lands on `ℝ` directly,
  finiteness discharged once.

This gives mathlib the correct general object *and* gives our downstream the
ergonomics, without scattering `Nonempty`/`BddBelow` across the general API.

## The one caveat that keeps us humble

If mathlib's existing CDF-adjacent code (`Mathlib.Probability.CDF`,
`MeasureTheory.Measure.Stieltjes`) already commits to an `ℝ`-with-hypotheses
convention for related inverses, *consistency with the neighbours can
outweigh the abstract argument* — house style is local. We can't fully
verify their current convention from here, so the Zulip ask is framed as
"we propose `EReal` for these reasons; does that match how you'd want it to
sit next to the existing Stieltjes/CDF API, or is there a convention we
should match instead?" Defended position, not a dictate.

## Bottom line

`EReal` primitive + `ℝ` specialization for the application. The tie-breaker
is that the Galois connection — the reason the whole file exists — is
unconditional over `EReal`. If a maintainer surfaces an existing local
convention to the contrary, we defer to it; otherwise this is the cleaner
mathlib object.

Drafted by `lopt`, 2026-05-30.
