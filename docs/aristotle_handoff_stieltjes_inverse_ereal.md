# Aristotle handoff: EReal-valued StieltjesFunction generalized inverse

Rewrite of the existing `StieltjesFunction.generalizedInverse` (ℝ-valued,
hypothesis-laden) into the **`EReal`-valued, total, hypothesis-free** form.
Verified against the same mathlib pin as the rest of the repo.

## Why this rewrite

We investigated mathlib at the pinned rev (`c5ea003`, v4.30.0):

- `StieltjesFunction R` has `toFun : R → ℝ` (domain `R`, codomain `ℝ`); for
  `R = ℝ` it's `ℝ → ℝ`.
- `Mathlib.Probability.CDF` defines `cdf μ : StieltjesFunction ℝ` with
  `tendsto_cdf_atBot (𝓝 0)` / `tendsto_cdf_atTop (𝓝 1)` — and **no inverse
  or quantile exists anywhere in mathlib** (confirmed by code search).
- `EReal` is a `CompleteLinearOrder`: `sInf` is total, `sInf ∅ = ⊤`.

The ℝ-valued inverse `sInf {x | y ≤ f x}` returns junk (`0`) on the empty
and unbounded-below level sets, forcing `Nonempty` + `BddBelow` hypotheses
on every lemma. Over `EReal` those rows become `⊤` / `⊥` — the correct
`±∞` quantile values — and the whole API becomes unconditional. Since
mathlib's CDF reaches 0/1 only in the limit, `F⁻¹(0) = −∞` and `F⁻¹(1) = +∞`
are the *real* endpoints of every quantile function, not edge cases.

## Target file

    LoptEntropy/Mathlib/StieltjesFunction/InverseEReal.lean

(New file; do not overwrite `Inverse.lean` — we keep both during review so
the diff/tradeoff is legible. Same import discipline: minimal.)

## Definition

```lean
/-- Generalized inverse (quantile function) of a Stieltjes function,
`EReal`-valued and total: `sInf` of the level set embedded in `EReal`,
so the empty set gives `⊤` (the value is never reached) and an unbounded
level set gives `⊥`. -/
noncomputable def egInverse (f : StieltjesFunction ℝ) (y : ℝ) : EReal :=
  sInf ((↑) '' {x : ℝ | y ≤ f x})   -- (↑) : ℝ → EReal
```

(Name `egInverse` is a working name — `generalizedInverseEReal` or a
namespaced `generalizedInverse` if the ℝ one is retired. Flag naming in the
open-questions block; we settle it on Zulip.)

## The load-bearing theorem (must be UNCONDITIONAL)

```lean
/-- **Galois connection, unconditional over `EReal`.** For all `y x : ℝ`,
`f.egInverse y ≤ (x : EReal) ↔ y ≤ f x`. No `Nonempty`/`BddBelow`. -/
theorem egInverse_le_iff (f : StieltjesFunction ℝ) {y x : ℝ} :
    f.egInverse y ≤ (x : EReal) ↔ y ≤ f x
```

Proof ingredients (both already available — reuse the existing file's idea):
- `(←)`: `y ≤ f x ⟹ x ∈ {x | y ≤ f x} ⟹ (x:EReal) ∈ image ⟹ sInf ≤ x`
  via `sInf_le` (complete lattice — no `BddBelow` needed).
- `(→)`: the level set `{x | y ≤ f x}` is a **closed up-set** (closed from
  right-continuity — port `isClosed_le_preimage`; up-set from `f.mono`). If
  `y ≤ f x` fails, then `f x < y`, so every `t` in the set has `t > x`
  (else `f t ≤ f x < y`), making `x` a lower bound; with closedness the inf
  is attained in the set, contradicting `sInf ≤ x`. The empty/`ℝ` cases
  satisfy the iff because `⊤ ≤ (x:EReal)` is false and `⊥ ≤ _` is true,
  matching `y ≤ f x` false/true respectively.

Everything below follows from this iff.

## Downstream lemmas (all unconditional)

```lean
theorem egInverse_mono (f : StieltjesFunction ℝ) : Monotone f.egInverse
-- from the iff (or: level sets are antitone in y ⟹ sInf monotone)

theorem egInverse_eq_top_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y = ⊤ ↔ {x : ℝ | y ≤ f x} = ∅      -- = ⊤ ↔ y unreachable

theorem egInverse_eq_bot_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y = ⊥ ↔ ¬ BddBelow {x : ℝ | y ≤ f x}

theorem egInverse_apply_self (f : StieltjesFunction ℝ) (hf : StrictMono f)
    (x : ℝ) : f.egInverse (f x) = (x : EReal)     -- inversion, NO bdd hyp now
```

Left-continuity: state it if it ports cleanly in the `EReal` order topology
(`EReal` is compact, so this may be *cleaner* than the ℝ version). If it
fights the `EReal` topology, leave it as a documented open issue rather than
forcing it — do NOT use `sorry`.

## Real-valued specialization (for the CDF / Φ⁻¹ downstream)

```lean
/-- For a probability CDF and `0 < p ≤ 1`, the quantile is a genuine real:
the level set is nonempty (since `f → 1` at `atTop`) and bounded below
(since `f → 0` at `atBot`). -/
theorem egInverse_ne_top_of_... / egInverse_ne_bot_of_...   -- finiteness
-- then `(f.egInverse p).toReal` is the usable ℝ-valued quantile, with the
-- `toReal` round-trip lemmas. This is the bridge back to MCV.lean's Φ⁻¹.
```

State the finiteness conditions in whatever form is cleanest; the point is
that finiteness is a *side lemma under hypotheses*, not a hypothesis smeared
across the whole API.

## Style / acceptance (mathlib-PR-grade — this is upstream-bound)

- Compiles clean against the repo's pinned mathlib (v4.30.0). Zero `sorry`,
  zero `admit`, zero new axioms.
- **Real human author** on the `Authors:` line (not "Harmonic") and 2026
  copyright — this file is headed for a mathlib PR.
- Minimal imports: `Mathlib.MeasureTheory.Measure.Stieltjes`,
  `Mathlib.Data.EReal.Basic`, immediate deps only.
- Docstring on every def + theorem. No `simp +decide`, no unused
  hypotheses (the old `Inverse.lean` carried an unused `_hbdd` — don't
  reproduce it).
- Footer "open design questions" block naming: (a) the name `egInverse`
  vs `generalizedInverse`; (b) whether to also bundle this as a
  `GaloisConnection` once `f` is extended to `EReal → EReal` (the Tier-3
  follow-up); (c) left-continuity if deferred. Honest open issues only —
  reviewers engage with those, not with `sorry`.
- Target size ~150–250 lines.

## Out of scope (separate later slices)

- Extending `f` to `EReal → EReal` and bundling the genuine
  `GaloisConnection` (Tier 3).
- The Gaussian Φ / Φ⁻¹ instantiation and the rewire into `MCV.lean`.

Drafted by `lopt` for Aristotle dispatch, 2026-05-30. Supersedes the
ℝ-valued spec in `aristotle_handoff_stieltjes_inverse.md` (kept for history).
