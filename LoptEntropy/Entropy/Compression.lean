import Mathlib

/-! # Compression Min-Entropy Estimator (NIST SP 800-90B §6.3.3)

Formalization of the Compression-based min-entropy estimator from
NIST SP 800-90B §6.3.3. This is Maurer's universal statistical test
in NIST's adapted form.

## Overview

The Compression estimator works as follows:
1. Partition the sample sequence `X_0, …, X_{L-1}` into an
   initialization segment of length `d` and a test segment of length
   `N = L − d`.
2. For each test-segment position `i ≥ d`, compute the *prior distance*
   `D_i`: the gap back to the last prior occurrence of `X_i`, or `i + 1`
   if `X_i` has not appeared before (0-based indexing).
3. Compute the sample mean `X̄ = (1/N) · Σ log₂(D_i)` over the test
   segment.
4. Subtract a confidence margin `σ` to obtain the lower confidence bound
   `X̄^L = X̄ − σ`.
5. Apply an asymptotic correction factor `G` to obtain the per-sample
   min-entropy estimate: `H_min = X̄^L / G(2^{−X̄^L})`.

## Main results

* `compression_monotone_sigma`: **Monotonicity in σ.** A larger
  confidence margin yields a smaller (more conservative) entropy
  estimate, given that the correction factor `G` makes
  `t ↦ t / G(2^{−t})` monotone.

* `compression_conservative_of_deviation_le`: **Deterministic core.**
  If the lower confidence bound is at most the true expected log₂
  distance, and the correction factor `G` correctly relates the true
  expected log₂ distance to the min-entropy, then the compression
  estimate lower-bounds the true min-entropy.

* `compression_estimator_is_conservative`: **Probabilistic wrapper.**
  Given any event `E` (guaranteed by the sampling distribution to have
  probability ≥ α) on which the deterministic hypotheses hold, the
  event "compression estimate ≤ true min-entropy" also has probability
  ≥ α.

## Relation to other estimators

This file is the third in a series of SP 800-90B estimators:
- `LoptEntropy/Entropy/MCV.lean` — §6.3.1 Most Common Value
- `LoptEntropy/Entropy/Markov.lean` — §6.3.2 Markov (in dispatch)
- **This file** — §6.3.3 Compression

All three follow the same structure: a deterministic core lemma
(where the confidence event is taken as a hypothesis) plus a
probabilistic wrapper that lifts the deterministic guarantee to a
measure-theoretic statement.

## Axiomatization

The correction factor `G` from NIST eq. 6.3.3.2-(4) is taken as a
parameter with stated monotonicity assumptions, rather than derived
in closed form. The confidence margin `σ` (which depends on the
standard normal quantile) is similarly taken as a parameter. Both
explicit derivations are downstream tasks (see Open Issues below).

## Reference

NIST SP 800-90B (January 2018), Section 6.3.3.
-/

noncomputable section

open Real Finset MeasureTheory

namespace LoptEntropy.Entropy.Compression

/-! ### Distribution definitions (mirrored from MCV for self-containedness) -/

/-- Maximum probability in a distribution over a finite nonempty type. -/
def pMax {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty p

/-- Min-entropy of a probability distribution:
    `H_min(p) = −log₂(max_i p(i))`. -/
def minEntropy {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) : ℝ :=
  -Real.logb 2 (pMax p)

/-! ### Prior distance -/

/-- Distance from position `i` to the last prior occurrence of `X i`,
    or `i + 1` if no prior occurrence exists. Uses 0-based indexing;
    the minimum distance is 1, ensuring `log₂(priorDistance X i) ≥ 0`.

    Formally: let `P = {j : Fin L | j < i ∧ X j = X i}`. If `P` is
    nonempty, return `i − max(P)`; otherwise return `i + 1`. -/
def priorDistance {A : Type*} [DecidableEq A] {L : ℕ}
    (X : Fin L → A) (i : Fin L) : ℕ :=
  let priors := Finset.univ.filter (fun j : Fin L => j < i ∧ X j = X i)
  if h : priors.Nonempty then
    i.val - (priors.max' h).val
  else
    i.val + 1

/-- The prior distance is always at least 1. -/
theorem priorDistance_pos {A : Type*} [DecidableEq A] {L : ℕ}
    (X : Fin L → A) (i : Fin L) : 1 ≤ priorDistance X i := by
  unfold priorDistance
  simp only
  split
  · next h =>
    have hmax := Finset.max'_mem _ h
    rw [Finset.mem_filter] at hmax
    omega
  · omega

/-! ### Compression estimator definitions -/

variable {A : Type*} [DecidableEq A] {L : ℕ}

/-- Sample mean of `log₂(D_i)` over the test segment `{i : Fin L | d ≤ i}`.
    Returns `0` if the test segment is empty. -/
noncomputable def compressionMean
    (X : Fin L → A) (d : ℕ) : ℝ :=
  let testSet := Finset.univ.filter (fun i : Fin L => d ≤ i.val)
  if _h : testSet.Nonempty then
    (↑testSet.card)⁻¹ *
      ∑ i ∈ testSet, Real.logb 2 (priorDistance X i : ℝ)
  else 0

/-- Conservative lower bound on the mean log₂ distance,
    adjusted by confidence margin `σ`:
    `X̄^L = X̄ − σ`. -/
noncomputable def compressionLowerBound
    (X : Fin L → A) (d : ℕ) (σ : ℝ) : ℝ :=
  compressionMean X d - σ

/-- The map `t ↦ t / G(2^{−t})` that converts a lower bound on the
    mean log₂ distance to a min-entropy estimate via the correction
    factor `G`. Monotonicity of this map (as a hypothesis on `G`)
    ensures that a smaller lower bound yields a more conservative
    entropy estimate. -/
noncomputable def entropyOfBound (G : ℝ → ℝ) (t : ℝ) : ℝ :=
  t / G (2 ^ (-t))

/-- Compression min-entropy estimate, parameterized by the confidence
    margin `σ` and the asymptotic correction factor `G`:
    `H_min = (X̄ − σ) / G(2^{−(X̄ − σ)})`. -/
noncomputable def compressionMinEntropy
    (X : Fin L → A) (d : ℕ) (σ : ℝ) (G : ℝ → ℝ) : ℝ :=
  entropyOfBound G (compressionLowerBound X d σ)

/-! ### Core lemma: relationship between definitions -/

/-- The compression estimate equals `entropyOfBound` applied to the
    lower confidence bound. -/
theorem compressionMinEntropy_eq_entropyOfBound
    (X : Fin L → A) (d : ℕ) (σ : ℝ) (G : ℝ → ℝ) :
    compressionMinEntropy X d σ G =
      entropyOfBound G (compressionLowerBound X d σ) :=
  rfl

/-! ### Core theorem 1: Monotonicity in σ -/

/-- **Monotonicity of the compression estimate in the confidence margin.**

A larger confidence margin `σ₂ ≥ σ₁` yields a smaller (more conservative)
compression min-entropy estimate, provided the correction factor `G`
makes `t ↦ t / G(2^{−t})` monotone non-decreasing.

This captures the intuition that being more conservative about sampling
error (larger `σ`) produces a more conservative entropy estimate. -/
theorem compression_monotone_sigma
    {X : Fin L → A} {d : ℕ} {G : ℝ → ℝ} {σ₁ σ₂ : ℝ}
    (hG : Monotone (entropyOfBound G))
    (hσ : σ₁ ≤ σ₂) :
    compressionMinEntropy X d σ₂ G ≤ compressionMinEntropy X d σ₁ G := by
  simp only [compressionMinEntropy_eq_entropyOfBound]
  exact hG (sub_le_sub_left hσ _)

/-! ### Core theorem 2: Deterministic conservatism -/

/-- **Deterministic core of compression conservativeness.**

Given:
1. The lower confidence bound is at most the true expected log₂ distance
   (`hconf`: the sampling deviation is within the confidence margin).
2. The correction factor `G` makes `t ↦ t / G(2^{−t})` monotone
   (`hG_mono`).
3. The correction factor `G` correctly upper-bounds the min-entropy
   at the true expected log₂ distance (`hG_bound`).

Then the compression min-entropy estimate is a lower bound on the
true min-entropy.

This is the mathematical heart of the compression estimator's
correctness: monotonicity of `entropyOfBound G` lets us chain
the confidence-bound inequality through to the final estimate. -/
theorem compression_conservative_of_deviation_le
    {α_type : Type*} [Fintype α_type] [Nonempty α_type]
    (p : α_type → ℝ)
    {X : Fin L → A} {d : ℕ} {σ : ℝ} {G : ℝ → ℝ}
    (trueMean : ℝ)
    (hG_mono : Monotone (entropyOfBound G))
    (hconf : compressionLowerBound X d σ ≤ trueMean)
    (hG_bound : entropyOfBound G trueMean ≤ minEntropy p) :
    compressionMinEntropy X d σ G ≤ minEntropy p :=
  calc compressionMinEntropy X d σ G
      = entropyOfBound G (compressionLowerBound X d σ) := rfl
    _ ≤ entropyOfBound G trueMean := hG_mono hconf
    _ ≤ minEntropy p := hG_bound

/-! ### Core theorem 3: Probabilistic wrapper -/

/-- **Main theorem (NIST SP 800-90B §6.3.3).**

The compression min-entropy estimator is conservative at confidence
level `α`: the probability that the compression estimate lower-bounds
the true min-entropy is at least `α`, given that the confidence event
`E` has probability at least `α`.

More precisely, let `lb : Ω → ℝ` be the per-sample compression lower
bound (i.e., `lb ω = compressionLowerBound (X ω) d (σ ω)` for the
sample and margin at outcome `ω`). Let `E` be any measurable event on
which `lb ω ≤ trueMean` holds. If `μ(E) ≥ α`, then
`μ({ω | entropyOfBound G (lb ω) ≤ minEntropy p}) ≥ α`.

This follows the same pattern as `mcv_estimator_is_conservative` and
`markov_estimator_is_conservative`: the deterministic core guarantees
`E ⊆ F`, and measure-monotonicity lifts the probability bound. -/
theorem compression_estimator_is_conservative
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {α_level : ℝ}
    {α_type : Type*} [Fintype α_type] [Nonempty α_type]
    (p : α_type → ℝ)
    (G : ℝ → ℝ)
    (hG_mono : Monotone (entropyOfBound G))
    (trueMean : ℝ)
    (hG_bound : entropyOfBound G trueMean ≤ minEntropy p)
    (lb : Ω → ℝ)
    (E : Set Ω)
    (_hE_meas : MeasurableSet E)
    (hE_prob : α_level ≤ (μ E).toReal)
    (hE_impl : ∀ ω ∈ E, lb ω ≤ trueMean)
    (F : Set Ω)
    (hF_def : F = {ω | entropyOfBound G (lb ω) ≤ minEntropy p})
    (_hF_meas : MeasurableSet F) :
    α_level ≤ (μ F).toReal := by
  refine le_trans hE_prob (ENNReal.toReal_mono ?_ ?_)
  · exact MeasureTheory.measure_ne_top _ _
  · exact MeasureTheory.measure_mono fun ω hω =>
      hF_def ▸ le_trans (hG_mono (hE_impl ω hω)) hG_bound

end LoptEntropy.Entropy.Compression

/-! ### Open Issues

The following design questions are deferred to downstream tasks:

1. **Explicit form of `G(p)`.** The NIST correction factor `G` from
   eq. 6.3.3.2-(4) has a closed form involving the binary entropy
   function and a series expansion. Deriving it and proving it satisfies
   the `Monotone (entropyOfBound G)` hypothesis used here is a
   self-contained follow-up task.

2. **Confidence margin `σ` from the standard normal quantile.** The
   NIST formula for `σ` involves the sample standard deviation, the
   test-segment size `N`, and the standard normal quantile `z_α`
   (e.g., `z_{0.99} = 2.5758`). Formally deriving this requires the
   Gaussian CDF inverse, which depends on the `StieltjesFunction`
   inverse machinery on trunk. This is the same machinery needed for
   MCV's de-axiomatization.

3. **`priorDistance` bounds.** The fact that `priorDistance X i ≥ 1`
   (proved as `priorDistance_pos`) ensures `log₂(D_i) ≥ 0`. Tighter
   bounds relating `priorDistance` to the alphabet size and repetition
   structure could strengthen the estimator's guarantees.

4. **Composition theorem.** Once all three estimator files (MCV, Markov,
   Compression) are on trunk, the composition theorem — that the minimum
   of the three estimates is a conservative lower bound on min-entropy —
   becomes a straightforward `min`-of-lower-bounds argument.
-/
