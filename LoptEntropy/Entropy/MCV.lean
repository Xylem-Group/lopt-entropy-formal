import Mathlib

/-! # Most Common Value (MCV) Min-Entropy Estimator

Formalization of the MCV min-entropy estimator from NIST SP 800-90B §6.3.1.

## Overview

The MCV estimator works as follows:
1. Compute `p̂ = c_max / n` (empirical maximum frequency).
2. Compute the upper confidence bound
   `p_u = min(1, p̂ + z_α · √(p̂(1 − p̂)/(n − 1)))`.
3. Return `H_min_MCV = −log₂(p_u)`.

## Main results

* `mcv_conservative_of_pMax_le_pU`: **Deterministic core.** If the upper
  confidence bound `p_u` is at least `p_max` (the true maximum probability)
  and `p_max > 0`, then the MCV estimate lower-bounds the true min-entropy.

* `mcv_estimator_is_conservative`: **Probabilistic wrapper.** Given any
  event `E` (guaranteed by the normal approximation to have probability ≥ α)
  on which `p_max ≤ p_u`, the event "MCV estimate ≤ true min-entropy" also
  has probability ≥ α.

## Axiomatization

The standard normal CDF `Φ` and its inverse are not yet available in
Mathlib in a convenient packaged form. The probabilistic guarantee of
the normal approximation (that the confidence-bound event has probability
≥ α) is therefore taken as a hypothesis rather than derived from first
principles. All other reasoning is fully proved.

## Reference

NIST SP 800-90B (January 2018), Section 6.3.1.
-/

noncomputable section

open Real Finset MeasureTheory

namespace LoptEntropy.Entropy.MCV

/-! ### Definitions -/

/-- Maximum probability in a distribution over a finite nonempty type. -/
def pMax {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty p

/-- Min-entropy of a probability distribution:
    `H_min(p) = −log₂(max_i p(i))`. -/
def minEntropy {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ) : ℝ :=
  -Real.logb 2 (pMax p)

/-- MCV upper confidence bound on the maximum probability:
    `p_u = min(1, p̂ + z_α · √(p̂(1 − p̂)/(n − 1)))`. -/
def mcvUpperBound (pHat : ℝ) (n : ℕ) (zAlpha : ℝ) : ℝ :=
  min 1 (pHat + zAlpha * Real.sqrt
    (pHat * (1 - pHat) / ((n : ℝ) - 1)))

/-- MCV min-entropy estimate: `−log₂(p_u)`. -/
def mcvMinEntropy (pHat : ℝ) (n : ℕ) (zAlpha : ℝ) : ℝ :=
  -Real.logb 2 (mcvUpperBound pHat n zAlpha)

/-! ### Auxiliary lemma: −log₂ is antitone on positives -/

/-- If `0 < a ≤ b`, then `−log₂(b) ≤ −log₂(a)`:
    negated log base 2 is antitone on positive reals. -/
theorem neg_logb_antitone {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    -Real.logb 2 b ≤ -Real.logb 2 a := by
  apply neg_le_neg
  rw [Real.logb, Real.logb,
    div_le_div_iff_of_pos_right (by positivity)]
  exact Real.log_le_log ha hab

/-! ### Core deterministic theorem -/

/-- **Deterministic core of MCV conservativeness.**

If the MCV upper confidence bound `p_u` is at least `p_max` (the true
maximum probability) and `p_max > 0`, then
`−log₂(p_u) ≤ −log₂(p_max)`, i.e. the MCV min-entropy estimate is a
lower bound on the true min-entropy.

This is the mathematical heart of the MCV estimator's correctness:
`−log₂` is antitone on `(0, ∞)`, so a larger argument yields a smaller
(more conservative) entropy estimate. -/
theorem mcv_conservative_of_pMax_le_pU
    {α : Type*} [Fintype α] [Nonempty α]
    (p : α → ℝ)
    (pHat : ℝ) (n : ℕ) (zAlpha : ℝ)
    (hpos : 0 < pMax p)
    (hle : pMax p ≤ mcvUpperBound pHat n zAlpha) :
    mcvMinEntropy pHat n zAlpha ≤ minEntropy p :=
  neg_logb_antitone hpos hle

/-! ### Probabilistic conservativeness

The probabilistic statement uses an abstract probability space `(Ω, μ)`.
The normal approximation to the binomial proportion guarantees the
existence of an event `E` with `μ(E) ≥ α` on which `p_max ≤ p_u`.
This is taken as a hypothesis; the theorem then shows the event
"MCV estimate ≤ true min-entropy" also has probability ≥ α.
-/

/-- **Main theorem (NIST SP 800-90B §6.3.1).**

The MCV min-entropy estimator is conservative at confidence level `α`:
the probability that the MCV estimate lower-bounds the true min-entropy
is at least `α`, given that the normal-approximation confidence event
has probability at least `α`.

More precisely, let `E` be any measurable event on which
`p_max ≤ mcvUpperBound (pHat ω) n zAlpha` holds. If `μ(E) ≥ α`, then
`μ({ω | mcvMinEntropy (pHat ω) n zAlpha ≤ minEntropy p}) ≥ α`. -/
theorem mcv_estimator_is_conservative
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {α_level : ℝ}
    {α_type : Type*} [Fintype α_type] [Nonempty α_type]
    (p : α_type → ℝ)
    (pHat : Ω → ℝ) (n : ℕ) (zAlpha : ℝ)
    (hpos : 0 < pMax p)
    (E : Set Ω)
    (_hE_meas : MeasurableSet E)
    (hE_prob : α_level ≤ (μ E).toReal)
    (hE_impl : ∀ ω ∈ E,
      pMax p ≤ mcvUpperBound (pHat ω) n zAlpha)
    (F : Set Ω)
    (hF_def : F = {ω | mcvMinEntropy (pHat ω) n zAlpha
      ≤ minEntropy p})
    (_hF_meas : MeasurableSet F) :
    α_level ≤ (μ F).toReal := by
  refine le_trans hE_prob (ENNReal.toReal_mono ?_ ?_)
  · exact MeasureTheory.measure_ne_top _ _
  · exact MeasureTheory.measure_mono fun ω hω =>
      hF_def ▸ mcv_conservative_of_pMax_le_pU
        p (pHat ω) n zAlpha hpos (hE_impl ω hω)

end LoptEntropy.Entropy.MCV
