import Mathlib

/-! # Markov Min-Entropy Estimator (NIST SP 800-90B §6.3.2)

Formalization of the Markov min-entropy estimator from NIST SP 800-90B §6.3.2.

## Overview

The Markov estimator works as follows:
1. Estimate initial-state probabilities `π̂_i` and transition probabilities `P̂_{i,j}`.
2. Build upper-confidence bounds `πU_i ≥ π̂_i` and `PU_{i,j} ≥ P̂_{i,j}`.
3. Define path probability: `pathProb(s_1,…,s_d) = πU_{s_1} · ∏ PU_{s_k,s_{k+1}}`.
4. Maximize over paths of length `d`: `maxPathProb = max_path pathProb(path)`.
5. Return per-sample min-entropy: `markovMinEntropy = −log₂(maxPathProb) / d`.

## Main results

* `pathProb_mono`: Path probability is monotone in the bound parameters.
* `maxPathProb_mono`: Maximum path probability is monotone in the bound parameters.
* `markov_conservative`: **Deterministic core.** If `πU ≥ pInit` and `PU ≥ pTrans`
  pointwise (and `maxPathProb pInit pTrans > 0`), then the Markov min-entropy
  estimate using `πU, PU` lower-bounds the true Markov min-entropy.
* `markov_estimator_is_conservative`: **Probabilistic wrapper.** Given an
  event `E` with `μ(E) ≥ α` on which the pointwise bounds hold, the event
  "Markov estimate ≤ true min-entropy" has probability ≥ α.

## Design notes

Paths of `d + 1` states and `d` transitions are represented as `Fin (d + 1) → A`,
where `d` is the number of transitions. Thus NIST's path length `d` corresponds
to `d + 1` in our indexing; the per-sample entropy divides by `(d + 1)`.

We avoid using `π` as a variable name since `open Real` brings `Real.pi` into
scope. Instead, `pInit` denotes the true initial distribution and `pTrans` the
true transition matrix.

The probabilistic wrapper takes the confidence event as a hypothesis (same
approach as `MCV.lean`). The actual Chernoff/Hoeffding bound that gives the
event is not yet available in Mathlib.

## Reference

NIST SP 800-90B (January 2018), Section 6.3.2.
-/

noncomputable section

open Real Finset MeasureTheory

namespace LoptEntropy.Entropy.Markov

/-! ### Definitions -/

variable {A : Type*} [Fintype A] [Nonempty A]

/-- Path probability under upper-confidence-bound initial distribution `πU`
and transition matrix `PU`. A path of `d + 1` states (indexed by `Fin (d + 1)`)
has probability `πU(path 0) · ∏_{k < d} PU(path k, path (k+1))`. -/
def pathProb (πU : A → ℝ) (PU : A → A → ℝ)
    {d : ℕ} (path : Fin (d + 1) → A) : ℝ :=
  πU (path 0) * ∏ k : Fin d, PU (path k.castSucc) (path k.succ)

/-- Maximum path probability over all paths of `d + 1` states. -/
def maxPathProb (πU : A → ℝ) (PU : A → A → ℝ) (d : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun path : Fin (d + 1) → A => pathProb πU PU path)

/-- Markov per-sample min-entropy estimate:
`−log₂(maxPathProb) / (d + 1)`. -/
def markovMinEntropy (πU : A → ℝ) (PU : A → A → ℝ) (d : ℕ) : ℝ :=
  -Real.logb 2 (maxPathProb πU PU d) / (d + 1 : ℝ)

/-! ### Auxiliary: −log₂ is antitone on positives -/

/-- Negated log base 2 is antitone on positive reals. -/
theorem neg_logb_antitone {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    -Real.logb 2 b ≤ -Real.logb 2 a := by
  apply neg_le_neg
  rw [Real.logb, Real.logb, div_le_div_iff_of_pos_right (by positivity)]
  exact Real.log_le_log ha hab

/-! ### Monotonicity of path probability -/

/-- Path probability is monotone in the bound parameters: if `πU₁ ≥ πU₂`
and `PU₁ ≥ PU₂` pointwise, and the smaller bounds are non-negative, then
`pathProb πU₂ PU₂ path ≤ pathProb πU₁ PU₁ path`. -/
theorem pathProb_mono {d : ℕ}
    (πU₁ πU₂ : A → ℝ) (PU₁ PU₂ : A → A → ℝ)
    (hπ : ∀ a, πU₂ a ≤ πU₁ a)
    (hP : ∀ a b, PU₂ a b ≤ PU₁ a b)
    (hπ_nn : ∀ a, 0 ≤ πU₂ a)
    (hP_nn : ∀ a b, 0 ≤ PU₂ a b)
    (path : Fin (d + 1) → A) :
    pathProb πU₂ PU₂ path ≤ pathProb πU₁ PU₁ path := by
  unfold pathProb
  apply mul_le_mul (hπ _)
  · exact Finset.prod_le_prod (fun _ _ => hP_nn _ _) fun _ _ => hP _ _
  · exact Finset.prod_nonneg fun _ _ => hP_nn _ _
  · exact le_trans (hπ_nn _) (hπ _)

/-- Maximum path probability is monotone in the bound parameters. -/
theorem maxPathProb_mono {d : ℕ}
    (πU₁ πU₂ : A → ℝ) (PU₁ PU₂ : A → A → ℝ)
    (hπ : ∀ a, πU₂ a ≤ πU₁ a)
    (hP : ∀ a b, PU₂ a b ≤ PU₁ a b)
    (hπ_nn : ∀ a, 0 ≤ πU₂ a)
    (hP_nn : ∀ a b, 0 ≤ PU₂ a b) :
    maxPathProb πU₂ PU₂ d ≤ maxPathProb πU₁ PU₁ d := by
  unfold maxPathProb
  apply Finset.sup'_le
  intro path _
  exact le_trans (pathProb_mono _ _ _ _ hπ hP hπ_nn hP_nn path)
    (Finset.le_sup' _ (Finset.mem_univ path))

/-! ### Deterministic core -/

/-- **Deterministic core of Markov conservativeness.**

If `πU ≥ pInit` and `PU ≥ pTrans` pointwise, all values non-negative, and
`maxPathProb pInit pTrans d > 0`, then the Markov min-entropy estimate using the
upper-confidence bounds is at most the true Markov min-entropy.

Here `pInit` is the true initial-state distribution and `pTrans` is the true
transition matrix; `πU` and `PU` are their upper-confidence bounds. -/
theorem markov_conservative {d : ℕ}
    (pInit πU : A → ℝ) (pTrans PU : A → A → ℝ)
    (hπ : ∀ a, pInit a ≤ πU a)
    (hP : ∀ a b, pTrans a b ≤ PU a b)
    (hπ_nn : ∀ a, 0 ≤ pInit a)
    (hP_nn : ∀ a b, 0 ≤ pTrans a b)
    (hpos : 0 < maxPathProb pInit pTrans d) :
    markovMinEntropy πU PU d ≤ markovMinEntropy pInit pTrans d :=
  div_le_div_of_nonneg_right
    (neg_logb_antitone hpos (maxPathProb_mono _ _ _ _ hπ hP hπ_nn hP_nn))
    (by positivity)

/-! ### Probabilistic wrapper -/

/-- **Main theorem (NIST SP 800-90B §6.3.2).**

The Markov min-entropy estimator is conservative at confidence level `α`:
the probability that the estimate lower-bounds the true min-entropy is at
least `α`, given that the confidence-bound event has probability ≥ `α`.

Let `E` be any measurable event on which the pointwise bounds
`pInit a ≤ πU(ω) a` and `pTrans a b ≤ PU(ω) a b` hold for all `a, b`. If
`μ(E) ≥ α`, then `μ({ω | markovMinEntropy (πU ω) (PU ω) d ≤
markovMinEntropy pInit pTrans d}) ≥ α`. -/
theorem markov_estimator_is_conservative
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {α_level : ℝ} {d : ℕ}
    (pInit : A → ℝ) (pTrans : A → A → ℝ)
    (πU : Ω → A → ℝ) (PU : Ω → A → A → ℝ)
    (hπ_nn : ∀ a, 0 ≤ pInit a)
    (hP_nn : ∀ a b, 0 ≤ pTrans a b)
    (hpos : 0 < maxPathProb pInit pTrans d)
    (E : Set Ω)
    (_hE_meas : MeasurableSet E)
    (hE_prob : α_level ≤ (μ E).toReal)
    (hE_impl : ∀ ω ∈ E,
      (∀ a, pInit a ≤ πU ω a) ∧ (∀ a b, pTrans a b ≤ PU ω a b))
    (F : Set Ω)
    (hF_def : F = {ω | markovMinEntropy (πU ω) (PU ω) d
      ≤ markovMinEntropy pInit pTrans d})
    (_hF_meas : MeasurableSet F) :
    α_level ≤ (μ F).toReal := by
  refine le_trans hE_prob (ENNReal.toReal_mono ?_ ?_)
  · exact MeasureTheory.measure_ne_top _ _
  · exact MeasureTheory.measure_mono fun ω hω =>
      hF_def ▸ markov_conservative pInit (πU ω) pTrans (PU ω)
        (hE_impl ω hω).1 (hE_impl ω hω).2 hπ_nn hP_nn hpos

end LoptEntropy.Entropy.Markov

