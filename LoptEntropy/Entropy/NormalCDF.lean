/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
import LoptEntropy.Mathlib.StieltjesFunction.InverseEReal
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Standard normal CDF and its quantile inverse

This file defines the standard normal cumulative distribution function Φ as a Stieltjes function,
and its generalized (quantile) inverse Φ⁻¹ via `StieltjesFunction.egInverse`.

## Main definitions

* `stdNormalCDF` — the CDF of the standard normal distribution `gaussianReal 0 1`,
  as a `StieltjesFunction ℝ`.
* `stdNormalQuantile` — the quantile function Φ⁻¹, defined as `stdNormalCDF.egInverse`,
  mapping `ℝ → EReal`.
* `stdNormalQuantileReal` — the real-valued quantile `(stdNormalQuantile p).toReal`.

## Main results

* `stdNormalCDF_tendsto_atBot` / `stdNormalCDF_tendsto_atTop` — Φ(x) → 0 as x → -∞
  and Φ(x) → 1 as x → +∞.
* `stdNormalQuantile_ne_top` / `stdNormalQuantile_ne_bot` — for `p ∈ (0, 1)`,
  the quantile is finite (neither `⊤` nor `⊥`).
* `stdNormalQuantile_toReal_le_iff` — `Φ⁻¹(p) ≤ x ↔ p ≤ Φ(x)` for `p ∈ (0, 1)`.
* `le_stdNormalCDF_stdNormalQuantileReal` — `p ≤ Φ(Φ⁻¹(p))` for `p ∈ (0, 1)`.

## References

Uses the probability CDF infrastructure from Mathlib (`ProbabilityTheory.cdf`) and the
generalized inverse from `StieltjesFunction.egInverse`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-! ### Standard normal CDF -/

/-- Standard normal CDF Φ, as a Stieltjes function.
  Defined as `ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)`. -/
noncomputable def stdNormalCDF : StieltjesFunction ℝ :=
  ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)

/-- Φ(x) → 0 as x → -∞. -/
theorem stdNormalCDF_tendsto_atBot : Tendsto stdNormalCDF atBot (𝓝 0) :=
  ProbabilityTheory.tendsto_cdf_atBot _

/-- Φ(x) → 1 as x → +∞. -/
theorem stdNormalCDF_tendsto_atTop : Tendsto stdNormalCDF atTop (𝓝 1) :=
  ProbabilityTheory.tendsto_cdf_atTop _

/-! ### Standard normal quantile (EReal-valued) -/

/-- Standard normal quantile Φ⁻¹, `EReal`-valued (total).
  Defined as `stdNormalCDF.egInverse p`. -/
noncomputable def stdNormalQuantile (p : ℝ) : EReal :=
  stdNormalCDF.egInverse p

/-- For `p ∈ (0, 1)`, the quantile Φ⁻¹(p) is not `⊤`.
  By `egInverse_ne_top_iff`, it suffices to show `{x | p ≤ Φ(x)} ≠ ∅`.
  Since `Φ(x) → 1` as `x → +∞` and `p < 1`, eventually `p ≤ Φ(x)`. -/
theorem stdNormalQuantile_ne_top {p : ℝ} (_hp0 : 0 < p) (hp1 : p < 1) :
    stdNormalQuantile p ≠ ⊤ := by
  unfold stdNormalQuantile
  rw [StieltjesFunction.egInverse_ne_top_iff]
  have h_tendsto : Tendsto (fun x : ℝ => stdNormalCDF x) atTop (nhds 1) := by
    convert stdNormalCDF_tendsto_atTop using 1
  have h_exists_x : ∃ x : ℝ, p < stdNormalCDF x :=
    (h_tendsto.eventually (lt_mem_nhds hp1)).exists
  exact Set.Nonempty.ne_empty
    ⟨Classical.choose h_exists_x, le_of_lt (Classical.choose_spec h_exists_x)⟩

/-- For `p ∈ (0, 1)`, the quantile Φ⁻¹(p) is not `⊥`.
  By `egInverse_ne_bot_iff`, it suffices to show `BddBelow {x | p ≤ Φ(x)}`.
  Since `Φ(x) → 0` as `x → -∞` and `0 < p`, eventually `Φ(x) < p`, so points
  with `p ≤ Φ(x)` are bounded below. -/
theorem stdNormalQuantile_ne_bot {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    stdNormalQuantile p ≠ ⊥ := by
  have h_exists_x : ∃ x, p ≤ stdNormalCDF x := by
    have h_lim : Tendsto (fun x => stdNormalCDF x) atTop (nhds 1) := by
      convert stdNormalCDF_tendsto_atTop using 1
    exact (h_lim.eventually (le_mem_nhds hp1)).exists
  contrapose! h_exists_x
  have h_not_bdd_below : ¬BddBelow {x | p ≤ stdNormalCDF x} :=
    (StieltjesFunction.egInverse_eq_bot_iff stdNormalCDF).mp h_exists_x
  contrapose! h_not_bdd_below
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ x < b, stdNormalCDF x < p := by
    have := stdNormalCDF_tendsto_atBot.eventually (gt_mem_nhds hp0)
    obtain ⟨b, hb⟩ := eventually_atBot.mp this
    exact ⟨b, fun x hx => hb x hx.le⟩
  exact ⟨b, fun x hx => not_lt.1 fun contra => not_le.2 (hb x contra) hx⟩

/-! ### Real-valued quantile and inversion -/

/-- Real-valued standard normal quantile, defined as `(stdNormalQuantile p).toReal`. -/
noncomputable def stdNormalQuantileReal (p : ℝ) : ℝ :=
  (stdNormalQuantile p).toReal

/-- For `p ∈ (0, 1)`, `Φ⁻¹(p) ≤ x ↔ p ≤ Φ(x)`.
  This bridges between the `EReal`-valued quantile and real-valued CDF.
  Uses `egInverse_le_iff` and the finiteness of `stdNormalQuantile p` on `(0, 1)`
  to convert between `EReal` and `ℝ`. -/
theorem stdNormalQuantile_toReal_le_iff {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    stdNormalQuantileReal p ≤ x ↔ p ≤ stdNormalCDF x := by
  unfold stdNormalQuantileReal
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal]
  · exact StieltjesFunction.egInverse_le_iff stdNormalCDF
  · exact stdNormalQuantile_ne_top hp0 hp1
  · exact stdNormalQuantile_ne_bot hp0 hp1

/-- For `p ∈ (0, 1)`, `p ≤ Φ(Φ⁻¹(p))`.
  This is the fundamental right-continuity property of the quantile. -/
theorem le_stdNormalCDF_stdNormalQuantileReal {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    p ≤ stdNormalCDF (stdNormalQuantileReal p) :=
  (stdNormalQuantile_toReal_le_iff hp0 hp1).mp le_rfl

end

/-!
## Open questions

### (a) Strict monotonicity and two-sided inverse

With strict monotonicity of Φ (which follows from the positivity of the Gaussian density
`gaussianPDFReal 0 1 x > 0` for all `x`), one can strengthen the inequality
`p ≤ Φ(Φ⁻¹(p))` to a full equality `Φ(Φ⁻¹(p)) = p` for `p ∈ (0, 1)`.

Proving strict monotonicity requires showing that `gaussianReal 0 1` is absolutely continuous
with respect to Lebesgue measure with an everywhere-positive density, and then that
`μ(Ioc a b) > 0` for `a < b`. This is a natural follow-up.

### (b) Generalization to `gaussianReal μ v`

The definitions and lemmas in this file specialize to the standard normal (`μ = 0`, `v = 1`).
A generalization to arbitrary `gaussianReal μ v` with `v ≠ 0` would follow a similar pattern,
using the affine relationship `Φ_{μ,σ²}(x) = Φ((x - μ) / σ)`.
-/
