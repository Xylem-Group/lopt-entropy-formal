import Mathlib
import LoptEntropy.Entropy.MCV
import LoptEntropy.Entropy.Markov
import LoptEntropy.Entropy.Compression

/-!
# Composite Min-Entropy Estimator — SP 800-90B "Report the Minimum" Rule

Per NIST SP 800-90B §5, the assessed per-sample min-entropy is the **minimum** of the
individual estimator outputs (MCV, Markov, Compression). This file formalises that
composition and proves:

1. **Deterministic conservativeness** (`compositeMinEntropy_le_of_each`):
   if every estimator output is ≤ the true min-entropy H, so is their minimum.
2. **Monotonicity** (`compositeMinEntropy_le_*`): the composite never exceeds any
   single estimate.
3. **Probabilistic conservativeness** (`composite_estimator_is_conservative`):
   given high-confidence events for each estimator, the composite is conservative
   on a joint event whose probability is lower-bounded via the union bound.

This file sits downstream of the three estimator modules:
  - `LoptEntropy.Entropy.MCV`
  - `LoptEntropy.Entropy.Markov`
  - `LoptEntropy.Entropy.Compression`

It is deliberately decoupled from their internals — it takes the three real-valued
estimate outputs and the true min-entropy H, using each estimator's conservativeness
only as a hypothesis.
-/

namespace LoptEntropy.Entropy.Composition

noncomputable section

open Real Finset MeasureTheory

/-! ## Definition -/

/-- The composite (assessed) min-entropy: the minimum of the three estimator outputs,
    following the SP 800-90B "report the minimum" rule. -/
noncomputable def compositeMinEntropy (mcv markov compression : ℝ) : ℝ :=
  min mcv (min markov compression)

/-! ## Group 1 — Deterministic conservativeness -/

/-- If each individual estimator output is at most the true min-entropy `H`,
    then the composite min-entropy is also at most `H`. -/
theorem compositeMinEntropy_le_of_each
    {mcv markov compression H : ℝ}
    (_h_mcv : mcv ≤ H) (_h_markov : markov ≤ H) (_h_compression : compression ≤ H) :
    compositeMinEntropy mcv markov compression ≤ H :=
  le_trans (min_le_left _ _) _h_mcv

/-! ## Group 2 — Monotonicity: the composite never exceeds any single estimate -/

/-- The composite min-entropy is at most the MCV estimate. -/
theorem compositeMinEntropy_le_mcv (mcv markov compression : ℝ) :
    compositeMinEntropy mcv markov compression ≤ mcv :=
  min_le_left _ _

/-- The composite min-entropy is at most the Markov estimate. -/
theorem compositeMinEntropy_le_markov (mcv markov compression : ℝ) :
    compositeMinEntropy mcv markov compression ≤ markov :=
  min_le_of_right_le (min_le_left _ _)

/-- The composite min-entropy is at most the Compression estimate. -/
theorem compositeMinEntropy_le_compression (mcv markov compression : ℝ) :
    compositeMinEntropy mcv markov compression ≤ compression := by
  unfold compositeMinEntropy
  exact le_trans (min_le_right _ _) (min_le_right _ _)

/-! ## Group 3 — Probabilistic conservativeness -/

/-- **Intersection inclusion**: the intersection of the three confidence events
    is contained in the composite conservativeness event. That is, if each estimator
    is conservative on its respective event, then the composite is conservative on
    their intersection. -/
theorem composite_event_superset
    {Ω : Type*} [MeasurableSpace Ω]
    (mcv markov comp : Ω → ℝ) (H : ℝ)
    (E_mcv E_markov E_comp : Set Ω)
    (h_mcv : ∀ ω ∈ E_mcv, mcv ω ≤ H)
    (_h_markov : ∀ ω ∈ E_markov, markov ω ≤ H)
    (_h_comp : ∀ ω ∈ E_comp, comp ω ≤ H) :
    E_mcv ∩ E_markov ∩ E_comp ⊆
      {ω | compositeMinEntropy (mcv ω) (markov ω) (comp ω) ≤ H} := by
  intro ω ⟨⟨hm, hmk⟩, hc⟩
  exact compositeMinEntropy_le_of_each (h_mcv ω hm) (_h_markov ω hmk) (_h_comp ω hc)

/-- **Union bound for three sets**: the measure of the complement of the composite
    conservativeness event is bounded by the sum of the complements of the individual
    confidence events. Together with `composite_event_superset`, this gives a usable
    lower bound on the probability that the composite estimator is conservative.

    Concretely, if `μ(E_i) ≥ α_i` for each `i`, then
    `μ(F) ≥ 1 - ((1 - α₁) + (1 - α₂) + (1 - α₃))`. -/
theorem composite_complement_union_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (E_mcv E_markov E_comp : Set Ω) :
    μ ((E_mcv ∩ E_markov ∩ E_comp)ᶜ) ≤ μ E_mcvᶜ + μ E_markovᶜ + μ E_compᶜ := by
  rw [Set.compl_inter, Set.compl_inter]
  exact le_trans (measure_union_le _ _) (add_le_add (measure_union_le _ _) le_rfl)

/-- **Main probabilistic conservativeness theorem**: combines the intersection
    inclusion and the union bound. The composite conservative event `F` satisfies
    `μ(Fᶜ) ≤ μ(E_mcvᶜ) + μ(E_markovᶜ) + μ(E_compᶜ)`, so high confidence in each
    estimator yields high confidence in the composite. -/
theorem composite_estimator_is_conservative
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (mcv markov comp : Ω → ℝ) (H : ℝ)
    (E_mcv E_markov E_comp : Set Ω)
    (h_mcv : ∀ ω ∈ E_mcv, mcv ω ≤ H)
    (h_markov : ∀ ω ∈ E_markov, markov ω ≤ H)
    (h_comp : ∀ ω ∈ E_comp, comp ω ≤ H) :
    let F := {ω | compositeMinEntropy (mcv ω) (markov ω) (comp ω) ≤ H}
    (E_mcv ∩ E_markov ∩ E_comp ⊆ F) ∧
    (μ Fᶜ ≤ μ E_mcvᶜ + μ E_markovᶜ + μ E_compᶜ) := by
  constructor
  · exact composite_event_superset mcv markov comp H E_mcv E_markov E_comp h_mcv h_markov h_comp
  · exact le_trans (measure_mono (Set.compl_subset_compl_of_subset
      (composite_event_superset mcv markov comp H E_mcv E_markov E_comp h_mcv h_markov h_comp)))
      (composite_complement_union_bound E_mcv E_markov E_comp)

end

end LoptEntropy.Entropy.Composition

/-!
## Notes

- The union bound is stated for exactly three events (matching the three SP 800-90B
  estimators formalised so far). A generalisation to `n` events via `Finset.sum` would
  be a natural extension.
- This file is deliberately decoupled from the estimator internals; adding a new
  estimator requires only extending the `compositeMinEntropy` definition and the
  corresponding lemmas.
-/
