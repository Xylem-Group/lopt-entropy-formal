/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Basic

/-!
# Generalized inverse of a Stieltjes function

Given `f : StieltjesFunction ℝ` (a monotone, right-continuous function
`ℝ → ℝ`), we define its *generalized inverse* (also called the *quantile
function* when `f` is a CDF):

  `f.generalizedInverse y = sInf { x : ℝ | y ≤ f x }`

This is the canonical construction underlying quantile functions in
probability theory.

The generalized inverse is the left adjoint of `f` in a Galois connection:
the fundamental characterization is
`f.generalizedInverse y ≤ x ↔ y ≤ f x` (see `generalizedInverse_le_iff`).
Monotonicity, left-continuity, and inversion on the range all follow from
this.

**Continuity note.** The generalized inverse defined via
`sInf {x | y ≤ f x}` is *left-continuous* in `y`, not right-continuous.
This is standard in probability: the quantile function
`F⁻¹(p) = inf {x | p ≤ F(x)}` is left-continuous. A right-continuous
variant uses strict inequality (`sInf {x | y < f x}`) but loses the clean
Galois connection.

## Main definitions

* `StieltjesFunction.generalizedInverse`: the generalized inverse.

## Main results

* `StieltjesFunction.generalizedInverse_le_iff`: the Galois connection
  `f.generalizedInverse y ≤ x ↔ y ≤ f x`.
* `StieltjesFunction.generalizedInverse_mono`: monotonicity.
* `StieltjesFunction.generalizedInverse_leftContinuous`: left-continuity.
* `StieltjesFunction.generalizedInverse_apply_self`: inversion when `f` is
  strictly monotone.

## References

* Embrechts, P. and Hofert, M., *A note on generalized inverses*, 2013
-/

open Set Filter

namespace StieltjesFunction

variable (f : StieltjesFunction ℝ)

/-! ### Definition -/

/-- The generalized inverse (quantile function) of a Stieltjes function `f`,
defined as `sInf {x : ℝ | y ≤ f x}`. This is the canonical left-continuous
inverse of a right-continuous monotone function. -/
noncomputable def generalizedInverse (y : ℝ) : ℝ :=
  sInf { x : ℝ | y ≤ f x }

theorem generalizedInverse_def (y : ℝ) :
    f.generalizedInverse y = sInf { x : ℝ | y ≤ f x } :=
  rfl

/-! ### Closedness of level sets -/

/-- The level set `{x | y ≤ f x}` of a Stieltjes function is closed. -/
theorem isClosed_le_preimage (y : ℝ) :
    IsClosed { x : ℝ | y ≤ f x } := by
  have h_open : IsOpen {x | f x < y} := by
    refine isOpen_iff_forall_mem_open.mpr ?_
    intro x hx
    obtain ⟨δ, hδ_pos, hδ⟩ :
        ∃ δ > 0, ∀ x', x < x' ∧ x' < x + δ → f x' < y := by
      have hrc := Metric.continuousWithinAt_iff.mp
        (f.right_continuous x) (y - f x) (sub_pos.mpr hx)
      obtain ⟨δ, hδ_pos, hδ⟩ := hrc
      exact ⟨δ, hδ_pos, fun x' hx' => by
        linarith [abs_lt.mp (hδ hx'.1.le
          (abs_lt.mpr ⟨by linarith, by linarith⟩))]⟩
    exact ⟨Ioo (x - δ) (x + δ),
      fun x' hx' => if hle : x' ≤ x
        then hx.out.trans_le' (f.mono hle)
        else hδ x' ⟨lt_of_not_ge hle, hx'.2⟩,
      isOpen_Ioo, ⟨by linarith, by linarith⟩⟩
  simpa only [compl_setOf, not_lt] using h_open.isClosed_compl

/-! ### The Galois connection -/

/-- If `{x | y ≤ f x}` is nonempty and bounded below, then the generalized
inverse belongs to the set: `y ≤ f (f.generalizedInverse y)`. -/
theorem generalizedInverse_mem
    (hne : ({ x : ℝ | y ≤ f x }).Nonempty)
    (hbdd : BddBelow { x : ℝ | y ≤ f x }) :
    y ≤ f (f.generalizedInverse y) :=
  (f.isClosed_le_preimage y).csInf_mem hne hbdd

/-- **Galois connection.** Under nonemptiness and boundedness hypotheses,
`f.generalizedInverse y ≤ x ↔ y ≤ f x`. This is the fundamental
characterization from which monotonicity, left-continuity, and inversion
all follow. -/
theorem generalizedInverse_le_iff
    (hne : ({ x : ℝ | y ≤ f x }).Nonempty)
    (hbdd : BddBelow { x : ℝ | y ≤ f x }) :
    f.generalizedInverse y ≤ x ↔ y ≤ f x :=
  ⟨fun h => (f.generalizedInverse_mem hne hbdd).trans (f.mono h),
   fun h => csInf_le hbdd h⟩

/-! ### Monotonicity -/

/-- The generalized inverse is monotone, assuming all level sets are
nonempty and bounded below. -/
theorem generalizedInverse_mono
    (hne : ∀ y, ({ x : ℝ | y ≤ f x }).Nonempty)
    (hbdd : ∀ y, BddBelow { x : ℝ | y ≤ f x }) :
    Monotone f.generalizedInverse := fun _ _ h =>
  (f.generalizedInverse_le_iff (hne _) (hbdd _)).mpr
    (h.trans (f.generalizedInverse_mem (hne _) (hbdd _)))

/-! ### Inversion for strictly monotone functions -/

/-- If `f` is strictly monotone, then `f.generalizedInverse (f x) = x`.
Strict monotonicity ensures `{t | f x ≤ f t} = Ici x`, whose infimum
is `x`. -/
theorem generalizedInverse_apply_self
    (hf : StrictMono f)
    (_hbdd : BddBelow { t : ℝ | f x ≤ f t }) :
    f.generalizedInverse (f x) = x := by
  have h_set : {t | f x ≤ f t} = Ici x :=
    Set.ext fun y => by simp +decide [hf.le_iff_le]
  unfold StieltjesFunction.generalizedInverse
  aesop

/-! ### Left-continuity -/

/-- The generalized inverse is left-continuous, assuming all level sets
are nonempty and bounded below. -/
theorem generalizedInverse_leftContinuous
    (hne : ∀ y, ({ x : ℝ | y ≤ f x }).Nonempty)
    (hbdd : ∀ y, BddBelow { x : ℝ | y ≤ f x }) (y : ℝ) :
    Tendsto f.generalizedInverse (nhdsWithin y (Iic y))
      (nhds (f.generalizedInverse y)) := by
  refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a ha => ?_⟩
  · -- Lower bound: find z < y with g(z) > a'.
    have h_lb :
        ∀ a < f.generalizedInverse y,
          ∃ z < y, f.generalizedInverse z > a := by
      intro a ha
      by_contra h_contra
      push Not at h_contra
      have h_fa : y ≤ f a :=
        le_of_forall_lt_imp_le_of_dense fun z hz =>
          (f.generalizedInverse_mem (hne z) (hbdd z)).trans
            (f.mono (h_contra z hz))
      linarith [(f.generalizedInverse_le_iff (hne y)
        (hbdd y)).mpr h_fa]
    obtain ⟨z, hz₁, hz₂⟩ := h_lb a' ha'
    filter_upwards [Icc_mem_nhdsLE hz₁] with b hb using
      hz₂.trans_le (f.generalizedInverse_mono hne hbdd hb.1)
  · -- Upper bound: g(z) ≤ g(y) < a for z ≤ y.
    filter_upwards [self_mem_nhdsWithin] with b hb using
      lt_of_le_of_lt
        (f.generalizedInverse_mono hne hbdd hb) ha

end StieltjesFunction

/-!
## Open design questions for mathlib discussion

1. **Naming**: `generalizedInverse` avoids collision with
   `Function.RightInverse` / `Function.LeftInverse` and matches the
   probability literature. Alternatives: `quantile`
   (too probability-specific), `leftContinuousInverse` (verbose).

2. **`EReal` vs `ℝ` codomain**: When `{x | y ≤ f x}` is empty, `csInf`
   on `ℝ` returns a junk value. An alternative design defines the
   generalized inverse as `ℝ → EReal` using `sInf` in `EReal`, which
   gives `⊤` for empty sets. This eliminates `Nonempty` / `BddBelow`
   hypotheses but changes the codomain. For CDF applications (where the
   hypotheses are automatic), the `ℝ`-valued version suffices.

3. **Hypothesis bundling**: The `Nonempty` and `BddBelow` hypotheses
   appear on many lemmas. For CDFs, both follow from `0 < p ∧ p ≤ 1`. A
   predicate `f.HasGeneralizedInverse` bundling these could reduce
   boilerplate, but may be over-engineering.

4. **Right-continuous variant**: `sInf {x | y < f x}` (strict inequality)
   gives a right-continuous inverse. It may be useful to define both.

5. **Generalization to `StieltjesFunction R`**: The definition and Galois
   connection generalize to any `ConditionallyCompleteLinearOrder R` with
   `OrderTopology R`. Left-continuity requires `DenselyOrdered R`. We
   restrict to `ℝ` for simplicity.
-/
