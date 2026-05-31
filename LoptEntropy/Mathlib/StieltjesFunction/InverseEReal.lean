/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.Basic

/-!
# EReal-valued generalized inverse of a Stieltjes function

We define the generalized inverse (quantile function) of a `StieltjesFunction ℝ`,
valued in `EReal` so that it is **total and hypothesis-free**: no `Nonempty` or
`BddBelow` conditions are needed anywhere.

## Main definitions

* `StieltjesFunction.egInverse`: the EReal-valued generalized inverse (quantile)
  of a Stieltjes function `f`, defined as the infimum of `{x : ℝ | y ≤ f x}` cast
  into `EReal`.

## Main results

* `egInverse_le_iff`: the load-bearing unconditional characterization
  `f.egInverse y ≤ ↑x ↔ y ≤ f x`.
* `egInverse_mono`: `f.egInverse` is monotone.
* `egInverse_eq_top_iff`: `f.egInverse y = ⊤ ↔ {x | y ≤ f x} = ∅`.
* `egInverse_eq_bot_iff`: `f.egInverse y = ⊥ ↔ ¬BddBelow {x | y ≤ f x}`.
* `egInverse_apply_self`: for strictly monotone `f`, `f.egInverse (f x) = ↑x`.
* `egInverse_leftContinuous`: left-continuity of the quantile function.
* Real-valued specialization lemmas for `toReal` round-trips.

## Implementation notes

The definition uses `sInf` on `EReal`, which is a `CompleteLinearOrder`, so
`sInf ∅ = ⊤` and all infimum lemmas are unconditional. The level set
`{x : ℝ | y ≤ f x}` is closed (complement of the open set `{x | f x < y}`,
which is open by monotonicity and right-continuity of `f`).
-/

noncomputable section

open Set

namespace StieltjesFunction

/-! ### Closedness of level sets -/

/-- The sub-level set `{x | f x < y}` is open for a Stieltjes function. -/
theorem isOpen_lt_preimage (f : StieltjesFunction ℝ) (y : ℝ) :
    IsOpen {x : ℝ | f x < y} := by
  rw [isOpen_iff_forall_mem_open]
  intro x₀ hx₀
  simp only [mem_setOf_eq] at hx₀
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousWithinAt_iff.mp (f.right_continuous x₀)
    (y - f x₀) (sub_pos.mpr hx₀)
  refine ⟨Iio (x₀ + δ), fun t ht => ?_, isOpen_Iio, mem_Iio.mpr (by linarith)⟩
  simp only [mem_setOf_eq, mem_Iio] at *
  by_cases htx : x₀ ≤ t
  · have hdist : dist t x₀ < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htx)]; linarith
    have := hδ (mem_Ici.mpr htx) hdist
    rw [Real.dist_eq] at this
    linarith [abs_lt.mp this]
  · push_neg at htx
    exact lt_of_le_of_lt (f.mono htx.le) hx₀

/-- The super-level set `{x | y ≤ f x}` is closed for a Stieltjes function. -/
theorem isClosed_le_preimage (f : StieltjesFunction ℝ) (y : ℝ) :
    IsClosed {x : ℝ | y ≤ f x} := by
  rw [show {x : ℝ | y ≤ f x} = {x : ℝ | f x < y}ᶜ from by ext x; simp [not_lt]]
  exact (isOpen_lt_preimage f y).isClosed_compl

/-! ### Definition of `egInverse` -/

/-- The EReal-valued generalized inverse (quantile function) of a Stieltjes function.
Defined as the infimum of the image of the level set `{x : ℝ | y ≤ f x}` under the
coercion `ℝ → EReal`. This is total: when the level set is empty, `egInverse` returns `⊤`;
when it is unbounded below, it returns `⊥`. -/
noncomputable def egInverse (f : StieltjesFunction ℝ) (y : ℝ) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | y ≤ f x})

/-! ### The load-bearing iff -/

/-- **Unconditional** characterization of `egInverse`: no `Nonempty` or `BddBelow`
hypotheses are required, thanks to `EReal` being a complete lattice. -/
theorem egInverse_le_iff (f : StieltjesFunction ℝ) {y x : ℝ} :
    f.egInverse y ≤ (x : EReal) ↔ y ≤ f x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose! h
    have h_lt : ∀ t, y ≤ f t → x < t :=
      fun t ht => not_le.mp fun h' => h.not_ge <| ht.trans <| f.mono h'
    by_cases h_empty : {t : ℝ | y ≤ f t} = ∅
    · unfold StieltjesFunction.egInverse; aesop
    · obtain ⟨a, ha⟩ : ∃ a, IsLeast {t : ℝ | y ≤ f t} a := by
        have h_closed : IsClosed {t : ℝ | y ≤ f t} := isClosed_le_preimage f y
        refine ⟨_, h_closed.csInf_mem ?_ ?_, fun t ht => ?_⟩
        · exact Set.nonempty_iff_ne_empty.2 h_empty
        · exact ⟨x, fun t ht => le_of_lt (h_lt t ht)⟩
        · exact csInf_le ⟨x, fun t ht => le_of_lt (h_lt t ht)⟩ ht
      exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr (h_lt a ha.1))
        (le_csInf (Set.Nonempty.image _ <| Set.nonempty_iff_ne_empty.mpr h_empty) <|
          Set.forall_mem_image.mpr fun t ht => EReal.coe_le_coe_iff.mpr <| ha.2 ht)
  · exact sInf_le ⟨x, h, rfl⟩

/-! ### Downstream lemmas -/

/-- `egInverse` is monotone: larger `y` gives a larger (or equal) quantile. -/
theorem egInverse_mono (f : StieltjesFunction ℝ) : Monotone f.egInverse := by
  intro y₁ y₂ hy₁₂
  apply sInf_le_sInf
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, le_trans hy₁₂ ht, rfl⟩

/-- `egInverse y = ⊤` exactly when no real `x` satisfies `y ≤ f x`. -/
theorem egInverse_eq_top_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y = ⊤ ↔ {x : ℝ | y ≤ f x} = ∅ := by
  simp [StieltjesFunction.egInverse, Set.ext_iff]

/-- `egInverse y = ⊥` exactly when the level set `{x | y ≤ f x}` is not bounded below. -/
theorem egInverse_eq_bot_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y = ⊥ ↔ ¬BddBelow {x : ℝ | y ≤ f x} := by
  constructor
  · contrapose!
    intro h_bdd_below
    obtain ⟨b, hb⟩ := h_bdd_below
    exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe b)
      (le_sInf (by rintro _ ⟨t, ht, rfl⟩; exact EReal.coe_le_coe_iff.mpr (hb ht))))
  · intro h
    rw [StieltjesFunction.egInverse, sInf_eq_bot]
    intro b hb
    induction b using EReal.rec with
    | bot => exact absurd hb (lt_irrefl _)
    | coe r =>
      obtain ⟨t, ht, htr⟩ := not_bddBelow_iff.mp h r
      exact ⟨(t : EReal), ⟨t, ht, rfl⟩, EReal.coe_lt_coe_iff.mpr htr⟩
    | top =>
      have : {x : ℝ | y ≤ f x}.Nonempty := by
        by_contra hempty
        rw [Set.not_nonempty_iff_eq_empty] at hempty
        exact h (hempty ▸ bddBelow_empty)
      obtain ⟨t, ht⟩ := this
      exact ⟨(t : EReal), ⟨t, ht, rfl⟩, EReal.coe_lt_top t⟩

/-- For a strictly monotone Stieltjes function, the generalized inverse at `f x` is `x`. -/
theorem egInverse_apply_self (f : StieltjesFunction ℝ) (hf : StrictMono f) (x : ℝ) :
    f.egInverse (f x) = (x : EReal) := by
  refine le_antisymm ?_ ?_
  · exact (egInverse_le_iff f).mpr le_rfl
  · exact le_sInf (by rintro _ ⟨t, ht, rfl⟩; exact EReal.coe_le_coe_iff.mpr (hf.le_iff_le.mp ht))

/-! ### Real-valued specialization -/

/-- The level set is nonempty iff `egInverse y ≠ ⊤`. -/
theorem egInverse_ne_top_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y ≠ ⊤ ↔ (∃ x : ℝ, y ≤ f x) := by
  rw [Ne, egInverse_eq_top_iff]
  simp only [Set.eq_empty_iff_forall_notMem, mem_setOf_eq, not_forall, not_not]

/-- The level set is bounded below iff `egInverse y ≠ ⊥`. -/
theorem egInverse_ne_bot_iff (f : StieltjesFunction ℝ) {y : ℝ} :
    f.egInverse y ≠ ⊥ ↔ BddBelow {x : ℝ | y ≤ f x} := by
  rw [← not_iff_not, not_not, egInverse_eq_bot_iff]

/-- When `egInverse y` is finite, `toReal` round-trips correctly. -/
theorem egInverse_toReal (f : StieltjesFunction ℝ) {y : ℝ}
    (htop : f.egInverse y ≠ ⊤) (hbot : f.egInverse y ≠ ⊥) :
    ((f.egInverse y).toReal : EReal) = f.egInverse y :=
  EReal.coe_toReal htop hbot

/-- When the level set is nonempty and bounded below, `y ≤ f (egInverse y).toReal`. -/
theorem le_apply_egInverse_toReal (f : StieltjesFunction ℝ) {y : ℝ}
    (htop : f.egInverse y ≠ ⊤) (hbot : f.egInverse y ≠ ⊥) :
    y ≤ f (f.egInverse y).toReal := by
  have h := egInverse_toReal f htop hbot
  exact (egInverse_le_iff f).mp (h ▸ le_refl _)

/-! ### Left-continuity -/

/-- The generalized inverse is **left-continuous**: as a function `ℝ → EReal` it is
continuous within `Set.Iic y` at every point `y`. This is the classical left-continuity
of a quantile function, here unconditional thanks to the `EReal` codomain. -/
theorem egInverse_leftContinuous (f : StieltjesFunction ℝ) (y : ℝ) :
    ContinuousWithinAt f.egInverse (Set.Iic y) y := by
  apply tendsto_order.2 ⟨?_, ?_⟩
  · intro a' ha'
    obtain ⟨r, hr⟩ : ∃ r : ℝ, a' < r ∧ r < f.egInverse y := EReal.exists_between_coe_real ha'
    have h_fr_lt_y : f r < y := by
      contrapose! hr
      exact fun _ => (egInverse_le_iff f).2 hr
    rw [eventually_nhdsWithin_iff]
    filter_upwards [lt_mem_nhds h_fr_lt_y] with x hx₁ hx₂ using
      lt_of_lt_of_le hr.1 (le_of_not_gt fun hx₃ => by
        linarith [(egInverse_le_iff f).1 hx₃.le])
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact lt_of_le_of_lt (f.egInverse_mono hb) ha

end StieltjesFunction

end

/-!
## Open design questions

1. **Naming**: `egInverse` vs `generalizedInverse` vs `quantile` — the `e` prefix
   signals the EReal codomain; `g` stands for "generalized". A final name should be
   chosen in coordination with the existing `ℝ`-valued `gInverse` in `Inverse.lean`.

2. **Galois connection**: once `f` is extended to `EReal → EReal` (sending `⊥ ↦ ⊥`
   and `⊤ ↦ ⊤`), the pair `(egInverse f, f_extended)` should form a
   `GaloisConnection`. This is a natural follow-up.
-/
