# Reply to Etienne Marion on Zulip

**Stream:** #mathlib4
**Topic:** Standard normal CDF Φ — status in mathlib?
**Status:** Draft — for a human to post (do not auto-send)
**Replies to:** Etienne's pointer ("you'd have to define it for a general
`StieltjesFunction` first")

Modeled on the physlib/Joseph contribution that landed: small slice, ask
placement + concerns *before* the PR, be transparent about how it was
produced, stay responsive to house style. Post as-is or lightly edit.

---

## Message

Went ahead and made some progress, open to your thoughts on this:

We built an `EReal`-valued generalized inverse for a general docs#StieltjesFunction — the quantile construction `f.egInverse y = sInf {x | y ≤ f x}`, valued in `EReal` so it is total — sorry-free against current mathlib. The file is public: [`InverseEReal.lean`](https://github.com/Xylem-Group/lopt-entropy-formal/blob/trunk/LoptEntropy/Mathlib/StieltjesFunction/InverseEReal.lean). The properties that make it usable as a CDF inverse:

- `egInverse_le_iff` — the Galois connection
  `f.egInverse y ≤ ↑x ↔ y ≤ f x`, **unconditional** (no `Nonempty`/`BddBelow`);
  the load-bearing one, the rest fall out of it
- `egInverse_mono` — monotonicity
- `egInverse_leftContinuous` — left-continuity (the quantile function is
  left-continuous, not right; we note this explicitly)
- `egInverse_apply_self` — inversion when `f` is strictly monotone
- `egInverse_eq_top_iff` / `egInverse_eq_bot_iff` and a `toReal`
  specialization — finiteness characterizations so the CDF case lands back
  on `ℝ`

Before we open a PR we'd rather align on design here, since this is your
house. A few genuine open questions:

1. **Naming.** Working name `egInverse` (the `e` flags the `EReal` codomain). `generalizedInverse` matches the probability literature and avoids collision with `Function.LeftInverse` / `Function.RightInverse`; `quantile` felt too probability-specific for something sitting next to docs#StieltjesFunction. Preference on the name, and on how to signal the `EReal` codomain?

2. **Codomain: `ℝ` vs `EReal`** — we went `EReal`, and would value a sanity check against your conventions. Over `ℝ` the inverse needs `Nonempty` + `BddBelow` guards on every lemma to fence off the `sInf`-junk on the empty / unbounded-below level sets; over `EReal` those rows become `⊤` / `⊥` (the correct $$\pm\infty$$ quantiles) and the function is total. Concretely the Galois connection `f.egInverse y ≤ ↑x ↔ y ≤ f x` holds *unconditionally* for all `y x : ℝ` — the level set is a closed up-set, so it is $$[a,\infty)$$, $$\varnothing$$, or $$\mathbb{R}$$, and the degenerate cases satisfy the iff vacuously — whereas over `ℝ` it is hypothesis-encumbered. That, plus the `ENNReal` / `EReal`-everywhere convention in the measure-theory neighbourhood, points to `EReal` as the right primitive, with a `toReal` specialization for the CDF case (where $$0 < p \le 1$$ makes finiteness automatic) so $$\Phi^{-1}$$ still lands on `ℝ` downstream. Does that sit right next to the existing docs#StieltjesFunction / docs#ProbabilityTheory.cdf API, or is there a local convention you'd rather we match?

3. **Placement.** Natural home looks like alongside `Mathlib/MeasureTheory/Measure/Stieltjes.lean` — either a new `Stieltjes/Inverse.lean` or a section in the existing file. Where would you want it to sit?

On provenance, since I know it matters here: the proof was drafted with Harmonic's Aristotle and then human-reviewed line by line on our side — the bar we're holding is "reads like a real mathlib file and we can defend every step", not "here's what the prover emitted". The file linked above is public, so you can read it directly, and we'll rewrite to whatever naming/style you land on before anything goes to a PR.

We'd keep this first slice to just the general inverse and its basic properties. Two things deliberately left for later: (a) bundling it as a genuine `GaloisConnection` once `f` is extended to `EReal → EReal`, and (b) the standard-normal $$\Phi$$ / $$\Phi^{-1}$$ instantiation that started this thread, on top of docs#ProbabilityTheory.gaussianReal. Both after the general construction has a home — no desire to land a sprawling stack at once.

We're a small group with limited Lean seniority, so we'd be staging this over weeks rather than rapid-fire — we'd much rather get one slice aligned than churn a big PR.

---

## Post-submission notes (for the human submitter)

- Reply *in the existing topic*, threaded under Etienne's message.
- If Etienne (or Rémy Degenne, who owns adjacent CDF work) answers the
  naming/codomain questions → settle those, update `InverseEReal.lean`
  accordingly, *then* open the mathlib PR. Not before.
- Offer the gist/branch only after someone asks, or attach it if the reply
  invites it — don't front-load a link wall.
- If it goes quiet for 5–7 days, that's a busy community, not a no. One
  nudge at the two-week mark is the etiquette ceiling.
- The PR itself is a human action on a human's leanprover-community
  account — `lopt`/Aristotle drafts the artifact and this message; the
  human owns the PR and the conversation.

Drafted by `lopt` for the lopt-mathlib bridge, 2026-05-30.
