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

Thanks Etienne — that pointer was exactly the right framing, so we took a
run at it. We prototyped a generalized inverse for a general
`StieltjesFunction` (the quantile-function construction
`f.generalizedInverse y = sInf {x | y ≤ f x}`), sorry-free against current
mathlib, with the four properties that make it usable as a CDF inverse:

- `generalizedInverse_le_iff` — the Galois connection
  `f.generalizedInverse y ≤ x ↔ y ≤ f x` (the load-bearing one; the rest
  fall out of it)
- `generalizedInverse_mono` — monotonicity
- `generalizedInverse_leftContinuous` — left-continuity (the quantile
  function is left-continuous, not right; we note this explicitly)
- `generalizedInverse_apply_self` — inversion when `f` is strictly monotone

Before we open a PR we'd rather align on design here, since this is your
house. A few genuine open questions:

1. **Naming.** We went with `generalizedInverse` (matches the probability
   literature, avoids collision with `Function.LeftInverse`/`RightInverse`).
   `quantile` felt too probability-specific for something living next to
   `StieltjesFunction`. Preference?

2. **Codomain: `ℝ` vs `EReal` — we lean `EReal`, and would value a sanity
   check.** Our reasoning: over `ℝ` the inverse needs `Nonempty` +
   `BddBelow` guards on every lemma to fence off the `sInf`-junk on the
   empty / unbounded-below level sets, whereas over `EReal` those rows
   become `⊤` / `⊥` (the correct `±∞` quantiles) and the function is total.
   Concretely the Galois connection `g y ≤ x ↔ y ≤ f x` holds
   *unconditionally* over `EReal` for all `y x : ℝ` (the level set is a
   closed up-set, so it's `[a,∞)` / `∅` / `ℝ`, and the degenerate cases
   satisfy the iff vacuously), but is hypothesis-encumbered over `ℝ`. That,
   plus the `ENNReal`/`EReal`-everywhere convention in the measure-theory
   neighbourhood, points to `EReal` as the right primitive — with a
   `toReal` specialization for the CDF case (where `0 < p ≤ 1` makes
   finiteness automatic), so Φ⁻¹ still lands on `ℝ` downstream. Does that
   sit right next to the existing `Stieltjes` / `CDF` API, or is there a
   local convention you'd rather we match?

3. **Hypothesis bundling.** The `Nonempty`/`BddBelow` pair recurs across the
   lemmas. A bundled predicate would cut boilerplate but might be
   over-engineering. Your call on whether that's worth it.

Full transparency on provenance, since I know it matters here: the proof
was drafted with Harmonic's Aristotle and then human-reviewed line by line
on our side — we're treating "reads like a real mathlib file and we can
defend every step" as the bar, not "here's what the prover emitted." Happy
to share the file (gist or branch) for a read, and to rewrite to whatever
naming/style you land on before anything goes to a PR.

Scope-wise we'd keep this to just the general inverse. The standard-normal
Φ / Φ⁻¹ instantiation that started this thread would be a separate,
later slice once the general construction has a home — no desire to land a
sprawling stack at once.

One thing we're realistic about: we're a small group with limited Lean
seniority, so we'd be staging this over weeks, not rapid-fire. We'd much
rather get one slice aligned than churn a big PR.

---

## Post-submission notes (for the human submitter)

- Reply *in the existing topic*, threaded under Etienne's message.
- If Etienne (or Rémy Degenne, who owns adjacent CDF work) answers the
  naming/codomain questions → settle those, update `Inverse.lean`
  accordingly, *then* open the mathlib PR. Not before.
- Offer the gist/branch only after someone asks, or attach it if the reply
  invites it — don't front-load a link wall.
- If it goes quiet for 5–7 days, that's a busy community, not a no. One
  nudge at the two-week mark is the etiquette ceiling.
- The PR itself is a human action on a human's leanprover-community
  account — `lopt`/Aristotle drafts the artifact and this message; the
  human owns the PR and the conversation.

Drafted by `lopt` for the lopt-mathlib bridge, 2026-05-30.
