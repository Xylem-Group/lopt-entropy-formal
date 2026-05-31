# mathlib PR readiness — StieltjesFunction.generalizedInverse

What stands between `LoptEntropy/Mathlib/StieltjesFunction/Inverse.lean`
(green on *our* CI) and a clean PR to `leanprover-community/mathlib4`.

Our `lean-action` CI runs `lake build` against the mathlib olean cache, so
it proves the file **compiles** sorry-free on v4.30.0. mathlib CI adds gates
we don't run — style linter, `runLinter` (environment linters), and human
reviewers who hold core files to a higher bar than a downstream repo.
"Green here ≠ green there." This is the list to clear *before* opening the
PR, ordered by how likely it is to draw a comment.

## Must-fix before PR

1. **Author attribution (the crux).** Header currently reads
   `Copyright (c) 2025 Harmonic` / `Authors: Harmonic`. mathlib requires
   real human contributor name(s) on the `Authors:` line — the person who
   stands behind the file and answers review. This is also where the
   AI-provenance question resolves cleanly: the human author is the human
   author; the Aristotle assist is disclosed on Zulip, not laundered. Set
   this to the actual contributor before PR. (Copyright year → 2026.)

2. **Unused hypothesis `_hbdd` in `generalizedInverse_apply_self`**
   (line 133). It's underscore-prefixed because the proof doesn't use it.
   A reviewer will immediately ask "why does this lemma take a hypothesis
   it never uses?" Either drop it (if the proof truly doesn't need it —
   it appears not to, since `{t | f x ≤ f t} = Ici x` and `sInf (Ici x) = x`
   unconditionally) or, if some downstream caller wanted symmetry, that's
   not a good enough reason for mathlib. Default: **remove it.**

3. **`simp +decide` (line 136).** mathlib discourages `decide` inside
   `simp` — it's flagged in review and can trip the `decide`-related lint
   in core files. Rewrite without it: the goal is
   `{t | f x ≤ f t} = Ici x` via `hf.le_iff_le`, which should close with a
   plain `simp [hf.le_iff_le]` / `Set.ext` + `mem_Ici` + `hf.le_iff_le`,
   no `+decide`. Confirm it still builds after removing.

## Likely review nits (clear if cheap)

4. **`aesop` finisher (line 138).** Accepted in mathlib, but for a short
   core lemma some reviewers prefer an explicit term/tactic so the proof is
   legible and robust to `aesop` changes. Low priority; leave unless asked,
   but be ready to unfold it.

5. **Line length / style linter.** mathlib's text linter enforces ≤ 100
   columns, no trailing whitespace, import block formatting, and a module
   docstring (we have a good one). Run `lake exe lint-style` once the file
   is in a mathlib checkout; fix any column overflows in the multi-line
   proofs (the `filter_upwards`/`refine` blocks are the risk).

6. **`runLinter` environment lints.** `docBlame` wants a docstring on every
   declaration — we have them on the defs/theorems; double-check
   `generalizedInverse_def` and `isClosed_le_preimage` aren't missing one.
   `simpNF` — none of ours are `@[simp]`, so low risk, but if any get
   tagged later they must be in simp-normal form.

## Design questions that belong on Zulip first (not PR-blockers, but settle them)

7. **`ℝ` vs `EReal` codomain** — the `Nonempty`/`BddBelow` hypothesis
   proliferation vs. a junk-free `EReal` version. Etienne/Rémy will have a
   convention preference; pick the one they bless rather than guessing and
   reworking. (Captured in the file's footer + the Zulip reply.)

8. **Naming** `generalizedInverse` and the lemma names — align on Zulip.

9. **Placement** — file path inside mathlib. Natural home is alongside
   `Mathlib/MeasureTheory/Measure/Stieltjes.lean` (e.g. a new
   `Stieltjes/Inverse.lean` or a section in the existing file). Ask, like
   the physlib placement question.

## Process gates (mathlib-specific, not in our control)

- PR is authored on a human's `leanprover-community`-linked GitHub account.
- mathlib requires the contributor to be added to the
  `mathlib4` contributors / sign the CLA-equivalent (the `Authors:` line
  + the maintainer-merge flow).
- mathlib CI is heavy (full build + linters + `bench`); expect longer turnaround
  than our 1m39s. Don't force-push churn; let it run.
- Merge is via mathlib's `bors`/maintainer-merge queue, not a direct merge.

## Sequence (don't skip to the PR)

1. Post the Zulip reply to Etienne (`zulip/reply-to-etienne-stieltjes-inverse.md`).
2. Settle naming + ℝ/EReal + placement from his answer.
3. Apply must-fixes 1–3 here, re-verify build on our CI.
4. *Then* open the mathlib PR, human-authored, with the design alignment
   linked from the thread.

The Gaussian Φ / Φ⁻¹ instantiation is a **separate, later** slice — only
after this general construction has a home.

Drafted by `lopt`, 2026-05-30. Compilation verified via lopt-entropy-formal
trunk CI (run 26660515429, v4.30.0).
