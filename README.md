# lopt-entropy-formal

Formal verification of NIST SP 800-90B min-entropy estimators in [Lean 4](https://lean-lang.org/),
built against [mathlib4](https://github.com/leanprover-community/mathlib4).

Companion to [lopt](https://github.com/Xylem-Group/lopt), an entropy
provisioning service. Theorems here are intended for eventual upstream
contribution to mathlib where applicable.

## Status

| Estimator (NIST SP 800-90B §6) | Lean | Notes |
|---|---|---|
| §6.3.1 Most Common Value (MCV) | ✅ Complete, `sorry`-free | `LoptEntropy/Entropy/MCV.lean`. Deterministic core fully proved; probabilistic wrapper takes the normal-approximation event as hypothesis pending a standard normal CDF in mathlib. |
| §6.3.2 Markov | — | Planned |
| §6.3.3 Compression | — | Planned |
| Composition (min of estimators ⇒ bound) | — | Planned, after the three estimators are individually formalized |

The probabilistic wrapper of MCV currently axiomatizes the normal-
approximation event because mathlib does not yet provide a packaged
standard normal CDF Φ and its inverse Φ⁻¹. Discussion of the path
forward is on Lean Zulip at
[#mathlib4 → Standard normal CDF Φ — status in mathlib?](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Standard.20normal.20CDF.20.CE.A6.20.E2.80.94.20status.20in.20.20.20mathlib.3F).

## Build

```sh
lake build
```

Pinned mathlib version is fixed in `lake-manifest.json`. CI on every
PR and push to `trunk` runs `lake build`; green means all theorems
compile clean against the pinned mathlib commit.

## Why this exists

The MCV estimator is a runtime check in
[lopt](https://github.com/Xylem-Group/lopt)'s TRNG service. Its claim
("the empirical maximum-frequency bound, padded by a confidence
margin, is a conservative lower bound on min-entropy") is one of the
load-bearing audit-grade claims of that service. A formal Lean proof
turns "the SP 800-90B reference implementation says so" into "the
theorem is checked by Lean against mathlib."

This is the first slice of an entropy-chain formalization. The
remaining estimators, the composition theorem, and the conditioning
function's min-entropy preservation are the natural follow-ups.

## Mathlib contribution path

Theorems that generalize beyond the lopt use case are intended for
upstream contribution to mathlib. The plan, per Lean Zulip dialogue:

1. Prototype here against pinned mathlib
2. Discuss design on `#mathlib4` (especially API and naming
   conventions) before opening a mathlib PR
3. Open the mathlib PR with the smallest possible scope, citing
   this repo as the originating context

Pull requests to *this* repo are welcome from anyone; PR review and
merge authority rests with the Xylem Group maintainer line.

## How this work was produced

The Most Common Value formalization was produced by
[Harmonic's Aristotle](https://arxiv.org/abs/2510.01346), an automated
theorem prover for Lean 4. Each contribution is reviewed by a human
before merge. Future contributions may come from Aristotle, from
mathlib community members, or from direct human work — the source is
disclosed in the commit message of each PR.

## License

Apache License 2.0 — see [`LICENSE`](LICENSE).

Choice of Apache 2.0 (vs MIT or GPL) matches mathlib4's own license,
keeps upstream contribution paths frictionless, and provides the
explicit patent grant + termination clause appropriate for
crypto-adjacent work.

## Citation

If this work supports a paper, please cite as:

```
@misc{lopt-entropy-formal,
  author       = {Xylem Group},
  title        = {lopt-entropy-formal: Formal verification of NIST SP 800-90B estimators in Lean 4},
  year         = {2026},
  howpublished = {\url{https://github.com/Xylem-Group/lopt-entropy-formal}},
}
```

Specific theorems should additionally cite the relevant Lean file
path (e.g. `LoptEntropy/Entropy/MCV.lean`).

## Related work

- [Harmonic's Aristotle](https://arxiv.org/abs/2510.01346) — the
  theorem prover used to produce the initial MCV formalization
- [NIST SP 800-90B (January 2018)](https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90B.pdf) — the
  source standard
- [mathlib4](https://github.com/leanprover-community/mathlib4) — the
  upstream Lean math library
- [lopt](https://github.com/Xylem-Group/lopt) — the consumer
  entropy-provisioning service that motivated this work
