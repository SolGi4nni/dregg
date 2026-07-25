/-
# `Dregg2.Circuit.CorrelatedAgreement` — the aggregator root for the correlated-agreement formalization.

This module exists so the seven-file `CorrelatedAgreement/` subtree is reachable from `Dregg2.lean`
through a SINGLE import line. `Dregg2.lean` is a heavily-contended shared file; a previous attempt
rooted the modules individually and the lines were dropped by subsequent commits, leaving the whole
subtree outside the default `lake build` target — i.e. outside CI, free to rot, and not covered by any
"full build green" claim. One line has a far smaller conflict surface than seven.

The subtree formalizes UNIQUE-DECODING-regime correlated agreement for Reed–Solomon codes
(BCIKS20 Thm 4.1 / Kopparty et al. 2025), the mathematical keystone of the FRI extractor's
`DecodedLdtLink` residual. Plan and rung DAG: `docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md`.

Rungs, in dependency order:

* **L0** `Scaffolding` — `RScode` as a `Submodule` via `evalOn`, `closeN`, `interleavedClose`, and the
  unique-decoding chain from Mathlib `card_roots'` (`rs_min_distance`, `rs_unique_decoding`,
  `rs_ball_subsingleton`).
* **L1** `BerlekampWelch` — the univariate Berlekamp–Welch facts. Note `bw_naive_converse_false`: the
  naive "system solvable ⟺ close" is FALSE and is refuted here; the true statement carries the decoding
  certificate `A ∣ B ∧ deg (B / A) < k`.
* **L2** `Interpolation` — bivariate interpolation over `F(Z)` via a Cramer engine whose kernel entries
  are signed minors over `F[Z]` ITSELF (no fraction field — a bare rank-over-`F(Z)` argument cannot give
  the degree bound the Polishchuk–Spielman budget needs), plus `interleavedClose_of_good_challenges`,
  the end-to-end composition through `Dregg2.PS.polishchuk_spielman` (`Dregg2/ForMathlib/`) into L4.
* **L4** `Collinearity` — degree control and the collinearity double count (Kopparty Lemma 2.4), curve
  form native with the line case as the `m = 2` wrapper; the bound is proven ATTAINED and the lossless
  threshold `(m−1)(e+1) < |Z|` proven sharp (it cannot be relaxed to `≤`).
* **L5/L6** `Theorems` — the target Props `CorrelatedAgreementPairUDParam` / `CorrelatedAgreementCurveUDParam`,
  proven in the exact shape `Interface` consumes, in the classical (`(m+1)r + k ≤ n`) regime, with the
  PS regime covering the full UD radius at a higher threshold. The residual band between them is
  machine-checked to cost under 1.2 bits.
* `Interface` — the pinned consumer interface: `ud_tower_far_survival`, the round-by-round/FS soundness
  statement over the pre-existing `Strategy`/`fsRun`/`winProb` layer, with correlated agreement as an
  explicit hypothesis.
* `DecimLiftDischarge` — `DecimLift` discharged from the landed `FriSetupTower`, and
  `ud_tower_far_survival_discharged`.

Honest scope for the subtree as a whole: these are theorems about Reed–Solomon codes and about the
honest fold chain under a uniform oracle. They do NOT by themselves make the FRI apex
adversary-quantified — `Strategy` is instantiated at `honestStrategy` throughout the survival theorems,
and the apex (`StarkSound` / `FriLdtExtractV3`) still quantifies over supplied proofs.
-/
import Dregg2.Circuit.CorrelatedAgreement.Scaffolding
import Dregg2.Circuit.CorrelatedAgreement.BerlekampWelch
import Dregg2.Circuit.CorrelatedAgreement.Interpolation
import Dregg2.Circuit.CorrelatedAgreement.Collinearity
import Dregg2.Circuit.CorrelatedAgreement.Interface
import Dregg2.Circuit.CorrelatedAgreement.DecimLiftDischarge
import Dregg2.Circuit.CorrelatedAgreement.Theorems
