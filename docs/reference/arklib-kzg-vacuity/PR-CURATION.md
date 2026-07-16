# PR curation — what a clean ArkLib PR carries, and what stays on the wip branch

**Recommend, do not delete.** Nothing here is removed from `emberian/ArkLib@kzg-vacuity-wip`
or from this reference directory. This is the manifest of what a *curated* PR branch would
contain, built from the wip corpus. ember + the integrator build the curated branch from it.

Corpus: 14 Lean modules (`ArkLib/Scratch/KzgVacuity/`) + the `Binding.lean` fix + ~18 docs.
Checked against ArkLib `d72f8392`, Lean `v4.31.0`. A good EF PR is defined as much by what it
leaves out: the load-bearing spine, none of our internal working notes, and above all **not**
the disclosure-letter drafted *to* them.

---

## A. Lean modules — keep/drop per file

The dependency closure settles most of this mechanically. `GgmEndToEnd.lean`'s own imports and
`open`s pull exactly `GgmCandidate, GgmAdaptive, GgmRandomEncoding, GgmArkLibTransport,
GgmEmbed, GgmProbThreading, GgmDegreeDischarge` — and pointedly **not** `GgmDegreeInvariant`,
`AgmSound`, `AlgebraicTSdh`, or `KzgQDlogVacuity`. The capstone defines its own minimal spine.

| File | Verdict | Justification |
|---|---|---|
| **`KzgVacuity.lean`** | **KEEP (spine)** | The finding. t-SDH + ARSDH vacuity against ArkLib's real assumptions; canaried. Every scope includes it (except pure MINIMAL). |
| **`RepairSurvives.lean`** | **KEEP (spine)** | Proves the fix survives the *exact* attack (`repair_survives_attack`). Without it the de-vacuation is an unwitnessed refactor. |
| **`GgmCandidate.lean`** | **KEEP (spine, FULL)** | Static Schwartz–Zippel core `(D+1)/(p−1)`, reused by `GgmAdaptive`/`GgmRandomEncoding`. Not exploratory despite the `candidates/` path — it is a load-bearing dependency of the capstone. |
| **`GgmAdaptive.lean`** | **KEEP (spine, FULL)** | The adaptive `q`-query bound; identical-until-bad hybrid proved by induction. The run model (`runAux`/`runTable`) the rest of the chain builds on. |
| **`GgmRandomEncoding.lean`** | **KEEP (spine, FULL)** | The Shoup all-pairs quadratic count; supplies `rand_encoding_bound_D_of_run` to the capstone. |
| **`GgmDegreeDischarge.lean`** | **KEEP (spine, FULL)** | Discharges the degree invariant on the *real* linear oracle (`hdeg_out_of_run`, `hdeg_handles_of_run`). This is what makes the capstone hypothesis-free on the critical path. |
| **`GgmArkLibTransport.lean`** | **KEEP (spine, FULL)** | Field→group transport against ArkLib's real `Groups.tSdhCondition` (`groupWinSet_eq_realWinSet`). |
| **`GgmProbThreading.lean`** | **KEEP (spine, FULL)** | Collapses ArkLib's `OptionT ProbComp`/`StateT QueryCache` game to `card/(p−1)` (`experiment_eq_count`). |
| **`GgmEmbed.lean`** | **KEEP (spine, FULL)** | Constructs the generic-restricted adversary (`embed`, `embed_run_correspondence`) — the class the capstone quantifies over. |
| **`GgmEndToEnd.lean`** | **KEEP (spine, FULL)** | The capstone `tSdh_ggm_sound` / `tSdh_ggm_sound_lt_one` on ArkLib's real `tSdhExperiment`. |
| `GgmDegreeInvariant.lean` | **DROP from PR** | The `buildPaired` **peer** model. Superseded on the critical path by `GgmDegreeDischarge` (which discharges the degree facts on the actual `runTable`). Nothing in the spine imports it; the capstone does not `open` it. It is a documented *off-path ceiling* for a hypothetical pairing-endowed (`δ = 2D`) adversary — real, but dead weight for a reviewer of the deployed bound. Stays on wip; belongs in the paper, not the PR. |
| `AlgebraicTSdh.lean` | **DROP from PR** | Alternative fix approach (panel). The probability-level anchor for the *static algebraic* case — a sibling to GGM-static. Genuinely nice, but redundant once `GgmProbThreading` closes ProbComp threading end-to-end. Not on the capstone's spine. Stays on wip. |
| `AgmSound.lean` | **DROP from PR** | Alternative fix approach (panel). Part 1 is a genuine FKL extraction (a valid representation of a t-SDH win *is* a q-DLOG solution); Part 2 is the negative "a representation field is free data, so it does not close the vacuity." Both subsumed by the vacuity + GGM story. Exploratory; stays on wip. |
| `KzgQDlogVacuity.lean` | **DROP from PR — cite in prose** | Shows the vacuity is *systemic*: the same `Classical.choice` extraction voids a q-strong-DLOG assumption stated in ArkLib's idiom. But the refuted `qDlogAssumption` is **defined by this file itself** (ArkLib has no q-DLOG assumption), so it refutes a self-authored object — a modeling demonstration, not a finding against ArkLib's code. Carries no claim the core files do not. Keep the *point* as one sentence in the README ("the same idiom voids a q-DLOG-style assumption too — evidence this is the unrestricted-quantifier pattern, not a t-SDH typo"); leave the file on wip. |

**Spine confirmed minimal.** The task's stated spine (`GgmAdaptive → … → GgmEndToEnd →
tSdh_ggm_sound`) plus its dependency `GgmCandidate`, plus the finding (`KzgVacuity`) and the
survival proof (`RepairSurvives`), plus the `Binding.lean` fix, is exactly the transitive
import closure of `GgmEndToEnd`. Nothing in it is droppable without breaking the
finding→repair→sound-bound story; nothing outside it is pulled by it.

---

## B. The fix itself

| Artifact | In the PR? | Justification |
|---|---|---|
| `Binding.lean` edit (`+41 / −14`) | **YES — as an actual code change** | The `binding_reduces_to_tSdh` split + `binding` corollary. This is the PR's core change to the main tree, not a committed `.patch` file. |
| `binding-repair.patch` | **DROP as a file** | Internal artifact. Its *content* becomes the diff; the `.patch` file does not ship in the PR. |
| `candidates/extraction.patch` | **DROP** | Internal per-candidate patch; duplicates/precedes `binding-repair.patch`. |

---

## C. Docs — triage

A PR to the EF should carry **one clean README** and none of our internal working notes.

| Doc | In the PR? | Justification |
|---|---|---|
| **`PR-README.md`** (this curation's sibling) | **YES — the only doc** | Clean, neutral, technical; the contribution's face. Written for the maintainers. |
| `PAPER.md` (78 KB) | **DROP verbatim; distill only** | The strongest technical content, and the source material for the README. But it is an internal working *paper* with panel-of-options history, our-own-floors framing, and frontier bookkeeping. For FULL scope, an *optional* trimmed `NOTES.md` (the GGM argument + Boneh–Boyen cross-check, de-internalized) could accompany §3 — ember's call. Default: link the paper externally, keep the PR to the README. |
| `DISCLOSURE-DRAFT.md` | **DROP — never in the PR** | It is a draft letter *to* them (an issue body). A letter addressed to the maintainers does not belong *inside* a PR to the maintainers. It is, however, the right basis for the **PR/issue description** ember writes when opening — collegial, already well-pitched. Use it there, not in-tree. |
| `REPAIR.md` | **DROP** | Internal proposal/rationale for option (B). Content folded into README §2. |
| `SOUND-FIX-VERDICT.md` | **DROP** | Internal integrator verdict comparing five candidate fixes. Decision record, not a deliverable. |
| `END-TO-END-PLAN.md` | **DROP** | Internal wiring/design plan for "the next swarm." No proofs; pure orchestration. |
| `LEAN-QUALITY-REVIEW.md` | **DROP** | Internal corpus grading (and now partly stale — predates the newer GGM files). |
| `WHY-FINDING-ONLY.md` | **DROP** | Internal analysis of whether a numeric fix was reachable — its conclusion ("send the finding alone") is now *superseded* by the completed GGM bound. Historical record. |
| `FACTCHECK-FABLE.md` | **DROP** | Internal independent second-checker log. Its *result* (independently reproduced) can be mentioned in the PR description, not shipped. |
| `twopager.typ` / `twopager.pdf` | **DROP** | Internal two-pager. |
| `candidates/*.md` (agm-sound, extraction, ggm, novel, qdlog-direct) | **DROP all** | Internal per-candidate design notes. |

Net: **the PR carries exactly one doc — the README** (plus an optional `NOTES.md` only if FULL
scope wants the GGM argument written out in-tree).

---

## D. PR-scope options

| Option | Contents | Size | For a maintainer |
|---|---|---|---|
| **(a) MINIMAL** | `Binding.lean` fix + short README explaining the vacuity in prose. Soundness + witness offered as follow-up. | Smallest; ~1 file changed + 1 doc | Fastest to merge, but the "your assumption is vacuous" claim arrives *without* the mechanized witness — reads like an unmotivated refactor. Weakest evidence. |
| **(b) FIX + WITNESS** *(recommended)* | `Binding.lean` fix + `KzgVacuity.lean` + `RepairSurvives.lean` + README. | 1 edit + 2 scratch files + 1 doc | Self-contained and reviewable in one sitting: the finding they can verify (`lake build` + `#print axioms`), a mergeable fix that keeps all their reduction, and proof it survives the attack. The GGM bound is a described, offered follow-up. |
| **(c) FULL** | (b) + the 8-file GGM spine (`GgmCandidate … GgmEndToEnd`) + README (+ optional `NOTES.md`). | 1 edit + 10 scratch files + 1–2 docs | The complete contribution, including a candidate first-in-Lean generic-group security theorem. But it is a *research artifact* — a novel GGM model + simulation across 8 files — and a much heavier review. Arguably its own PR, and worth a prior discussion about where GGM/AGM infrastructure should live (they have a WIP `AGM/Basic.lean`). |

### Recommendation: **(b) FIX + WITNESS now, (c)'s GGM chain as a signposted follow-up.**

What an ArkLib maintainer most wants to receive is a finding they can verify in one sitting, a
fix that discards none of their work and keeps `binding`'s signature, and a proof it survives —
all mergeable today. That is exactly (b). Bundling the 8-file GGM development into the same PR
multiplies the review surface (a bespoke generic-group model + simulation theorem is not a
drive-by review) and couples a low-risk merge to a research-scale one. The GGM result is strong
enough to stand as its own PR — ideally after a short issue-level conversation about whether it
belongs in `Scratch/`, alongside a completed `AGM/Basic.lean`, or as new shared infrastructure.
The README §3 is written so it serves as the *offer* under (b) and drops in unchanged as the
*content* under (c).

**Suggested sequencing:** open an issue from `DISCLOSURE-DRAFT.md` (the finding, collegially),
land (b) as the fix PR, then propose (c) as a follow-up once they signal where the GGM
infrastructure should live.

---

## E. The curated PR branch (manifest to build from wip)

```
ArkLib/Commitments/Functional/KZG/Binding.lean         # EDIT: +41/−14 (binding_reduces_to_tSdh + corollary)
ArkLib/Scratch/KzgVacuity/KzgVacuity.lean              # finding                     [b, c]
ArkLib/Scratch/KzgVacuity/RepairSurvives.lean          # survives-attack             [b, c]
ArkLib/Scratch/KzgVacuity/GgmCandidate.lean            # static core                 [c]
ArkLib/Scratch/KzgVacuity/GgmAdaptive.lean             # adaptive bound              [c]
ArkLib/Scratch/KzgVacuity/GgmRandomEncoding.lean       # quadratic count             [c]
ArkLib/Scratch/KzgVacuity/GgmDegreeDischarge.lean      # degree discharge (real)     [c]
ArkLib/Scratch/KzgVacuity/GgmArkLibTransport.lean      # field→group transport       [c]
ArkLib/Scratch/KzgVacuity/GgmProbThreading.lean        # ProbComp threading          [c]
ArkLib/Scratch/KzgVacuity/GgmEmbed.lean                # generic-restricted embed    [c]
ArkLib/Scratch/KzgVacuity/GgmEndToEnd.lean             # capstone tSdh_ggm_sound      [c]
docs/…/PR-README.md (as the PR's README)               # the one doc

# STAYS ON wip (not in any PR): GgmDegreeInvariant, AlgebraicTSdh, AgmSound, KzgQDlogVacuity,
# binding-repair.patch, candidates/*.patch, and every internal .md/.typ/.pdf above — including
# DISCLOSURE-DRAFT.md (that one seeds the issue/PR description, never ships in-tree).
```

Note: on the curated branch the scratch modules' cross-imports become
`import ArkLib.Scratch.KzgVacuity.<Module>` (the wip files use scratch-relative bare imports
like `import GgmEmbed`).
