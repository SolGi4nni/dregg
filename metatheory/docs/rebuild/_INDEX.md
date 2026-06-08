# `docs/rebuild/` — Document Index

One line per doc: **what it covers + currency**. These are mid-development design / ledger /
orientation notes. When a doc and the code disagree, **the code wins** — but the `_*-LEDGER` /
`_*-DESIGN` docs below are mostly kept current and cite `file:line`. Currency tags:

- **CURRENT** — dated 2026-06-06+ and code-grounded; a reliable answer.
- **LIVING** — a design spine that's still evolving; the *shape* is right, details may move.
- **DATED** — useful but predates a rename/refactor; read for intent, verify against code.

> Note: there is a **second** `docs/rebuild/` at the **repo root** (`…/breadstuffs/docs/rebuild/`)
> with the *foundations / spine / candidate* essays (`01-spine-*.md`, `cand-*.md`,
> `FOUNDATIONS-*.md`, `DREGG4-*.md`, `GLOSSARY.md`, …). This index covers the **`metatheory/docs/rebuild/`**
> set — the operational ledgers and design passes for the verification campaign.

---

## ⚑ Read-first ledgers (the honest state of the system)

| Doc | Covers | Currency |
|---|---|---|
| **`_CIRCUIT-ASSURANCE-PER-EFFECT.md`** | THE per-effect circuit-assurance ledger: each of ~56 effects classed A/B/C/D, with cited theorem `file:line`. ~12 genuine class A; ~40 class C. *Read before any circuit claim.* | **CURRENT** (finalized 2026-06-08) |
| **`_DREGG-DREGGRS-MANIFEST.md`** | The dregg(Lean-truth)/dreggrs(Rust-heritage) segregation, crate by crate, + the Port-phase residuals. | **CURRENT** (2026-06-08) |
| **`_SILVER-COVERAGE-LEDGER.md`** | Every workspace crate (53 members) ⟺ Lean coverage: LOC, EFFECT/PROTOCOL layer, FULL/PARTIAL/GAP, runtime path, load-bearing, port priority. | **CURRENT** (2026-06-08) |
| **`_CRYPTO-HYPOTHESIS-LEDGER.md`** | Every load-bearing named crypto assumption on the verified surface; per-hyp DISCHARGED vs IRREDUCIBLE-PRIMITIVE. | **CURRENT** (finalized 2026-06-08) |
| **`_PROOF-INTEGRITY-LEDGER.md`** | Severity-ranked proof-integrity findings from the adversarial-verify rounds; every cited line re-checked. | **CURRENT** (2026-06-08) |
| **`_VACUITY-SWEEP.md`** | Load-bearing-vacuity audit: each `:= True`/`:= Unit`/`fun _ => True`/`rfl` traced to whether it props up a `*_sound`. | CURRENT |
| **`_WHAT-IS-DREGG.md`** | A skeptic's honest, code-grounded "what is dregg, really" review (quotes are `file:line`). | DATED (2026-06-06) |
| **`_DREGG-ONTOLOGY-AND-PRODUCT.md`** | Canonical brutally-honest ontology + functional-correctness + product-layer map (5 deep code reviews, Lean + Rust). | CURRENT |
| **`CONSISTENCY-SURFACE.md`** | The full trusted-assumption carrier audit — every Prop-carrying typeclass field / structure field. | CURRENT |
| **`_THREAT-MODEL.md`** | Threat model + info-flow / metadata-privacy analysis; the map for fuzz/chaos phases. | LIVING |

## Subsystem orientations + design passes

### Executor / effects

| Doc | Covers | Currency |
|---|---|---|
| **`_EXECUTOR-COMPLETENESS-GAPMAP.md`** | Distance between the verified Lean executor (`execFullForestG`) and full execution. | CURRENT (2026-06-06) |
| **`EFFECT-FIDELITY-LEDGER.md`** | dregg1 `apply.rs` vs Lean `execFullA`, adversarially audited (4 skeptics). | DATED (2026-06-03) |
| **`DESIGN-EFFECT-HANDLER-ALGEBRA.md`** | The effect-handler algebra (the swap-grade executor foundation); scaffold in `Exec/Handler.lean`. | LIVING (accepted 2026-06-04) |
| **`DREGG2-GAP-MAP.md`** | What's still MISSING/under-implemented in the Lean model that real execution needs; REAL/DECORATIVE tags. | DATED (2026-06-02) |

### Circuit / ZK

| Doc | Covers | Currency |
|---|---|---|
| **`_EMITTER-AMPLIFICATION-WORKLIST.md`** | The work-list to amplify the verified emitter from transfer to all effects. | CURRENT |
| **`_IR-EXTENSION-DESIGN.md`** | EffectVM IR extension for side-table state binding (additive). | LIVING |
| **`_RECORD-LAYER-UPGRADE.md`** | The committed field-MAP record-layer upgrade (read-only design). | LIVING |
| **`_RUST-CIRCUIT-CONSOLIDATION.md`** | Can we delete the manual Rust AIRs because Lean is better? Verdict: not yet, keep as diversity. | DATED (2026-06-06) |
| **`DESIGN-lookups-plonky3-perf.md`** | LogUp lookup arguments + plonky3 performance for the circuit mapping. | LIVING (research) |
| **`DESIGN-recursion-aggregation-private-joint-turns.md`** | Recursion/aggregation for private joint turns (Silver→Gold). | LIVING (research) |

### Distributed / consensus / federation

| Doc | Covers | Currency |
|---|---|---|
| **`_FEDERATION-SSB-DESIGN.md`** | The comprehensive verified-federation blueprint: federation = Secure-Scuttlebutt-on-crack. Directs the distributed-protocol wave. | CURRENT |
| **`_FEDERATION-SSB-ORIENTATION.md`** | SSB heritage mapped to dregg, cited to real Rust (`blocklace/`, `federation/`, `captp/`, `net/`, `node/`). | CURRENT |
| **`CONSENSUS-GROUNDING.md`** | Phase-2.1 consensus grounded in two 2024 papers (Sridhar resilience pair + Wong taxonomy). | CURRENT |
| **`_CAPTP-ORIENTATION.md`** | The `captp/` crate (~5395 LOC): object-cap transport, trust model, verification targets. | CURRENT |

### Authority / caveats / policy

| Doc | Covers | Currency |
|---|---|---|
| **`_AUTHORIZATION-COMPLETE.md`** | The authorization model internalized end-to-end: token gates EXECUTOR admission, every caveat tier executed. | CURRENT |
| **`_POLICY-LANGUAGES-REFRESH.md`** | De-stodgying the predicate/caveat/datalog policy surfaces dregg2 formalizes + enforces. | LIVING (design) |

### Intent / agents / web3

| Doc | Covers | Currency |
|---|---|---|
| **`INTENT-AS-CO-RECEIPT.md`** | The living design spine: intent = co-receipt; a first-class metatheory of web3. | LIVING |
| **`PHASE-2-INTENT-SPEC.md`** | The concrete `Intent` core build spec (layered option c). | LIVING |
| **`INTENT-REFS-*.md`** | Reference surveys per pillar: `-centers` (monoidal/Drinfeld), `-fairness` (justness/van Glabbeek), `-linear` (linear logic/session types), `-optics` (coend/open-games), `-resources` (string diagrams), `-tensor-categories` (hyperdoctrines), `-time` (causal vs frame), `-web3` (intent-centric SOTA). | LIVING (research) |

### Crypto / UC

| Doc | Covers | Currency |
|---|---|---|
| **`PHASE-UC-TRANSPORT.md`** | Closing the dynamic-UC commitment hole by cross-system transport (Lean↔Isabelle). | LIVING |
| **`UC-CARRIER-GAME-MAP.md`** | The UC-carrier ↔ CryptHOL game map — the Lean↔Isabelle trust seam (pillar #6). | LIVING |

### Apps / product / frontend

| Doc | Covers | Currency |
|---|---|---|
| **`APP-THEOREM-SUITE.md`** | What "a verified userspace app" means in dregg2 (the app theorem suite). | LIVING |
| **`_PRODUCT-POLIS-ASSESSMENT.md`** | Is dregg *good for its purpose* yet? Product/usability/polis assessment. | CURRENT (2026-06-08) |
| **`_FRONTEND-OVERHAUL-PLAN.md`** | Frontend/product-surface overhaul plan (read-only assessment). | CURRENT (2026-06-08) |
| **`REVIEW-explorer.md` / `REVIEW-playground.md` / `REVIEW-studio-starbridge.md`** | Reviews of the explorer / playground / studio+starbridge web surfaces. | DATED (2026-06-06) |

### Program-wide / meta

| Doc | Covers | Currency |
|---|---|---|
| **`TITANIUM-PHASE.md`** | The Titanium program (v2): one description, one theory, one trust base; the Gold light-client target. | LIVING |
| **`HANDOFF-2026-06-06.md`** | Entry point for continuing whole-turn ZK / emitted→spec diamonds / no-lurking-holes. | DATED (2026-06-06) |
| **`HANDOFF-2026-06-03.md`** | The whole-program state & master roadmap handoff. | DATED (2026-06-03) |
| **`_DREGG1-DREGG2-UNIFICATION-LEDGER.md`** | Where dregg1 Rust and dregg2 types are still duplicated / not unified. | DATED |
| **`_RUST-LEAN-DIVERGENCE-LEDGER.md`** | Output of the live differential finder (`turn/tests/rust_lean_divergence_finder.rs`): every Rust↔Lean executor divergence. Regenerated by the harness. | CURRENT (regenerated) |
| **`_METATHEORY-GLUE-AUDIT.md`** | How much "glue" is in `Metatheory/*.lean` (5 files + Open/, 4536 LOC). | DATED (2026-06-06) |
| **`EXTERNAL-LEAN-REFERENCES.md`** | External Lean 4 reference libraries for the formal-methods push. | DATED (2026-06-02) |
| **`_DOCS-CLEANUP-PLAN.md`** | The 98-file triage that produced this cleanup; dispositions. | DATED (2026-06-06) |
| **`_RECOVERED-DESIGNS-2026-06-02.json`** | Machine-readable recovered-designs report (post-compaction recovery). | DATED (2026-06-02) |

---

*Sibling navigation: [`../NAVIGATION.md`](../NAVIGATION.md) (where-is-X map),
[`../../README.md`](../../README.md) (what dregg2 is), [`../guides/`](../guides/) (subsystem guides).*
