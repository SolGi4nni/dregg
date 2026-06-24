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

## ⚑ Read-first ledgers (the state of the system)

| Doc | Covers | Currency |
|---|---|---|
| **`_CIRCUIT-ASSURANCE-PER-EFFECT.md`** | THE per-effect circuit-assurance ledger: each of ~56 effects classed A/B/C/D, with cited theorem `file:line`. ~12 genuine class A; ~40 class C. *Read before any circuit claim.* | **CURRENT** (finalized 2026-06-08) |
| **`_DREGG-DREGGRS-MANIFEST.md`** | The dregg(Lean-truth)/dreggrs(Rust-heritage) segregation, crate by crate, + the Port-phase residuals. | **CURRENT** (2026-06-08) |
| **`_SILVER-COVERAGE-LEDGER.md`** | Every workspace crate (53 members) ⟺ Lean coverage: LOC, EFFECT/PROTOCOL layer, FULL/PARTIAL/GAP, runtime path, load-bearing, port priority. | **CURRENT** (2026-06-08) |
| **`_CRYPTO-HYPOTHESIS-LEDGER.md`** | Every load-bearing named crypto assumption on the verified surface; per-hyp DISCHARGED vs IRREDUCIBLE-PRIMITIVE. | **CURRENT** (finalized 2026-06-08) |
| **`_PROOF-INTEGRITY-LEDGER.md`** | Severity-ranked proof-integrity findings from the adversarial-verify rounds; every cited line re-checked. | **CURRENT** (2026-06-08) |
| **`_VACUITY-SWEEP.md`** | Load-bearing-vacuity audit: each `:= True`/`:= Unit`/`fun _ => True`/`rfl` traced to whether it props up a `*_sound`. | CURRENT |
| **`_WHAT-IS-DREGG.md`** | What dregg is, code-grounded (quotes are `file:line`): the runtime, what is built, the verification story. | LIVING |
| **`_DREGG-ONTOLOGY-AND-PRODUCT.md`** | The ontology (what the structures are) + the functional-correctness line + the product-layer map (Lean + Rust). | LIVING |
| **`CONSISTENCY-SURFACE.md`** | The full trusted-assumption carrier audit — every Prop-carrying typeclass field / structure field. | CURRENT |
| **`_THREAT-MODEL.md`** | Threat model + info-flow / metadata-privacy analysis; the map for fuzz/chaos phases. | LIVING |

## Subsystem orientations + design passes

### Executor / effects

| Doc | Covers | Currency |
|---|---|---|
| **`_EXECUTOR-COMPLETENESS-GAPMAP.md`** | Distance between the verified Lean executor (`execFullForestG`) and full execution. | CURRENT (2026-06-06) |
| **`DESIGN-EFFECT-HANDLER-ALGEBRA.md`** | The effect-handler algebra (the swap-grade executor foundation); scaffold in `Exec/Handler.lean`. | LIVING (accepted 2026-06-04) |

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
| **`_PRODUCT-POLIS-ASSESSMENT.md`** | The product/usability/polis surface: the agent-orchestration substrate, measured turn latency, and the on-ramp. | LIVING |
| **`_FRONTEND-OVERHAUL-PLAN.md`** | Frontend/product-surface overhaul plan (read-only assessment). | CURRENT (2026-06-08) |
| **`REVIEW-explorer.md` / `REVIEW-playground.md` / `REVIEW-studio-starbridge.md`** | Reviews of the explorer / playground / studio+starbridge web surfaces. | DATED (2026-06-06) |

### Program-wide / meta

| Doc | Covers | Currency |
|---|---|---|
| **`TITANIUM-PHASE.md`** | The Titanium program (v2): one description, one theory, one trust base; the Gold light-client target. | LIVING |
| **`_DREGG1-DREGG2-UNIFICATION-LEDGER.md`** | Where dregg1 Rust and dregg2 types are still duplicated / not unified, and the Lean-producer cutover boundary. | LIVING |
| **`_RUST-LEAN-DIVERGENCE-LEDGER.md`** | Output of the live differential finder (`turn/tests/rust_lean_divergence_finder.rs`): every Rust↔Lean executor divergence. Regenerated by the harness. | CURRENT (regenerated) |
| **`_METATHEORY-GLUE-AUDIT.md`** | What the `Metatheory/*.lean` layer (5 files + Open/) IS and how it connects to `Dregg2/`: which keystones are load-bearing instantiations vs re-namings. | LIVING |
| **`EXTERNAL-LEAN-REFERENCES.md`** | External Lean 4 reference libraries for the formal-methods push. | DATED (2026-06-02) |

---

*Sibling navigation: [`../NAVIGATION.md`](../NAVIGATION.md) (where-is-X map),
[`../../README.md`](../../README.md) (what dregg2 is), [`../guides/`](../guides/) (subsystem guides).*
