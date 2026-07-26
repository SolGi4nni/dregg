# ROADMAP — Assurance-Perimeter Closure (living tracker)

The multi-swarm-cycle execution tracker for closing the witness-generation perimeter. **DESIGN** (the
architecture + the verdicts) = `docs/DESIGN-assurance-perimeter-closure.md`. **INVENTORY** (what was
trusted-Rust) = memory `project-witness-gen-assurance-perimeter`. This file = *where we are*, updated each
cycle. Orthogonal axis: the FRI floor (`project-fri-soundness-reality`; see `FriDeployedHeightPairing` for the deployed posture) — never laundered by
this work.

## Mission (the invariant we are driving to)
Every consensus-visible value is EITHER constrained by a proven-**COMPLETE** AIR (`air_accepts ⟺ spec`, in
the honest shape below) OR a single Lean implementation Rust calls into. The receipt carries a **proof**, not
a trusted key. **Nothing trusted, nothing duplicated.**

## Standing discipline (the rules that keep re-earning themselves)
- **GREENFIELD** — nothing is deployed. NO cutover / migration / flag-day / byte-identical / compat theater
  (`feedback-no-greenfield-migration-theater`). Build the right object, DELETE the debt.
- **The honest `⟺` shape** (from the non-rev template, `209d543e5`): NOT a per-trace `Satisfied2 ↔ spec`
  (degenerates vacuous when ordering is lookup-enforced). It is **accept-SET ↔ spec** + **∀-soundness ∧
  ∃-completeness**, all trust folded into ONE named carrier bundle. Canary both directions.
- **CI-wire every exemplar** — a proof the default `Dregg2` build never compiles is a green nobody runs
  (`776381e52` wired the first two). Import into the root aggregator.
- **AIR is Lean-authored** (law #1). Rust computes witnesses / calls in; the CONSTRAINT is Lean.
- **VERIFY AGAINST THE DEPLOYED DESCRIPTOR, not a study face** ([[feedback-reality-gate-first-not-internal-consistency]]). The audit/crux mis-classified cap (#4) as underconstrained by reading a SUPERSEDED `*Refine`/study module — the LIVE registry entry (`attenuateVmDescriptor2R24 = attenuateV3`) already forced the genuine `writesTo8`. Every value's status is confirmed against the deployed registry entry + its apex wiring (`Rfix _`, `ClosureFanoutGenuine`), NOT a `*Refine` peer. A lane that REFUSES to build a mirror + reports the deployed reality is the discipline HOLDING (cap lane, `c8f443e37`).

## Status board — the 11 perimeter values
| # | value | class | status |
|---|---|---|---|
| — | `⟺` TEMPLATE (non-rev) | technique | ✅ `209d543e5` — the reusable schema + honest-shape finding; CI-wired |
| 8 | non-revocation | technique | ✅ (the template IS non-rev); residual: fold spine decode further |
| 2 | state commitment (transfer) | technique | ✅ FLAGSHIP `c68c4f5a9` — `transferDescriptor_commit_iff`; CI-wired. **ANCHOR CUTOVER LANDED** (this cycle): `dregg_turn::state_commit` is now THE consensus anchor — `TurnReceipt::{pre,post}_state_hash`, the executor signature, the federation receipt QC body, and (transitively via `receipt_stream_root`) the `AttestedRoot` quorum all carry the CHIP 8-felt `wire_commit_8_chip`, not BLAKE3 `Ledger::root()`. ⚑ NOT `⟺`-CLOSED: the flagship theorems certify the **1-felt** `wireCommitR`; the 8-felt anchor is chip-bound + soundness-ADDITIVE, and `air_accepts ⟺ spec` at 8 felts awaits the S2 flag-day + an 8-felt re-derivation (gated on the vacuous-at-params `Poseidon2WideCR`/`InjectiveFloorRegrounded`). TAIL: generalize to ALL effect tags; the 8-felt re-derivation. |
| 5 | heap-root | ARCHITECTURE | ✅ `f7dd79db2` — genuine `Heap.set` forced, prepend-digest DELETED, MapOps carrier verified |
| 3 | receipt `TurnExecuted` | trust→proof | ✅ **VERIFIED GREEN** — resolver `26d3b1615` + migration `b4ac7ef23` (all 4 features → `TurnProven`, proof threaded onto the receipt), on origin. Clean run: `service_promise` **7 passed / 0 failed**, incl. `committed_state_forbids_refund_after_release` + `committed_terminal_moves_the_cell_commitment` — the earlier "failures" WERE a stale-reverted-source artifact (the tree had been reset mid-session), exactly as the lane diagnosed. Trusted-key retired as the `TurnExecuted` trust root; a receipt now requires a VERIFIED EffectVM STARK bound to the turn. |
| 4 | cap-root | ~~ARCHITECTURE~~ **ALREADY CLOSED** | ✅ the DEPLOYED `attenuateV3` already forces the faithful 8-felt sorted-tree write `writesTo8` (`CapOpenEmit.effCapOpenWriteV3_forces_write8`, §11 keystone, `#assert_axioms`-clean, apex-wired via `Rfix 12` / `ClosureFanoutGenuine` CLASS A) — **STRONGER than heap** (full ~124-bit vs heap's lane-0 scalar). The audit/crux "prepend / free CAP_DIGEST_NEW" read a SUPERSEDED study face, not the deployed descriptor. Doc corrected `c8f443e37`. The cap lane correctly REFUSED to build the requested scalar splice (would be a weaker re-authored mirror — reality-gate held). RESIDUALS (tracked, NOT soundness gaps): (a) delete the superseded prepend/free-digest code across ~15 cap-family modules (own multi-session cutover + adversarial audit); (b) a `Satisfied2`-only forged-root canary needs the sorted-tree functional property from the trace (discharge the `SpineCommits` decode) + closes the arity-7 leaf other-field encoding residual. |
| 6 | note-spend | structural | ✅ `cb2567872` (on origin) — `noteSpendFresh_accepts_iff` (full `⟺`: `NoteFreshAccepts ↔ nf∉nulls`), `gapOpen_complete` forward gap-construction, canaried both directions, `#assert_axioms`-clean. `NullifierTreeEncodes` kept as the honest Rust-accumulator-boundary residual (named). |
| — | garbled-eval | technique | ✅ `ba38e878b` (on origin) — `garbled_accepts_iff` (`AirAccepts ↔ CanonInstance`) + `garbled_bridge` (∀-soundness ∧ ∃-completeness); `honestG_satisfied2` generalizes the single witness parametrically; `GarbledCarriers` bundle (canon+hash), both canaries. Also CI-wired the previously `lake env`-only Rung-1/2 garbled chain. |
| 1 | ledger root | trusted-Rust | 🟡 **OFF THE RECEIPT/SIGNING PATH** — `Ledger::root()` no longer reaches any receipt, executor signature, or federation receipt QC. It survives ONLY where a genuine non-consensus rationale holds (the `reversible.rs` in-process scrubber teeth, snapshot/image whole-image bootstrap, wasm host export) — the roles the dual-hash ADR (`dregg_commit::hash`) actually reserves for BLAKE3. `canonical_ledger_root` REMAINS in `AttestedRoot`/`FinalizationVote` as the **restart anchor** (a node reconstructs its ledger from the store and checks it against the quorum-signed digest — no per-cell algebraic commitment fills that role). RESIDUAL: this anchors a **per-cell/per-transition** commit, so the whole-ledger 8-felt state root is still the deferred `cells_root` Phase-E. |
| 9 | `system_roots_digest` | trusted-Rust | ⏳ later — small; make it an AIR-bound or Lean-authored value |
| 10 | effect state-transition | Lean-authored | ✅ deployed `produce_via_lean` (covered set); residual: the root (#2) + wasm/unmapped fallback |

## ⚑ VACUITY AXIS (07-24→25) — the accrual gate, and the strategy that had to be corrected

A second, orthogonal disease to the `⟺` axis: a hypothesis **PROVABLY FALSE at deployed BabyBear params** makes
every theorem assuming it **VACUOUS** — true, and saying nothing about the deployed system.

**LANDED.** `#floor_ratchet` (`Dregg2/Verify/FloorRatchet.lean`, end of `Dregg2.lean`): a NEW declaration taking
a refuted floor is a **BUILD ERROR**. Adversarially proven (8 probes, every evasion class red). CI-armed via
`scripts/floor_ratchet_check.sh` (`16f7719341`) — **presence-then-build**, because a deleted command raises no
error. Holes found and closed: **B3** bundle-user, **B4** binder-order (`Γ → F → False` *is* `Γ → ¬F`, so the old
rule keyed on a spelling the author controls), **inj-spelling** (`Verify/InjSpelling.lean` — the refuted set is
DERIVED from in-tree refutation theorems, never hardcoded, so it self-updates). `1c20b7290`, `9e0f13d2f`.
⚑ `9e0f13d2f` records the headline: the gate was *"blind to 24 bundles and **laundering 105 security claims**"* —
theorems that READ as assurance while assuming something false. **That named list is the campaign's most valuable
artifact.**

**TOOLING.** `Verify/FloorCensus.lean` (semantic census over ELABORATED terms, 27 floors — text cannot see
`variable` binders nor tell endpoint from threader) · `Tools/ConePort.lean` (codemod, 100% of its eligible class,
byte-reproducible) · `Tools/ConeCutover.lean` (TRANSACTIONAL delete+rewire+pin-move, falsified with 5 probes) ·
`scripts/binding_surface_complete.py` (coarse textual ruler — blind to 20 of 27 floors, treat as an UNDERCOUNT).

**STATE: accrual STOPPED** (34 commits / 366 new declaration headers, tier-A flat). **Removal still NET-NEGATIVE**
(1 declaration out, 6 in). The gate stopped the bleeding; nothing drains yet.

**⚑ THE MEASURED STRATEGY CORRECTION — read before planning any removal wave.**
- The endpoint→cone unlock model is **FALSE, measured at 0.5**: 20 endpoints ported freed only 10 threaders, and
  the threader class went **UP** (1177→1184). CAUSE: **multi-floor declarations** — a declaration stays a carrier
  while ANY floor remains, so shedding one floor of four is real proof work with **zero** realized reduction.
  Proof: cellleaf shed `cellLeafInjective` from 13 sites; all 13 reappeared carrying other floors.
- **Work order by measured ratio:** ① **BUNDLES** (floor-FIELD deletions; 3 bought −6). Remaining:
  `CircuitSoundness.lean:117`, `:1050`, `ClosureLog.lean:86`, `DeployedCapTree.lean:139`. ② **SOLE-FLOOR**
  declarations (verify sole-floor status FIRST). ③ multi-floor only in whole floor-COMBO batches (~16 combos).
- **BUNDLE RULE** (`Shielded/RealCrypto.lean` §2.0): DELETE the floor field; **never** swap in a `noColl` field —
  a field has no argument position, so it must quantify over a pre-chosen set (empty carries nothing; non-trivial
  is uninhabitable again). That is laundering. Re-inhabit with a **constructed deployed inhabitant whose own
  carriers REFUTE the deleted field** (`deployedCap8Scheme`, `deployedPoseidon2Tree`, `deployedCompress2`).

**⚑ THREE OPERATIONAL LAWS PAID FOR IN LOST TIME:**
1. **A red root build DELETES a build-embedded gate rather than failing it.** `#floor_ratchet` emitted nothing for
   **111 commits** because two committed modules referenced providers that were never committed at any revision
   (`a71b631a8e`). Treat root-build-green as a load-bearing invariant, and guard the gate's *presence* out of band.
2. **Never measure a repo-wide metric in the working tree** — it carries other people's uncommitted providers and
   yields a green no other checkout reproduces. Use a clean `git archive` export, md5-verify the instrument across
   compared trees.
3. **Ask where a number came from.** "112/121 endpoints" was never real — the ruler counts 86, and every 121 in
   the tree is **automatafl's n²=121**. A campaign was sized off a game board because it was only ever checked for
   internal consistency.

## Cycles
- **Cycle 1 — DONE.** template · heap hole · state-commit flagship · CI-wiring · receipt resolver (held).
- **Cycle 2 — ✅ COMPLETE.** note-spend `cb2567872` · garbled `ba38e878b` · cap found-already-closed `c8f443e37` ·
  #3 receipt migration `b4ac7ef23` **VERIFIED GREEN** (7/0 service_promise, the earlier reds were stale-reverted-source).
  All exemplar modules CI-wired into the default `Dregg2` build and on origin.
- **Cycle 3 — IN FLIGHT, sequenced AROUND the co-tenant heap8/S2 churn.** KEY: the `→` soundness half is ALREADY
  generic (`runnable_full_sound` over `RunnableFullStateSpec` in `EffectVmFullStateRunnable.lean`, ~28 emits ride it);
  only the `←` completeness is missing. **FIRE-NOW ✅ DONE** — engine `92518d277` (`runnable_full_commit_iff`) +
  fan A `1a53b1035` (8 kernel/lifecycle tags) + fan B `f4e7f871f` (9 kernel-emit tags incl. SetField) = **17 kernel-only
  tags with `air_accepts ⟺ spec`**, reality-gated against the deployed `*Wide` descriptors, `#assert_axioms`-clean, per-tag
  canaries; **CI-wiring ✅ DONE** — both tag modules wired into the default `Dregg2` build on origin (all 6 perimeter
  exemplars now imported), and they build **green in-closure (3083 jobs)**. ⚠ The full `Dregg2` tree is currently red from
  ANOTHER lane's `AutomataflResolveCapstone` `sorryAx` (committed, self-described "one hypothesis short") — NOT from the
  perimeter work; the axiom gate is doing its job on their side. The recipe was: the ONE generic `runnable_full_complete` +
  `runnable_full_commit_iff` (transfer template lifted) → the flagship becomes the ENGINE → ~15 KERNEL-ONLY tags become
  thin instantiations (IncrementNonce, SetVK, SetPermissions, MakeSovereign, CellSeal/Destroy/Unseal, CreateCell{,FromFactory},
  EmitEvent, Exercise, PipelinedSend, ReceiptArchive, Noop, Burn, BridgeMint; verify SetField). **DEFER (gated on heap8/S2
  landing, then near-instantiations of THEIR machinery):** sorted-tree tag completeness (cap/heap/note), `cells_root` Phase-E.
  **DEFER + CORRECTED:** the state-commit anchor must target `wire_commit_8` (`Faithful8`), NOT the 1-felt `wire_commit`
  (anchoring the 1-felt now RE-CEMENTS the ~31-bit waist the co-tenant is deleting — a regression); land after the 8-felt
  STATE_COMMIT settles. **THEIRS:** the ~31-bit→8-felt node8 thread (co-tenant). `hcanon` field-faithfulness rides that.
- **Apex (post-A).** recursive-proof-default (grow inner AIR to real `EffectVmAir`, force `NEW_COMMIT` in-circuit,
  then recurse). THEN the FRI floor campaign (`FriLdtExtractV3`, an adversary object) — separate.

## Cross-crate arcs (the multi-session pieces — plan before firing)
1. **Receipt proof-threading (#3):** commit pipeline PRODUCES the rotated STARK → ATTACH to `TurnReceipt`/
   `ConditionProof` at construction → 4 features migrate to `TurnProven`+`EffectVmProof` → land `26d3b1615`.
   Touches: node commit pipeline, sdk receipt type, turn/conditional, the 4 feature crates + tests.
2. **State-commit anchor cutover (#2 tail): ✅ LANDED.** `turn/src/state_commit.rs` is THE anchor
   (`wire_commit_8_chip`, NOT the plain `wire_commit_8` — the plain chain diverges from the deployed chip
   chain and a canary test pins that). Converted: `execute.rs` pre/post, `collapse.rs` head,
   `exec-lean/lean_apply.rs` (Lean/Rust differential now over the anchor), `finalize.rs` contracts.
   Domain-bumped: `dregg-receipt-v5`, `executor-receipt-sig-v5`, `dregg-fed-receipt-body-v2`,
   `dregg-attested-root-v6`, `dregg-finalization-vote-v3`. RESIDUAL (do not overclaim): 8-felt `⟺` is not
   derived; the anchor is per-cell not whole-ledger; the lane-0 waist persists at narrow-leg broadcast
   sites; the executor's root phase regressed from incremental O(log n) to O(n_cells) Poseidon2.
3. **All-effect-tag `⟺`:** generalize `transferDescriptor_commit_iff` from transfer to every effect (the rotated
   descriptor covers them; the per-family completeness proofs do not exist). Pure Lean, but broad.

## Update protocol
Each cycle: flip the status cells, add the commit hashes, move finished arcs out of "in flight". Keep it terse.
This is the thread across the rolling window — the design doc explains WHY, this says WHERE WE ARE.
