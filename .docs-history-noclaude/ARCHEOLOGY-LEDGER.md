# Archeology Ledger

A session-archeology sweep: items that were RAISED in past sessions, apparently dropped, and re-verified as still-open at HEAD (`3a4ae70ca`, 2026-06-19). Each entry carries its source-session evidence, what slipped + why it matters, and a recommendation. Verified against the live tree, not against compaction summaries.

## Executive summary

Three failure modes recur. **(1) Complete-but-unwelded drafts** — the most expensive class: AIRs and Lean twins authored axiom-clean, then left as untracked files imported by a modified-but-uncommitted `Dregg2.lean`/`lib.rs`. A pathspec commit of only the modified files would push imports to nonexistent modules and break origin; the whole file-set must land atomically. **(2) Named-not-shipped follow-ups** — gaps flagged "loudly so they aren't lost" in a commit message, but whose HORIZONLOG line was never actually written, so the named lane evaporated (the marketplace reputation-drop bug is the sharp instance: the commit *claimed* to record it, the line is absent). **(3) Verifier-side residue** — Lean proves the property, but the deployed `proof_verify.rs` still binds only `vm_effects.first()` or resolves one descriptor; the soundness gain is real but never lifted onto the live light-client path.

The five highest-value rescues, in order:
1. **Land the circuit-soundness cluster atomically** (`git add` all untracked AIR/Lean/descriptor files, *then* commit with the modified `Dregg2.lean`+`lib.rs`) — a live phantom-commit hazard that breaks origin's build if half-committed.
2. **Fix the node recovery first-writer-wins bug** (`insert_cell`→`upsert_cell` + fail-closed on convergence mismatch) — a silently-wrong recovered ledger is a soundness event, not a log line.
3. **Wire the in-flight AIRs into `proof_verify.rs`** (cross-cell Σδ=0 #6, agent signature #3, whole-turn forest #2) — the drafts close the Lean side but the deployed verifier is still foolable.
4. **The live interactive seL4 cockpit** (MEMORY's "#1 PRECIOUS") — the render PIPE landed and reads as done; the live per-viewer affordance-surface embedding + repaint-on-turn is the actual remaining work.
5. **Reproduce + fix the compute_marketplace multi-cell drop** — a multi-cell turn that drops a state write yet commits is a real executor atomicity hole; re-add the HORIZONLOG line the commit falsely claimed.

---

## HIGH

### unintegrated-draft

**Circuit-soundness cluster: untracked AIR/Lean/descriptor files imported by uncommitted `Dregg2.lean`/`lib.rs`** — *trust-surface session*
The 8-felt-flip / smuggle-wave session left a live phantom-commit file-set: `circuit/src/cross_cell_conservation_air.rs`, `circuit/src/turn_auth_signature_air.rs`, `metatheory/Dregg2/Circuit/{CrossCellConservation,CircuitCompletenessNonVacuity,RotatedKernelForestCohortChain}.lean`, `metatheory/Dregg2/Crypto/TurnAuthSignature.lean`, `metatheory/EmitCrossCellConservation.lean`, and `circuit/descriptors/dregg-cross-cell-conservation-v1.json` are all `??`; none in `git ls-files`; yet the working-tree `Dregg2.lean` (imports at 48/553/620/625) and `lib.rs` (`pub mod` at 154/282) reference them — both absent from HEAD. Matters because a pathspec commit of only the modified files pushes imports to nonexistent modules and breaks origin's build.
**Recommendation:** `git add` ALL untracked cluster files FIRST, THEN commit together with the modified `Dregg2.lean` + `lib.rs` + `lib.rs`. Land atomically; never half.

**`turn_auth_signature_air.rs` — in-circuit Schnorr turn-auth forcing AIR, additive/not-wired** — *trust-surface session (smuggle #3)*
Header reads "ADDITIVE; not live-wired"; proves only path-(b) Schnorr forcing while the deployed turn signature is Ed25519 verified off-circuit. Wired into working-tree `lib.rs:154` + `Dregg2.lean:48`; both refs absent from HEAD; companion `TurnAuthSignature.lean` also untracked. Matters because a ledgerless verifier reading only the rotated proof gets no agent-authorization binding.
**Recommendation:** Commit with the cluster. Separately decide build-heavy-Ed25519-AIR vs re-bind-turn-authority-to-Schnorr; enter the verifier handoff + the Ed25519→Schnorr translation in HORIZONLOG in the same breath — do not leave the gap merely "named."

**`cross_cell_conservation_air.rs` / `CrossCellConservation.lean` — turn-wide Σδ=0 AIR, not wired into `proof_verify.rs`** — *trust-surface session (smuggle #6)*
Axiom-clean with teeth (`ccc_rejects_unbalanced` / `ccc_forged_mint_unsat`: the A-10,B+999 forgery balances to 989≠0 ⇒ UNSAT / `ccc_rejects_wrong_asset`); `EmitCrossCellConservation.lean` emits the descriptor json's bytes. Both untracked; `git log --all` empty. Declared in `lib.rs:282` but `rg` finds zero references in `proof_verify.rs`. Matters because a single-cell rotated proof cannot conclude turn-wide no-mint — a light client at HEAD is still foolable.
**Recommendation:** Commit with the cluster, then wire the Σδ=0 aggregation into `proof_verify.rs` (the pairing the per-cell proof cannot conclude). Do not let "gap #6 closed" overclaim until the verifier consumes it.

### bug-or-soundness

**Per-cohort proof-chain forcing: verifier forces ONLY the lead effect** — *trust-surface session (smuggle #2)*
`proof_verify.rs:160` is `let lead = vm_effects.first()` then resolves ONE descriptor and verifies ONE proof — no per-leg adjacency loop. `RotatedKernelForestCohortChain.lean` (untracked, imported at `Dregg2.lean:625`) proves `chainForcesEveryCohort` / `chainBroken_rejects` / `lightclient_cohort_chain_forces_full_turn` axiom-clean; the producer-side `leg[i].NEW==leg[i+1].OLD` check already exists at `full_turn_proof.rs:2448`. Matters because tail-cohort effects (e.g. a trailing `SetPermissions`) are currently unforced — a real soundness gap, only partially mitigated by the selector-validity gate that makes same-cell cross-cohort tails UNSAT.
**Recommendation:** Commit the untracked Lean file; rewrite the `proof_verify` path to verify the whole leg-list with NEW==OLD adjacency, retiring `effects.first()`-only. VK-affecting. Track distinctly from #3/#6.

**Node recovery first-writer-wins: `insert_cell` silently drops post-checkpoint writes; convergence mismatch only LOGS** — *recovery-overlay session*
`node/src/state.rs:699` and `:879` both use strict `insert_cell`, so a post-checkpoint write to a cell the checkpoint already holds is silently dropped. The convergence assertion at `:702-733` emits `tracing::error!` "STORE INTEGRITY EVENT" on mismatch and falls through — no `Err`, no panic, no fail-closed. Matters because a silently-wrong recovered ledger is a soundness event served as truth.
**Recommendation:** Swap `insert_cell`→`upsert_cell` (remove-then-insert per the verified `CrashRecovery.upd` point-update) at both sites AND make the convergence-root mismatch fail closed (return `Err` / refuse to serve).

**Argus precondition-COMPLETENESS audit: executor preconditions never proven to be in-circuit conjuncts** — *argus-completeness session*
`EffectVmEmitBurnRunnable.lean:33-35` explicitly: the BurnGuard authority/non-negativity/availability/liveness preconditions "have NO row column: they are executor-side preconditions NOT in-circuit conjuncts of `burnVmDescriptor` … the named, deferred systematic audit wave." The Jun-18 "SOUND ∧ COMPLETE" campaign is the *other* direction (valid turn HAS an accepting proof), not this "forgot-to-assert-a-precondition" soundness half. Matters because a forgotten precondition lets a light client accept a proof over bad data.
**Recommendation:** Re-dispatch the per-effect-family precondition-completeness audit: for each runnable descriptor, prove every executor precondition is an in-circuit conjunct or name the gap as a fix-descriptor in the obligation table. Acknowledged-deferred in the Lean source itself.

**Class-A SetMembership family (queue-FIFO / note-nullifier / seal-box) never graduated to full-semantics descriptor proofs** — *circuit-functional-correctness session*
`docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` (HEAD, Jun 18) lists noteSpend/noteCreate/createCell/spawn + cap/seal/destroy in the VALUE_MISSING class: ":189 nothing forces pubPost to reflect the change," and ":249-254 the queue/seal effects route writes into kernel side-tables that have no committed column or systemRoot." The deployed `compute_commitment` (`cell_state.rs:76`) binds only balance/nonce/8-fields/cap_root. Matters because these are the hardest set-membership soundness rungs and remain unbound.
**Recommendation:** Bind the set-membership effects (nullifier/commitment accumulator roots, queue FIFO root, seal-box) into a committed column/systemRoot via genuine in-circuit root recompute (the "sorted-Poseidon2 everywhere" unification), have the runtime emit them, then discharge a setField-style refinement. Runtime+circuit, not Lean-only.

**META-FILL F Rust preimage differential never built (Lean signing-message bytes vs Rust `compute_signing_message`)** — *meta-fill session*
`metatheory/Dregg2/Exec/SigningMessage.lean` has complete byte-exact preimage builders (`sigMsgFull:151`, partial/custom/stealth/bearer/handoffCert) + `*_hasPrefix` domain-separation theorems, but NO `@[export]`/extern (not even FFI-exposed) and NO Rust byte-equality test anywhere. `compute_signing_message` exists in ~20 Rust files but is never differentially pinned to the Lean preimage; no HORIZONLOG line, no commit. Matters because the Lean signing-message proofs are unpinned to the deployed signer.
**Recommendation:** Add `@[export]` to the `sigMsg*` builders + a `dregg-lean-ffi` differential test asserting Lean preimage bytes == Rust `compute_signing_message`/partial/custom/stealth bytes. Add the HORIZONLOG line in the same breath.

**FoldAir leaves `new_root` free; legacy `dsl/fold.rs` folds arbitrary caveats (no in-AIR Merkle membership)** — *fold-air session*
The PRODUCTION path is fixed (in-AIR `merkle_air.rs` validated-IVC + cap-reshape openable `capability_root`, #103). But legacy `dsl/fold.rs` still has the gap: `RemovedFact::verify_membership` (`:83-107`) walks the Poseidon2 path in Rust `generate_trace` not in-AIR; `HASH_VALID` is set to ONE by the prover (`:316`), constrained only binary+required; `new_root` is a free PI whose only constraint is the tautology `row[NEW_ROOT]-pi[1]`. The obligation doc only names a *different* cosmetic fold. Matters because if this fold is on any live trust path, a federation member folds arbitrary caveats.
**Recommendation:** Determine whether `dsl/fold.rs` FoldAir is still on a live trust path or fully superseded by validated-IVC/cap-reshape. If live, port `verify_membership` into the audited `MerkleAir` and constrain `new_root` as a Merkle update. If dead, delete it.

### follow-up

**starbridge-v2 native cockpit embedding the LIVE affordance surfaces — render PIPE landed, interactive embedding QUEUED** — *desktop-frontier session*
`GPUI-OFFSCREEN-FORK.md`: the landed render bakes the live cockpit element tree over `world::demo_world` into the PD as raw RGBA (`cockpit_frame.rgba`, 1.92MiB) — a SEEDED/baked frame, not interactive surfaces. `SEL4-INTERACTIVE-COCKPIT.md` (newest doc, `3a4ae70ca`) is design+scaffold for live-repaint-on-turn; input is "NOT greenfield (virtio-keyboard already boots; cockpit mode just discards nav)." `DEOS.md:131` QUEUES the embedding behind the rotation hardswap. Matters because this is MEMORY's "#1 PRECIOUS" and the landed PIPE is easy to misread as done.
**Recommendation:** Drive the live interactive per-viewer affordance-surface embedding + repaint-on-turn (scaffolded in `SEL4-INTERACTIVE-COCKPIT.md`), gated on the rotation hardswap clearing metatheory/turn/node. The most actionable + highest-value of the desktop strands.

### parked-lane

**The 6 light-client trust-surface smuggles — sequential VK-affecting burn-down (the active campaign)** — *trust-surface session*
`docs/LIGHT-CLIENT-TRUST-SURFACE.md` (revised to live HEAD in `b0f1aa51f`) DoD: commit-width ✅ FORCED ~124-bit (`9e5a83935`); #4 replay ✅ FORCED; #5 fee ✅ FORCED-LIVE. STILL OPEN: #1 refusal+setFieldDyn authority (anchored off-circuit, needs openable-fields_root #103); #2 whole-turn lead-only; #3 agent signature (largest long-pole, Ed25519 AIR); #6 cross-cell Σδ=0; #8 non-vacuity. The untracked working-tree AIRs/Lean confirm #2/#3/#6/#8 mid-flight right now. Matters because this IS the #1 campaign and the per-smuggle granularity must not collapse into one line.
**Recommendation:** Continue the sequential burn-down; drive the in-flight strands to commit + WIRE into `proof_verify.rs` (currently standalone modules, not on the deployed sovereign per-cell path). Integrate by file-set. #3 (Ed25519) is the long-pole. *(This entry subsumes the duplicate smuggle-table candidates; #2/#3/#6 also appear above as individual bug/draft entries.)*

---

## MEDIUM

### bug-or-soundness

**compute_marketplace atomic multi-cell action silently DROPS the reputation `set_field` yet COMMITS** — *round-8 session*
Commit `ed3b2bc46`'s message lists "compute_marketplace's unmasked multi-cell reputation set_field drop" as a pre-existing defect "HORIZONLOG'd … flagged loudly, not papered" — but a grep of the live HORIZONLOG finds NO such entry (the named follow-up the commit claimed to record is absent), and no closing commit exists since. `demo-agent/examples/compute_marketplace.rs:507-518` still issues escrow+reputation+receipt_log `set_field`s in one atomic settle turn and asserts `total_jobs=1` at `:592`. Matters because a multi-cell turn that drops a state write yet commits is an executor atomicity/conservation hole.
**Recommendation:** Run `cargo run -p dregg-demo-agent --example compute_marketplace`; if the assert fails (left 0 right 1), fix the executor apply path so a dropped per-cell write ABORTS the turn (not the example), and re-add the HORIZONLOG line.

**circuit note-spend DSL self-inconsistency: `create_test_witness` produces a trace the AIR rejects; `note_spending.rs` has ZERO `#[test]`** — *triage session*
`grep -c '#[test]' circuit/src/dsl/note_spending.rs` = 0 at HEAD (34KB file). `create_test_witness` is imported (`:48`) and the witness generators present but never tested against the AIR; the only commit since the flag is a clippy green-drive. Matters because an untested witness generator that contradicts its own AIR is a latent soundness/correctness inconsistency.
**Recommendation:** Add a `#[test]` running `create_test_witness` → `generate_note_spending_trace` → `NoteSpendingAir` constraint check; this exposes the inconsistency. Fix whichever side is wrong (likely the witness generator vs the AIR's expected trace).

### unintegrated-draft

**Coordinated/bilateral turn: covenant φ guard is a binding propBit gate, full polynomial φ deferred** — *coordinated-turn session*
`CoordinatedTurnEmit.lean` has no open holes; the covenant guard is a real binding gate (`cCTCovenantGuard {vCovenantGuard=1}`, `propBit(step.covenant.φ … = true)`) with proven `ct_pub_charter_iff` + Wave-6 `covenantGuard_of_emitted`/teeth. But `:300` still reads "scaffold; full polynomial φ deferred" — φ is enforced via a propBit witness column, NOT in-circuit φ recompute. `DESIGN-recursion-aggregation-private-joint-turns.md` is stale (cites line-619 open holes that no longer exist). Matters because the residual propBit-vs-polynomial gap is the difference between a witnessed guard and a recomputed one.
**Recommendation:** Mostly closed (genuine binding gate + refinement lemma + teeth, not a no-op). Refresh the stale DESIGN doc; decide whether the propBit-vs-polynomial-φ gap warrants closure.

### follow-up

**Bearer/token producer-admit e2e for REAL credentials — named "so it isn't lost," never landed** — *producer-mode session*
`node/tests/lean_producer_mode.rs` has only transfer/setfield/cell_unseal producer tests; no bearer/token. `HORIZONLOG.md:2078-2087` records the latent gap: a genuine bearer/token turn carries `deleg_msg`/`issuer_key` as full-256 digest vs low-64 `deleg_sig`/`sig` (the same width-mismatch class the Signature fix closed), "LATENT because no test drives a real bearer/token turn through `DREGG_LEAN_PRODUCER=1`." Matters because it's a latent veto-a-genuine-credential gap.
**Recommendation:** Add the `sig_echo_wire` treatment for bearer/token + an e2e producer test submitting a genuine bearer/token turn under `DREGG_LEAN_PRODUCER=1` asserting ADMIT.

**Divergence-ledger test overwrites a git-tracked `.md` on every run — swarm-unsafe, blocks persvati pushes** — *divergence-finder session*
`turn/tests/rust_lean_divergence_finder.rs:936` `std::fs::write(&path, md)` where path (`:815-825`) is the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md`. `HORIZONLOG.md:1819` records it dirties trees + blocks persvati pushes, "one-line fix … STILL LIVE." Matters because tree-dirtying is not a swarm-safe operation and every parallel agent shares the working dir.
**Recommendation:** Redirect the write to a build-artifact path (`target/` or `OUT_DIR`). Trivial.

**Ethereum settlement Groth16-of-STARK wrapper — in-repo scaffold, crypto core in sibling repos, progressing** — *EVM-bridge session*
`bridge/src/ethereum.rs::wrap_for_ethereum` still produces a blake3 `BindingOnly` artifact and only validates externally-supplied SNARK bytes; the module doc still says the Groth16 circuit "is NOT in this repo." But `HORIZONLOG.md:978-1020` documents a named campaign: rung (B) VALIDATED (`dregg-circuit --features verifier` cross-compiles to `riscv32im-risc0-zkvm-elf`; `RiscZeroGroth16Verifier` + `DreggBridgeVault.sol` compile under foundry), rung (C) Step 1 BUILT+GREEN at `~/dev/plonky3-bn254-wrap` (`e80f499`); gnark wrap at `~/dev/dregg-gnark-wrap`. Matters because the in-repo doc reads more dormant than the campaign is.
**Recommendation:** Carry as the EVM-bridge closure lane (run (B) zkVM wrap end-to-end on a 24-core box; finish (C) Plonky3-BN254 steps 2-3). Refresh the `ethereum.rs` module doc to point at `docs/EVM-BRIDGE.md`. The crypto core remains genuinely unbuilt-to-ship.

### design-idea

**Real-time / interactive tempo for deos apps (#169) — framework primitive built, no app consumes it** — *deos-apps session*
`app-framework/src/optimistic_fire.rs` (`OptimisticFire::predict/settle`, same anti-ghost cap-gate both tempos) + `deos_app.rs:229 DeosCell::predict` landed (`7d7726879`). But `rg 'optimistic_fire|OptimisticFire|\.predict('` across `starbridge-apps/`/`starbridge-web-surface/` = ZERO; tussle is frame-based but still commit/reveal turn-paced; `DEOS-APPS.md §gap#3` still reads "no app realizes it." Matters because the live tempo is the "webby/live-desktop" feel the deos-ux vision wants.
**Recommendation:** Gap narrowed from design-only to framework-built-but-unconsumed. Have one app (tussle or the webgame) call `DeosCell::predict` to realize the live tempo.

**Membrane-negotiation UX (C2): non-amp Lean landed, negotiation meet-algebra + UI unbuilt** — *frustum-replay session*
`metatheory/Dregg2/Deos/Membrane.lean` exists (`d738f2c84`) proving reshare/non-amplification (the surface-as-cap crown), but the C2 negotiation-algebra theorems are absent (`rg 'negotiation_meet_assoc_comm|deputy_confers_no_unheld_target'` = 0). `FRUSTUM-REPLAY-MEMBRANE.md §C2` still lists them open + "the negotiation UX (GitHub-org-settings surface) remains genuinely unbuilt"; `DEOS.md:130` QUEUES the membrane into the live captp sturdyref path. Matters because the cross-membrane negotiation UX is load-bearing for the agent-first-class vision.
**Recommendation:** Re-scope to "C2 negotiation algebra + UX" (the broad "no Lean" framing is outdated). The meet-algebra (assoc/comm/deputy-confers) and propose/counter/accept UX are genuinely unbuilt; live-captp wiring is queued behind the rotation hardswap.

**Agent-as-first-class-user deos shape — agent-orchestration app realizes the thesis, cross-membrane negotiation thin** — *deos-apps session*
`starbridge-apps/agent-orchestration` is a real agent-primary app: Mandate (attenuated tool-set ∧ sub-budget ∧ sub-task, granted⊑held), every worker action a cap-gated verified turn, MCP binding (`src/mcp.rs`), per-viewer cap-projection, durable crash-recoverable workflow, auditable receipts. But no `AgentSpec` primitive in `app-framework`, and the cross-membrane agent-negotiation UX rides on the unbuilt C2. Matters because this is the heart of the refinement-epoch not-a-toy goal.
**Recommendation:** Downgrade from "unbuilt" — the app substantially exercises the thesis. The cross-membrane negotiation leg depends on C2 and remains thin.

### parked-lane / unclear

**dregg-analyzer live-capture half — crate built + attesting, but no node trace-export or Studio binding** — *think-big / FRONTIER-BACKLOG 2e.4*
The crate is substantial (`blocklace.rs`/`receipts.rs`/`wal.rs`/`network.rs`/`forest.rs`/`findings.rs` + 24KB tests; capture types defined; analysis attests against real verifiers; `dregg-analyze` CLI exists; landed `14a32e3e2`/`2e5c2d5f4`). But `rg` finds NO node-side trace-export endpoint, NO producers of the Capture types outside the analyzer's own tests, NO `AnalysisReport` rendering in starbridge-v2/studio/site — captures must be hand-built. Matters because the wire types are already exact, so the live hook is thin.
**Recommendation:** Promote 2e.4's first clause to a real lane: add a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from a running node, then bind `AnalysisReport` into the shell. Size M, wide-safe.

**Rust-side guarded-holes / partial-turn as a first-class EFFECT — circuit-scope lift un-owned** — *partial-turn session*
The metatheory study + a first-class WEAK guarded hole landed (`556c5de32`/`5d38c4386`/`e2e3e52ad`; `Dregg2.Exec.GuardedHole` + `execConditionalTurn`; `holeFill_binds_in_circuit` keystone). But `rg 'ConditionalBatch|GuardedHole|holeFill|EventualRef'` in `circuit/` = NOTHING; no descriptor for a conditional/partial/hole/batch effect; the apex fold's `FullForestA` has no batch-bearing node. The three honest open questions (is the circuit in scope; new Effect variant vs reflection; what commits slot-fills) remain un-owned at the circuit layer. Matters because the spec/executor braid is closed but the in-circuit lift isn't.
**Recommendation:** Correctly deferred behind circuit-soundness completeness. When the apex obligation table clears, scope the circuit-feasibility question against `execConditionalTurn` + `FullForest` + the apex fold before claiming payoff.

### bug-or-soundness (proof-corpus)

**Orphan-rot class: unimported non-compiling Lean modules silently broken (`CapTPHandoffSound.lean`)** — *coherence/orphan session*
`metatheory/lakefile.toml`: the Dregg2 lib is import-rooted (no globs); only the Metatheory lib is globbed. So any unimported `Dregg2/*` module silently rots — `lake build Dregg2` never compiles it. `CapTPHandoffSound.lean` is NOT in the compiled-import closure and nothing imports it (`grep 'import Dregg2.Exec.CapTPHandoffSound'` = 0). Ad-hoc repairs landed (`e3a500eb5`, `1a772e128`) but no systematic mechanism; 1410 `.lean` files. Matters because orphans counted as assurance is exactly the "don't launder vacuity" hazard.
**Recommendation:** Convert the Dregg2 lib to globbed (like Metatheory) OR add a CI step compiling every `Dregg2/*.lean` (fail-closed on orphans), catching the whole class in one move. Re-anchor or delete `CapTPHandoffSound.lean`.

---

## LOW

### follow-up

**Trustline pureCredit HTTP open lane: `parse_collateral` dead code, `OpenRequest` fullReserve-only** — *trustline session*
`node/src/trustline_service.rs:393-400` TODO(collateral-axis): "the node OpenRequest does not yet carry a collateral field, so the HTTP open path is fullReserve-only"; `:401 fn parse_collateral` is `#[allow(dead_code)]`; the `OpenRequest` struct (`:623`) has no collateral field. Rust semantics + SDK (`dregg_sdk::trustline::open_with_collateral`) exist. Matters little — fullReserve works; this is built-but-disconnected.
**Recommendation:** Add `OpenRequest.collateral` + a pureCredit funding branch (escrows nothing) and route `parse_collateral`. Low priority.

**Store-and-forward signed CustodyReceipt keystone (~50 lines)** — *relay session*
`node/src/relay_service.rs` (60KB) has ZERO `CustodyReceipt`/`custody` hits; no `CustodyReceipt.lean` or Rust keystone landed; last substantive commit is the unrelated mailbox crank. Matters little — delay-tolerant relay accountability is off the live light-client critical path.
**Recommendation:** Leave parked or schedule as a self-contained ~50-line keystone when the relay lane is next active.

**`Spec/Prelude.lean` shared-vocabulary refactor (Coherence §7) never built** — *coherence session*
No `metatheory/Dregg2/Spec/Prelude.lean` exists; no commit references the refactor. The planned consolidation of independently-declared Spec types onto one shared vocabulary was never executed (`Spec/Coherence.lean` exists but not the Prelude consolidation it named). Matters little — a tidy-refactor, not soundness; serves the "theories don't interrelate" concern.
**Recommendation:** Schedule only if a Spec-module dedup pass is wanted; otherwise demote to Research with that note (per WE-DO-NOT-NAME-WE-SHIP, it shouldn't sit unscheduled).

### unintegrated-draft / parked

**RecordKernel "store commitments in state" (Mina-style) half — silently designed out, no parked-question home** — *record-reshape session*
The additive `fields_root` map landed (`RECOVERED-DESIGNS.md:22`, `RECORD-DIGEST-SPLIT-RESHAPE.md`). But the SECOND RecordKernel ambition — storing commitments INSIDE the enlarged state (the "Mina did this too" half) — has no doc recording it as adopted OR as a named open question; the simpler accumulator shipped and the alternative was collapsed out. Matters little — the chosen path is sound; this is an un-parked fork, not a bug.
**Recommendation:** If ember cares about the state-resident-commitments direction, add one explicit parked line naming why `fields_root` was chosen over it. Not urgent.

**Devnet redeploy of the assured dregg3 node — explicit ember-gated park** — *reorient*
`REORIENT.md:99/451/473` + `HORIZONLOG.md:1564`: "devnet redeploy = EMBER's act (fresh genesis), HELD for ember"; Fable 5 suspended by a US export-control directive (`seal-note-fable-5-2026-06-12.md`). Local main has advanced far past the live pre-epoch binary. Matters as context, not as a slip — a deliberate ember-decision park.
**Recommendation:** No agent action — keep accumulating enhancements (which is happening).

---

## RESEARCH

**Unbounded IVC accumulator driver — the "Gold" continuous accumulator, named-open** — *IVC session*
`circuit/src/ivc_turn_chain.rs:1265` "## What the UNBOUNDED driver still needs (named open) … wiring it to the node's live finality stream and persisting the running output across restarts." No closure commit; the bounded K-fold (K=4) is what landed. Forward-vision, not a defect.
**Recommendation:** Pursue when the light-client running-proof-across-restarts story is the focus. Not urgent.

**Think-bigger non-conservation assurance domains (bounds/no-overflow, relational/octagon/zone) in-circuit** — *think-bigger steer*
No in-circuit non-conservation abstract-interpretation beachhead exists (`rg octagon/RelationalCaveat/interval-domain` in `circuit/src` = only incidental bounds-check mentions). The relational work that landed (`4173d6103`, `Authority/RelationalClosure.lean`, `TemporalAlgebra.lean`) is metatheory authority-algebra, not an in-circuit non-conservation predicate domain; the trust campaign stayed pinned to conservation/authority smuggles — the "pedestal" ember de-emphasized. Faithful to "conservation is boring."
**Recommendation:** Gated behind "after trust closed." Beachhead one non-conservation in-circuit domain (bounds/no-overflow is the cheapest entry) once the soundness apex lands.

**`docs/RECOVERED-DESIGNS.md` — ~16 specced-but-unbuilt designs banked from the 100-md audit** — *recovered-designs audit*
The doc is unchanged durable memory; the bulk (notify-as-authority, ADOS narration→effect compiler, macaroon↔cap-crown bridge, `fields_root` map, cap-root IR hash site, embedded servo) show no closing commits. A parking-lot ledger by construction, not an open bug.
**Recommendation:** Per WE-DO-NOT-NAME-WE-SHIP, pull the 1-2 highest-leverage items (macaroon↔cap-crown one-lemma bridge; notify-as-authority ~9-site edit) into HORIZONLOG with a closure lane, and explicitly demote the rest to Research. The doc itself is fine as memory.

**MM-bridging proof — explicitly-optional upstream contribution, superseded by dregg3** — *pre-dregg3 (2026-05-17/20)*
No `mm_step`/`MM-bridging`/`stellar-resolution` references in the live tree or git history; not in the dregg3 redesign. The in-scope MM proof was completed; only the upstream bridge was parked, marked COMPLETE in the original note. No soundness debt in the live substrate.
**Recommendation:** Treat as research/dropped. Resurface only if an upstream UC/MM publication is desired.

---

## OUT OF SCOPE — wrong repo (re-verify elsewhere, NOT breadstuffs)

These candidates pertain to `~/dev/allgame` or `~/dev/rig`, not dregg. Recorded here only so they aren't re-swept against the wrong tree; **adjudicate in their home repos.**

- **Live Zulip API credentials in local git history** (`.zuliprc-gemma`/`.zuliprc-sonnet46`) — HIGH if keys never rotated. Files live in `~/dev/allgame`; zero breadstuffs hits. **Re-verify in allgame; a gitignore + history-rewrite does NOT rotate a leaked key.**
- **allgame "resident family" arc committed-but-not-pushed** — residents present at allgame HEAD hint it landed; check the 9-commit series (HEAD `73d404e`) against `origin/dev`.
- **Nemo (Nemotron) persona + extractor/code-leak fixes uncommitted** — `nemotron_resident.py` is at allgame HEAD; verify the specific fenced-tool-call extractor + code-fence-strip fixes via `git log -p`.
- **MAPPO/MARL analytical backprop never implemented** — belongs to `~/dev/rig` (or allgame `game/rl/`); grep analytical-backprop vs the documented ES-gradient bottleneck.
- **"rust-eval-harness" subagent never launched** (`rig-core/src/eval.rs`) — likely resolved-by-rename to `skill_eval.rs` in rig; reconcile there.
- **graphplay prove-everything: 8 killed proof agents' drafts** — `~/dev/graphplay`; the lost drafts are unrecoverable, but open-hole-closing was carried forward by waves 21/22. Re-target the remaining specific open holes (`Path.lean`, `DistributedQuotient`) with fresh agents rather than mourning the aborted run.
- **Completed subagent report lost to a plan-mode rewind** — rig/allgame era; unrecoverable by nature. Re-derive findings if they matter.
