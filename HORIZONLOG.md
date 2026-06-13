# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

Last sweep: 2026-06-12 (the Grand Convergence session).

## Rides THE ROTATION (dies at or lands with the one VK epoch — do not do separately)

- sbox_registers→0 descriptor metadata (chip uses inline x⁷; named in 0b05afc1a) — flip at the closing-ceremony regen.
- RESERVED mask removal + 186→159 column compaction (REORIENT EPOCH STATUS).
- registers 8→16 + FactoryDescriptor.fields · PI v3 (committed-height + rateBound/challengeWindow) · heap_root register.
- iroot bound into recStateCommit (non-omission obligation, 9dcd42cd9).
- cap-reshape phase D (in-circuit cap crown completion; #103 audit: A–C done, D deferred-by-design).
- #150 confirmation: does the umem `absent` + sorted-gap boundary fully retire DslRevocationTree (TREE_DEPTH=4)? One read-pass at cutover.
- fresh-key sorted-INSERT map-op (reuses MapAbsent adjacency; named in cff8509ba).
- per-turn chip amortization (blocked on an IR-v2 turn assembly; named in 0b05afc1a).
- MMR §6 CommitBindsMMR layout fact (node writes both roots at dense positions; the Receipt-apex residual premise, 7894e5789) — discharged-by-construction at the flag-day.
- ~~Full-cohort descriptor regen at the ROTATED 25-slot block~~ STAGED (2026-06-12): `EffectVmEmitRotationV3.lean::v3Registry` re-emits all 26 cohort members at the rotated R=24 block via ONE parametric `rotateV3`; keystones lift ONCE (`rotateV3_satisfiedVm_v1`, `rotV3_binds_published`), axiom-clean; Rust twin `rotation-v3-staged-registry.tsv` sha-pinned + coverage test. The FLIP (§3 steps 1-6) — replacing the live v1 registry — remains the main loop's act at the VK epoch.
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (`turn/src/rotation_witness.rs`, NAMED in EffectVmEmitRotationV3.lean §3; the rotated block's first/last limbs; MMR theory landed, executor carrier + a Rust MMR/cells-root primitive both missing) + lifecycle/epoch trace carriers (CellState tracks them — umem projection maps them, the trace doesn't) — ROTATION-CUTOVER.md §5 items 3-5. SEQUENCING (confirmed 2026-06-12): build these WITH the flip's rotated trace builder, not before — a producer is unvalidatable until a verifier consumes the rotated commitment; no live consumer exists while it is staged.

## LOAD-BEARING NOW (promoted 2026-06-12 — the register argument depends on these)

- Heap-addressable constraint language: program atoms that gate HEAP KEYS, not just slot
  indices (the executor already admits heap fields, b133354fc; the "registers are the L1,
  heap is where apps live" argument is VACUOUS until programs can constrain heap fields).
  Lean Exec.Program + cell/program.rs lockstep + the DSL surface. = the language-uplift R3
  named-fields work, now critical path. LANDED 2026-06-12 (this lane): Lean
  `HeapAtom`/`HeapAtom.lift`/`evalHeap` + absence-as-theorems (Exec/Program.lean, welded to
  `FieldsMap.userKey`); Rust `HeapField { key, atom }` in BOTH constraint enums +
  `evaluate_heap_atom`; executor-enforced (turn test
  `test_program_heap_field_constraint_enforced`, coverage-gate arm true); blueprint
  proof-of-life (channel + heap counter in one program). REMAINS (this lane's tail):
  (a) the DSL surface atom (dregg-dsl has no heap-keyed syntax yet — programs construct
  `StateConstraint::HeapField` directly); (b) multi-key heap atoms (prefixOf/affine/
  sumEquals over heap keys — only single-key atoms lifted); (c) heap-keyed caveat operand:
  wire shape STAGED 2026-06-12 (the line below) — the runtime discharge remains.
- HEAP-KEYED CAVEATS wire shape: **STAGED 2026-06-12** (this lane) — the widened operand
  is `(domain_tag, key)` on the umem `domainCode` codes (registers 0 · heap 1; key u8→felt;
  entry = 7 felts, manifest = 29), Lean-first in `EffectVmEmitRotationCaveat.lean`
  (no-aliasing keystone `caveat_operand_no_aliasing`, `caveatCommit_binds`, the R=24 probe
  `rotationCaveatProbe_binds_published`) + Rust staged twins/teeth (`rotation::caveat`,
  `RotCaveatEntry` fail-closed decode, forged-domain/tampered-heap-key refusals; pins
  byte-frozen, live v1 manifest untouched). ROTATION-CUTOVER §3 pre-gate ✓. REMAINS:
  (a) the EXECUTOR runtime discharge of heap-domain entries (named premise
  `HeapCaveatRuntimeDischarge`; template = `verify_slot_caveat_manifest`; semantics
  already welded via `tagHeapAtom` → `HeapAtom.lift` → `evalHeap`) — ROTATION-CUTOVER §5
  item 9; (b) at the flag-day the staged 29-felt manifest replaces the live 25-felt slot
  manifest in the regenerated PI region.
- guardAtom IR kind (umem adapter c) confirmed NOT landed (absent from DescriptorIR2.lean
  + descriptor_ir2.rs): in-circuit policy/caveat enforcement for v2/v3 = cap-crown phase D
  + Policy.lean line, rides rotation — now confirmed-open, not quietly-done.
- PI v3 rateBound/challengeWindow tags: LOOKED 2026-06-12 — **carried-only**: the producer
  copies context values into PI 202/203 (trace.rs) and the verifier PINS BOTH TO ZERO
  sentinels (proof_verify.rs:269-270); no AIR constraint and no caveat-layer evaluator
  reads them. Enforcement arrives with the optimistic-proving/dispute modes (#169), which
  already own these slots by name — nothing further pre-#169.
- PI v3 producer/verifier tear (RED at HEAD): 007c2f1d2 bumped `inner_pi::ACTIVE_BASE_COUNT`
  to 204 but the witness producer still emits 201 PIs, so
  `node blocklace_sync::tests::distributed_witness_path_gossip_materialize_aggregate_verify`
  fails ("bilateral bundle entry 0 has 201 public inputs, expected at least 204",
  turn/src/executor/proof_verify.rs:1465) — the PI v3 lane closes producer emission to the
  new layout (found red by the remote-lane finisher 2026-06-12; unrelated to #170/#171).
- Register-count: MEASURED + CONFIRMED R=24 (ember 2026-06-12, "22 it is") — pre-gate ✓; remaining work rides the regen. (was: measurement: MEASURED (2026-06-12) — 16/24/32 probes from the parametric
  Lean emission (`EffectVmEmitRotationR.lean`; `wireCommitR_binds` parametric in R; R=16
  byte-identical to the pinned artifacts), proved+verified+toothed at production
  `ir2_config`: 94.4 / 96.5 / 99.8 KiB. Table + verdict in ROTATION-CUTOVER.md §2b —
  recommendation R=24 (+2.2 KiB always-paid per turn, 22 app registers, exact 3-fill
  chunking). REMAINS: ember confirms R (the §3 pre-gate checkbox).

## Metatheory closures (Lean-side, mostly lane-sized)

- ~~CrashRecovery × registries: extend the recovery model to `(writes, burns)` and lift `draw_replay_refused_across_epochs` across the crash cut~~ CLOSED (metatheory-closures lane, `Dregg2/Distributed/CrashRecovery.lean`): `BRecord` carries `(writes, burns)`; `registry` folds the per-step burn carrier and `registry_append`/`registry_mono`/`registry_cut_independent` make it append-only and crash-cut-independent; `recoverB_eq_replayB` recovers through the forever table; KEYSTONE `draw_replay_refused_across_crash` — a burn in `registry (tlLog s₀ sched n)` makes `drawS srec d amt = none` on ANY recovered cell (`recoverB … = some srec`), so a replayed draw is refused ACROSS the crash cut, riding `registry_burn_in_draws` + `tlLog_recover`. `#assert_axioms`-clean; both-polarity `#guard`s (lost/stale recovery; the forever table load-bearing).
- ~~Channels: program-readable `delegation_epoch`~~ CLOSED (executor-atoms lane): `DelegationEpochEquals` atom (Rust both enums + `TransitionMeta::delegation_epoch` per-cell stamp; Lean `delegationEpochEquals` + iff/absence theorems); channel blueprint constraint 6 installs it; `DelegationEpochTie` DISCHARGED on admitted turns (`admitted_ties_delegation_epoch` + `remove_darkens_both_discharged`; premise form kept for foreign/pre-atom states). Tails: the Lean-producer/wire path has no per-cell delegation_epoch carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- ~~Channels: count-equal / order-statistic constraint atom~~ CLOSED (executor-atoms lane): `CountGe{threshold, set_commitment_slot}` — the witness RE-EXHIBITS the distinct element set each turn against the openable sorted-set commitment (the anti-affineLe-flag design); Lean `countGe` + `councilGated` keystones; `council_count_ge_shape` blueprint test + `test_program_count_ge_enforced` executor test. Tails: per-element approval binding (exhibited ≠ "approved THIS turn") — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the DEPLOYED channel program; CountGe AIR projection (witness-side scalar enforcement only; classified no-SlotCaveat-projection).
- ~~Argus fee-wrapper conservation: `FeeChainStep` + `wellformed_history_conserves_modulo_burn`~~ CLOSED (metatheory-closures lane, `Dregg2/Distributed/FeeHistory.lean` — a dedicated module consuming `HistoryAggregation`, cleaner than inlining there): `FeeChainStep` = one ACCEPTED `runTurn` (`commits : runTurn … = .bodyCommitted post`; fee cells load-bearing fields) with `runTurn_bodyCommitted_inv` the accepted-outcome inversion; per-step keystone `feeStep_conserves_modulo_burn` (recTotal moves by EXACTLY `−feeBurned` via owned `recTotal_commitPrologue`/`recTotal_distributeFee`/`transfer_body_total_frame`) → HEADLINE `wellformed_history_conserves_modulo_burn` (`recTotal endpoint + totalBurn = recTotal genesis` over ANY state-chained fee history, additively); `feeStep_exposes_body_strand_step` consumes the Aggregate §6 body-strand link (the fee chain rides the light-client strand, not re-proved). `#assert_axioms`-clean; both-polarity `#guard`s EXECUTED (real accepted transfer 100→98; `=100`/`=90` both FALSE).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- ~~QueueRoot/commitment: leaf/node level-tags + length binding in `blake3_binary_root` (domain separation is computational-only today)~~ CLOSED (metatheory-closures lane, `Dregg2/Apps/QueueRoot.lean` §7): the hardened `taggedRoot tagLeaf combine bindLen` adds leaf/node level-tags (`tagLeaf`) + a length-binding outer layer (`bindLen`/`LenBindCR`), and KEYSTONE `taggedRoot_injective` proves it injective on ALL leaf lists under only the three per-domain CR carriers — RETIRING the zero-free restriction (`tag_separation_kills_passthrough`/`tagged_kills_pad_alias` witness the old `refRoot` pad-alias dying); `taggedRoot_RootCR` lifts every zero-free-keyed keystone to it for free, and `tagged_dequeue_proof_pins` re-runs the verifier-soundness proof on the hardened root. `#assert_axioms`-clean; both-polarity `#guard`s. (The pad-alias `refRoot` carrier — `padded_root_not_fully_injective` — kept as the documented contrast; full injectivity needs no zero-free premise on the tagged root.)
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- ~~Fibration (#35): `DistConservationBound`/`DistAttenuationBound` carried hypotheses → theorems~~ CLOSED (metatheory-closures lane, `Dregg2/Distributed/Fibration.lean` §12/§13): both bounds get DERIVED witnesses, not just structure-hypotheses. `distConservationBound_derived` builds a `DistConservationBound` from `wellformed_history_conserves` (window 0 even off-apex — prefix-closure beats reconciliation), discharged through the §8 machinery (`conservation_discharged_collapse`) and fired on a real executed teeth chain (`conservation_fibre_real`). `distAttenuationBound_derived` builds a `DistAttenuationBound` from the revocation fibre (`eventual_bounded_revocation` window + window-free `attenuate_narrows` narrowing + instantaneous-apex collapse), with the NEGATIVE tooth preserved (`att_fibre_weakens_offApex` — strictly-positive window AND stale broad token still honored inside it) and `att_fibre_terminal` the single-machine collapse. `#assert_axioms`-clean across both discharges. (Bonus item beyond the four assigned files; #35 named open closed by exactly the derivation §9 prescribed.)
- ~~Quorum unification (#170) Lean lift: the unified formula's Lean twin~~ LANDED (`Dregg2/Distributed/QuorumThreshold.lean`): `supermajorityThreshold n = ⌊2n/3⌋+1` byte-for-byte `dregg_blocklace::supermajority_threshold` + the n=0 fail-closed pin + `threshold_monotone` + UNCONDITIONAL `supermajority_intersection`/`two_quorums_share_honest` (no `StrictBft` caveat — the n=3f hole witnessed NEGATIVE/closed POSITIVE) + `historical_relation` pinning the exact `+1 at 3∣n` gap; `#assert_axioms`-clean, wired into `Dregg2.lean`. Tails: MIGRATE the consumers onto it — `BlsQuorumCert.lean`/`EpochReconfig.lean` still transcribe the historical `n−⌊n/3⌋` and carry `StrictBft`; `MembershipSafety.lean` still has the `n=0 ↦ 0` guard (bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the relations until the consumer migration).

## Node / runtime closures

- ~~Same-transaction burn weld~~ LANDED (`persist/src/commit_log.rs::commit_finalized_turn_with_burns` + the `(height, creator, ordinal)` index key + boot migration + welded test `burns_land_atomically_with_the_commit_record`): the in-turn API burns a turn's anti-replay digests in the SAME redb txn as its `CommitRecord` (crash ⇒ both or neither). `commit_finalized_turn` now delegates to it with no burns. ALL current burn sites (trustline draw/settle, court verdict) are OUT-OF-TURN — the route mutates the live ledger and burns journal-first (`record_digest_durable`/`execute_slash` step 6 commit the digest BEFORE the ack; the route turn's `CommitRecord` is written later on the consensus path), so the weld is the available mechanism for any future in-turn finalizer; the out-of-turn carrier is documented journal-first (docs/PERSISTENCE.md §3, the in-turn-vs-out-of-turn split).
- ~~Channel room rosters durable table~~ LANDED (`persist/src/channel_rosters.rs` + `node/src/channels_service.rs::{persist_roster,ChannelRegistry::restore_rosters}` + state.rs boot wiring): every committed epoch step (open/join/remove/rekey) persists `(anchor, members)` in one txn; boot rebuilds each room AFTER re-committing it against the recovered ledger's on-cell `member_root` (mismatch/missing/non-channel ⇒ discard + durable remove, no re-alarm). A restart no longer serves `RosterStale` for a roster still matching its cell; epoch keys are node-minted secrets, NOT persisted (a rekey re-establishes forward delivery). Restart-shaped tests: persist `channel_rosters_roundtrip_and_survive_reopen` + node `roster_survives_a_simulated_restart_and_stale_is_discarded`.
- Stale-cap c-list sweep: epoch-step turn also `RevokeCapability`s superseded grants (channels 72d43dc64 residue). STILL OPEN — and it is a real verb gap, not a quick fix: `member_cap_grants` installs caps into each MEMBER's c-list (`GrantCapability { to: member }`), while `RevokeCapability { cell, slot }` removes from a cell's OWN c-list. Sweeping a departed member's superseded grant therefore needs `RevokeCapability` targeting the MEMBER cell, which requires the group operator to hold cross-cell `Delegate` authority over each member — authority it does not generally hold (`apply_revoke_capability`, `turn/src/executor/apply.rs`). Today the `RevokeDelegation` epoch bump already DARKENS every prior-epoch group cap at admission (R7 `CapabilityStale`), so this is c-list GC (storage), not a soundness hole. The honest closure is a new verb shape (member-initiated self-revoke, or a group-scoped revoke authority), NOT a hack onto the existing one.
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues). STILL OPEN — the bond cell is a plain operator-owned cell, not yet deployed via the obligation factory so its program pins "only the slash turn moves this balance" (today an unrestored bond fails CLOSED — `NothingAtStake`). The enabling `obligation_factory_descriptor` (CreateObligation/Fulfill/Slash) is the +1467-line `cell/src/blueprint.rs` work of the FLASH-WELL/blueprint lane, currently UNCOMMITTED + sprint-UNVERIFIED; wiring court onto it now would couple this lane to that one's unverified state and risk green. Deferred to AFTER that blueprint lands+verifies; then `post_bond` deploys the bond cell via the factory in one slice.
- ~~persist/ dregg1 residue retirement~~ LANDED: tokens.rs / recovery.rs / keys.rs / audit.rs DELETED (re-verified zero external consumers by grep — all `token_count`/`token_counter` hits are unrelated wasm/cli/node-local fields, not the persist store's methods/types; no `persist::{audit,keys,recovery,tokens}` paths or re-exports anywhere). Their tables/init/pruner references removed; checkpoint pruner no longer touches an audit log; lib.rs doc + PERSISTENCE.md §1 updated. Old store files keep the dead tables harmlessly (redb ignores uncreated tables).
- Storage: erasure coding + dedup-beyond-content-addressing unreachable from routes (45fc99167 honest gap).
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).

- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees and blocking persvati pushes — emit to a build artifact path (or commit deliberately), one-line fix.
- CLI `config init` is not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` (ignores env overrides), so `dregg config init` mutates the real home and preflight can only gate the read-only `config show` (preflight/checks/cli.rs). Honor a `DREGG_HOME`-style override in `config_path()`, then restore a hermetic preflight `cli_config_init` check (create-in-tmp + file-exists + reload round-trip).

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact).
- ECVRF per-agent sortition (targeting-resistant juries — approved future; rides identity-cell keys/pre-rotation). LANDED 2026-06-12 (`federation/src/vrf.rs`): RFC 9381 ECVRF-EDWARDS25519-SHA512-TAI from in-tree dalek primitives (no new curve) — prove/verify/proof_to_hash pinned to the Appendix B.3 test vectors, §5.4.4 non-canonical-`s` + §5.4.5 small-order-key refusals, deterministic §5.4.2.2 nonces; `sortition_select(beacon, sk, role, threshold)`/`verify_sortition` self-selection under `SortitionThreshold::from_ratio(k, pool)` (private until reveal — the targeting-resistant complement to `beacon::select_jury`, same beacon randomness); SDK surface in `sdk/src/identity.rs` (`derive_vrf_seed`/`vrf_public_key`/`key_set_with_vrf` — the VRF key is a CURRENT-key-class member of the identity cell, ECVRF keygen = RFC 8032 keygen so pre-rotation covers it with no new verb). REMAINS: compile+test gauntlet not yet run (authored in the sprint window); ticket transport serde (byte codecs only today); dalek `decompress` canonicality vs §5.5 `string_to_point` unaudited; juror-seat binding of ticket pubkey → key-set opening is documented, not yet a checked verb.
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- KERI-shaped identity event-log export (ORGANS identity rider). LANDED 2026-06-12 (`node/src/identity_export.rs`): the cell's key history as a portable KEL — chained events (each commits the prior's canonical digest), `icp`/`rot`/`ixn`/`rtd` classification from commit-log post-state snapshots, full `TurnReceipt` + executor-signature attachment, DWR1 federation witness artifacts, the pre-rotation replay tooth (`blake3(exhibited) == prior next_keys_digest` — `rotChain_pinned_by_commitments`'s deployed half), portable `verify_export` (no node), route `GET /identity/export/{cell}`, tamper/preimage/signature tests authored. REMAINS: compile+test gauntlet not yet run (authored in the sprint window); per-cell state-commitment openings against `ledger_root` (the export carries the anchors; today the snapshot↔turn binding rests on the exporting node's commit log); cooling-window check needs charter data (the stamp is checked, the window length is not).
- OCapN netlayer adapter (2–4 week artifact; ORGANS interop ladder). The enabling netlayer trait LANDED in captp (`captp/src/netlayer.rs`): `Netlayer`/`NetConnection`/`NetSession` + `ocapn://` locator module (`ocapn_uri`, with the DreggUri sturdy bridge) + two instances (`InProcessNetlayer` over a shared fabric; `RelayNetlayer` adapting the existing store-and-forward seal+queue verbatim). Remaining = the adapter itself: Syrup codec + `op:start-session` handshake + descriptor translation onto our session/gc tables + a wire Goblins speaks (tcp+tls/onion) → a Goblins peer holding a dregg sturdy ref.
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well blueprint — AUTHORED 2026-06-12 (single-action ring + net-delta program admission + the granularity-constraint tooth): `cell/src/blueprint.rs` flash-well section (quantized fee-ratchet ladder: `MemberOf` rungs × `BalanceGte` floors + `StrictMonotonic`-on-touch = the `post ≥ pre + fee` encoding over today's absolute-only balance atoms) + `sdk/src/flashwell.rs` (`FlashWell::open/borrow → FlashRing::pay/settle` riding the two-nouns `.turn()`), tests pinning the four laws both program-level and executor-path. UNVERIFIED (sprint-authored, not yet compiled/run). Remaining lane: a real `BalanceDeltaGte` atom (one evaluator arm + Lean `Exec.Program` twin) collapses the ladder into one constraint and closes the donation-cushion residue; `Dregg2.Apps.FlashWell` keystones land with it.
- Willow geometry for storage caps (3D area caveats, range reconciliation) — adopted design, not scheduled.
- Room-as-OS + delay-tolerant polis (docs/ROOM-AS-OS.md, docs/DELAY-TOLERANT-POLIS.md).

## HANDOFF READINESS (the pug bar — a stranger evaluates dregg as a finished, usable thing)

*(ember 2026-06-12: aiming to hand the system to pug to evaluate usefulness/usability
for HIS purposes. Everything here is judged by "works without ember in the loop.")*

- FRESH-CLONE BUILD: clone → documented steps → running node, no tribal knowledge. The FFI
  archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is currently
  tribal-knowledge-heavy and has bitten US twice this session — it must be one documented
  command (or build.rs does it) with a loud, teaching failure mode.
- QUICKSTART re-verified against the POST-ROTATION reality, every command actually run
  (it was verified pre-rotation; #110's closure predates the organs + rotation).
- The organs reachable as a STRANGER would reach them: SDK two-nouns + trustline/channel/
  mailbox/storage nouns each with a copy-paste example that runs against a local node;
  error messages that teach (refusals say WHY and what would be admitted).
- An evaluator's README: what dregg IS (teach-what-is register), what it guarantees
  (AssuranceCase in human terms), what it does NOT yet do (honest scope), and the three
  things to try in the first ten minutes.
- The site/playground consistent with the shipped system (no stale pre-rotation surfaces).
- One real end-to-end story pug can run start-to-finish: e.g. two agents, a trustline,
  a channel, a mailbox — money moves, messages flow, a removed member goes dark, every
  receipt checkable. The demo IS the evaluation artifact.

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter.)
- Hosted key custody posture (above).

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).

## OPUS FULL-BURN LANDING RESIDUES (2026-06-12 night — named at landing, post-seal)

*(The 13 Fable full-burn lanes were resumed as Opus finishers and ALL landed green —
7 commits f554d34d2..475f19115. These residues were named honestly at landing, per the
no-launder discipline. None block the green board.)*

- **python-lean Linux/ELF proof**: the macOS smoke proved the shared kernel works; the
  ELF (mimalloc-TLS) blocker must be confirmed on persvati — the exact command is in
  /tmp/pylean-lane2.log (cargo check -p dregg-lean-ffi && cd sdk-py && DREGG_LEAN_LINK=shared
  cargo build && python3 import dregg + assert kernel.lean). Run at round 8.
- **flash-well**: no Lean twin yet (Dregg2.Apps.FlashWell); the floor is the fee SCHEDULE
  not literal pre-balance — the named BalanceDeltaGte relative-balance atom is the closure.
- **trustline pureCredit HTTP lane**: node OpenRequest has no `collateral` field, so the
  HTTP open path is fullReserve-only; trustline_service::parse_collateral is dead
  (#[allow(dead_code)] + TODO(collateral-axis)). The Rust pureCredit semantics + SDK exist;
  wiring the request field is the remaining lane.
- **DKG ceremony slash**: complaints are witness-first attributed; the slash itself defers
  to the court→obligation-cell lane (the same node-closures item #4).
- **node-closures #3/#4 (carried)**: stale-cap c-list sweep needs a new cross-cell revoke
  verb (GC not soundness); court bond → program-toothed obligation cell (dependency on the
  flash-well obligation_factory pattern, now landed — unblocked for a future lane).
- **DKG ceremony, KERI, channel-rosters**: tests authored + type-check; full e2e runs need
  a lock-free window (round 8 on persvati exercises them).
