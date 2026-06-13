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
- Full-cohort descriptor regen at the ROTATED 25-slot block (the staged probe `EffectVmEmitRotation.lean` is the validated reference shape; the 26 per-effect descriptors still emit 186/14) — the §3 steps 1-2 motion of docs/ROTATION-CUTOVER.md.
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (the rotated block's first/last limbs; MMR theory landed, executor carrier missing) + lifecycle/epoch trace carriers (CellState tracks them, the trace doesn't) — ROTATION-CUTOVER.md §5 items 3-5.

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

- CrashRecovery × registries: extend the recovery model to `(writes, burns)` and lift `draw_replay_refused_across_epochs` across the crash cut (named by the persist lane; Rust half landed with `forever_digests`).
- ~~Channels: program-readable `delegation_epoch`~~ CLOSED (executor-atoms lane): `DelegationEpochEquals` atom (Rust both enums + `TransitionMeta::delegation_epoch` per-cell stamp; Lean `delegationEpochEquals` + iff/absence theorems); channel blueprint constraint 6 installs it; `DelegationEpochTie` DISCHARGED on admitted turns (`admitted_ties_delegation_epoch` + `remove_darkens_both_discharged`; premise form kept for foreign/pre-atom states). Tails: the Lean-producer/wire path has no per-cell delegation_epoch carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- ~~Channels: count-equal / order-statistic constraint atom~~ CLOSED (executor-atoms lane): `CountGe{threshold, set_commitment_slot}` — the witness RE-EXHIBITS the distinct element set each turn against the openable sorted-set commitment (the anti-affineLe-flag design); Lean `countGe` + `councilGated` keystones; `council_count_ge_shape` blueprint test + `test_program_count_ge_enforced` executor test. Tails: per-element approval binding (exhibited ≠ "approved THIS turn") — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the DEPLOYED channel program; CountGe AIR projection (witness-side scalar enforcement only; classified no-SlotCaveat-projection).
- Argus fee-wrapper conservation: `FeeChainStep` + `wellformed_history_conserves_modulo_burn` in `Distributed/HistoryAggregation.lean` (statement written in the apex inventory).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- QueueRoot/commitment: leaf/node level-tags + length binding in `blake3_binary_root` (domain separation is computational-only today; named in f0e11ea3a).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Fibration (#35): `DistConservationBound`/`DistAttenuationBound` carried hypotheses → theorems.
- Quorum unification (#170) Lean lift: raise `quorumThreshold` in `Distributed/BlsQuorumCert.lean` + `EpochReconfig.lean` to the strict supermajority `⌊2n/3⌋+1` and discharge the `StrictBft` hypothesis; lift `MembershipSafety.lean`'s `computeThreshold` `n=0 ↦ 0` guard to the fail-closed 1 (Rust unified on `dregg_blocklace::supermajority_threshold`; bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the exact `+1 at 3∣n` and n=0 relations until then).

## Node / runtime closures

- Same-transaction burn weld: digest burn inside the turn's CommitRecord (closes the post-commit/pre-ack crash window; named in docs/PERSISTENCE.md).
- Channel room rosters durable table (`RosterStale` is availability-not-soundness today; design in PERSISTENCE.md).
- Stale-cap c-list sweep: epoch-step turn also `RevokeCapability`s superseded grants (channels 72d43dc64 residue).
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues).
- persist/ dregg1 residue retirement: tokens.rs / recovery.rs / keys.rs / audit.rs (zero external consumers; cutover-ledger discipline).
- Storage: erasure coding + dedup-beyond-content-addressing unreachable from routes (45fc99167 honest gap).
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).

- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees and blocking persvati pushes — emit to a build artifact path (or commit deliberately), one-line fix.
- CLI `config init` is not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` (ignores env overrides), so `dregg config init` mutates the real home and preflight can only gate the read-only `config show` (preflight/checks/cli.rs). Honor a `DREGG_HOME`-style override in `config_path()`, then restore a hermetic preflight `cli_config_init` check (create-in-tmp + file-exists + reload round-trip).

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact).
- ECVRF per-agent sortition (targeting-resistant juries — approved future; rides identity-cell keys/pre-rotation).
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- KERI-shaped identity event-log export (1–2 week artifact; ORGANS identity rider).
- OCapN netlayer adapter (2–4 week artifact) + a netlayer trait in captp regardless (ORGANS interop ladder).
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well blueprint (single-action ring + net-delta program admission + the granularity-constraint tooth — assessed feasible 2026-06-12, trustline-blueprint-sized).
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
