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

## Metatheory closures (Lean-side, mostly lane-sized)

- CrashRecovery × registries: extend the recovery model to `(writes, burns)` and lift `draw_replay_refused_across_epochs` across the crash cut (named by the persist lane; Rust half landed with `forever_digests`).
- Channels: program-readable `delegation_epoch` — an EvalContext/`Exec.Program` atom discharging the `DelegationEpochTie` premise (ChannelGroup.lean 0c57aac80; executor + Lean lockstep).
- Channels: count-equal / order-statistic constraint atom (in-program M-of-N council; slot-in point named in ChannelGroup.lean's adminGated docstring).
- Argus R1/R2: the Rust descriptor-AIR transcription gap — `Boundary` arm at `lean_descriptor_air.rs:909` so `EffectVmDescriptorAir::eval ≈ decideVm` (exact statement in the 7894e5789 apex inventory).
- Argus fee-wrapper conservation: `FeeChainStep` + `wellformed_history_conserves_modulo_burn` in `Distributed/HistoryAggregation.lean` (statement written in the apex inventory).
- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- QueueRoot/commitment: leaf/node level-tags + length binding in `blake3_binary_root` (domain separation is computational-only today; named in f0e11ea3a).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Fibration (#35): `DistConservationBound`/`DistAttenuationBound` carried hypotheses → theorems.

## Node / runtime closures

- Same-transaction burn weld: digest burn inside the turn's CommitRecord (closes the post-commit/pre-ack crash window; named in docs/PERSISTENCE.md).
- Channel room rosters durable table (`RosterStale` is availability-not-soundness today; design in PERSISTENCE.md).
- Stale-cap c-list sweep: epoch-step turn also `RevokeCapability`s superseded grants (channels 72d43dc64 residue).
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues).
- persist/ dregg1 residue retirement: tokens.rs / recovery.rs / keys.rs / audit.rs (zero external consumers; cutover-ledger discipline).
- Storage: erasure coding + dedup-beyond-content-addressing unreachable from routes (45fc99167 honest gap).
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).

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

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter.)
- Hosted key custody posture (above).

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).
