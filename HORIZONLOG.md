# HORIZONLOG — the named-follow-up burn-down

*(Standing rule: when a lane/commit NAMES a follow-up, residue, or closure lane,
it gets a line HERE in the same breath — "named in a report" is not durable.
Each line: what · where it was named · the closure shape. Remove lines when
closed (git history is the record). This is a burn-down list, not a parking
lot: per WE-DO-NOT-NAME-WE-SHIP, anything that sits here across many sessions
should be either scheduled or explicitly demoted to the Research tier with a
reason.)*

Last sweep: 2026-06-13 (flagged-items burndown — removed ~14 landed/struck items,
deduped the DreggDL/sel4/snapshot landings into git history, kept live tails).

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
- balance/nonce → NAMED-register assignment (RotatedLimbs carries no separate balance/nonce limbs; the umem projection maps them to the heap domain — pick ONE canonical story; ember-visible decision, ROTATION-CUTOVER.md §2 note).
- cells_root + iroot per-turn PRODUCERS in turn/ (`turn/src/rotation_witness.rs`, NAMED in EffectVmEmitRotationV3.lean §3) + lifecycle/epoch trace carriers — ROTATION-CUTOVER.md §5 items 3-5. The staged-additive producers + trace builder + cell≡circuit differential ALREADY LANDED GREEN (51850ee91, no VK bump); these notes track the FLIP consumption. SEQUENCING: build the rest WITH the flip's rotated trace builder, not before.
- guardAtom IR kind (umem adapter c) confirmed NOT landed (absent from DescriptorIR2.lean + descriptor_ir2.rs): in-circuit policy/caveat enforcement for v2/v3 = cap-crown phase D + Policy.lean line, rides rotation.
- HEAP-KEYED CAVEATS executor runtime discharge (named premise `HeapCaveatRuntimeDischarge`; template = `verify_slot_caveat_manifest`; semantics welded via `tagHeapAtom`→`HeapAtom.lift`→`evalHeap`) — ROTATION-CUTOVER §5 item 9; at the flag-day the staged 29-felt manifest replaces the live 25-felt slot manifest in the regenerated PI region. (Wire shape STAGED; live v1 manifest untouched.)
- PI v3 rateBound/challengeWindow: carried-only (producer copies context into PI 202/203; verifier pins ZERO sentinels, proof_verify.rs:269-270). Enforcement arrives with optimistic-proving/dispute (#169) which owns these slots — nothing further pre-#169.

## THE ROTATION FLIP — the irreversible tail (ember-COMMISSIONED, a4c7368ae; touches cell/+live registry+executor PI)

*(The genuinely-new long pole — staged producers + rotated trace builder + cell≡circuit
differential — is DONE and GREEN beside v1, no VK bump. What remains is the deliberate flip:)*

- regen EmitAllJson so `v3Registry`→THE live registry (fingerprints bump) · cell
  `CANONICAL_COMMITMENT_CONTEXT` v8→v9 (rotated absorption order) · executor PI assembly reads
  `pi::v3` as LIVE · VK/commitment bump + succession drill · v1 path deletion (DORMANT today).
  ROTATION-CUTOVER §3 steps 2-6 / §4 pins. Off-limits this run (cell/+registry+executor+persvati
  gauntlet) — the main loop's separate deliberate act at the VK epoch.

## Metatheory closures (Lean-side, lane-sized — tails of landed work)

- Argus joint-AIR fold (Silver→Gold layer: per-leg descriptors folded; not an Argus/ statement).
- Coeffect dst-liveness (named in the 4dd84a3ae audit; outside the four apex modules).
- BiorthRelational: threshold-D iff at Shamir t-of-n (proved at 2-of-2 additive); n-ary trace statement (reduced to the adjacent-step atom).
- Trustline: `settled`-era pureCredit — Lean has both collateral points; the Rust pureCredit realization (issuer-well draws) is open (7da845758 divergence 1-as-Rust).
- Quorum unification (#170) consumer migration: `BlsQuorumCert.lean`/`EpochReconfig.lean` still transcribe the historical `n−⌊n/3⌋` + carry `StrictBft`; `MembershipSafety.lean` still has the `n=0↦0` guard. The unified `supermajorityThreshold` Lean twin LANDED (QuorumThreshold.lean) — migrate the consumers onto it (bls_quorum_diff.rs/epoch_diff.rs/membership_safety_differential.rs pin the relations until migration).
- Channels delegation_epoch wire carrier: the Lean-producer/wire path has no per-cell `delegation_epoch` carrier yet (a `DelegationEpochEquals` program evaluated there fails closed — wire lockstep before channels ride the producer); pre-atom channel cells keep the old program (no live-cell program-upgrade verb).
- Channels CountGe tails: per-element approval binding (exhibited ≠ "approved THIS turn" — the actor-bound approval-slot ceremony must write the quorum commitment slot before `councilGated` replaces `senderIs admin` in the deployed program); CountGe AIR projection (witness-side scalar only).

## Node / runtime closures

- Stale-cap c-list sweep (channels 72d43dc64 residue): epoch-step turn should `RevokeCapability` superseded grants. STILL OPEN — a real verb gap, NOT a quick fix: `member_cap_grants` installs into each MEMBER's c-list, while `RevokeCapability {cell,slot}` removes from a cell's OWN c-list; sweeping a departed member needs cross-cell `Delegate` authority the operator doesn't hold. `RevokeDelegation` epoch bump already DARKENS prior-epoch group caps at admission (R7 `CapabilityStale`) → this is c-list GC (storage), not soundness. Honest closure = a new verb shape (member-initiated self-revoke or group-scoped revoke authority). → node/turn, post-flip.
- Adjudication: bond cell → program-toothed obligation cell; tau-exclusion via a membership cell (court is the value leg only; 460d4d6bd residues). STILL OPEN — bond is a plain operator cell, not yet deployed via the obligation factory; deferred to AFTER the FLASH-WELL/blueprint `obligation_factory_descriptor` lands+verifies, then `post_bond` deploys via the factory in one slice. (That pattern now landed — unblocked for a future lane.)
- Storage: erasure coding + dedup-beyond-content-addressing — IN-CRATE half closed (storage/src/availability.rs, 10 tests). REMAINS: the node put/get HTTP route (gated by storage-gateway-mandate cell) can now CALL the in-crate availability route — the "weld to the shell" half. → node, post-flip.
- Trustline payment-channel parity: channel close (TL_STATE_CLOSED residual-escrow return) · one-factory collateral parameter · MCP `dregg_extend_trustline` · remote-silo pubkey registration (n=1 collapses it) · multilateral rippling (TRUSTLINES.md §7).
- Trustline pureCredit HTTP lane: node OpenRequest has no `collateral` field → HTTP open is fullReserve-only; `trustline_service::parse_collateral` is dead (`#[allow(dead_code)]`+TODO(collateral-axis)). Rust semantics+SDK exist; wiring the request field is the lane. → turn/node.
- Hosted-operator epoch-key custody posture (sovereign-member groups ride the SDK noun client-side; channels residue — partly an ember-decision).
- Divergence-ledger doc churn: `turn/tests/rust_lean_divergence_finder.rs:684` overwrites the git-tracked `metatheory/docs/rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md` on every run, dirtying trees + blocking persvati pushes — emit to a build-artifact path (or commit deliberately). One-line fix. → turn/ (off-limits this run; STILL LIVE, tree dirty at HEAD).
- CLI `config init` not path-injectable: `cli/src/config.rs::config_path()` hardcodes `~/.dregg` → `dregg config init` mutates real home, preflight can only gate read-only `config show`. Honor `DREGG_HOME`-style override, then restore a hermetic preflight `cli_config_init` check. → cli/.
- node recovery overlay first-writer-wins bug (surfaced by the snapshot lane): `node/src/state.rs` recovery uses `insert_cell` (strict insert), so a post-checkpoint write to a cell the checkpoint ALREADY holds is silently dropped; the convergence root-mismatch only LOGS, does not fail closed. Fix = `upsert_cell` (the verified `CrashRecovery.upd` point-update needs remove-then-insert). → node/persist, post-flip.
- persist snapshot wire half: in-crate `ship_snapshot`/`apply_snapshot`/`apply_snapshot_verified`/`install_snapshot` LANDED green (persist/src/snapshot.rs, 7 tests, shape = CrashRecovery.lean). REMAINS: node-side `GET /snapshot/{from}` serve + joiner consume route so a fresh node bootstraps over the network. → node, post-flip.
- checkpoint-prune → commit-log compaction (§2.1): `prune_before` trims attested roots but commit-log records below a finalized checkpoint are never compacted (unbounded WAL). Add `CommitLog::compact_below(height)` preserving the index-audit invariant. → persist.

## Product surfaces (post-rotation)

- dregg-query: attested-queries feature only (Q2 of docs/EPISTEMIC-DATALOG.md) — NOT the full Datalog engine.
- Flash-well: `BalanceDeltaGte` relative-balance atom (one evaluator arm + Lean `Exec.Program` twin) collapses the fee-ratchet ladder into one constraint + closes the donation-cushion residue; `Dregg2.Apps.FlashWell` keystones land with it. The blueprint + SDK are AUTHORED (cell/src/blueprint.rs flash-well, sdk/src/flashwell.rs) but sprint-UNVERIFIED.
- Willow geometry for storage caps (3D area caveats, range reconciliation) — adopted design, not scheduled.
- range-based set reconciliation (§1.5/§3.2d, Willow shape): the shared primitive behind scalable anti-entropy (O(diff·log) not O(state)) AND storage partial-sync; cap chains as the pluggable authorization. Adopt the geometry, keep our proofs.
- eclipse hardening at scale (§1.1): peer_score buckets by SocketAddr today; add /24·/48 prefix + AS-diversity bucketing so a single cloud /24 cannot fill the eager set.
- availability route follow-ons (§3.1): swap XOR-prototype erasure (erasure.rs:11) for real Reed–Solomon; real Merkle-path chunk proof vs manifest.root (erasure.rs:226 is integrity-only).
- proving-modality dial #169 (§4.1): make prove-on-demand vs checkpoint vs eager a CONFIGURED axis, not hardcoded policy; settlement/pipelining depth (§4.2) parameterized by topology (n=1 = immediate settlement). Owns the PI 202/203 slots.
- Room-as-OS + delay-tolerant polis (docs/ROOM-AS-OS.md, docs/DELAY-TOLERANT-POLIS.md).

### SDK polyglot crypto/binding closures

- **sdk-ts organ-noun crypto closures** (named 2026-06-13; sdk-ts now mirrors two-nouns + organ-noun as thin typed clients, green): three crypto ops stay node/wasm-side (pure TS has no Poseidon2/X25519/STARK): (a) `mailbox-verify-dequeue-proof-in-ts` (re-run storage queue Merkle verify over a drained batch); (b) `channel-seal-open-in-ts` (X25519→HKDF→ChaCha20-Poly1305 epoch-key seal/open so a TS member decrypts the fan-out — example uses placeholder ciphertext today); (c) `attested-verify-in-ts` (`verify_full_turn` STARK + federation threshold-sig check so `AttestedQuery` returns a CHECKED verdict — the light-client crown, likely waits on a wasm `verify_full_turn` export). (a)+(b) are the first users of `@dregg/sdk/wasm`.
- **userspace-verify TS/Py binding** (named 2026-06-13; `dregg-userspace-verify/` landed green, 22 tests): expose `analyze()` to TS/Py so `sdk-ts`/`sdk-py` call it pre-submission. (a) cheap path: SDK serializes its forest to JSON, shells/WASM-calls `dregg-uverify --json`; (b) integrated: a `#[no_mangle]` FFI `uverify_analyze(json_ptr,len)->json` in a small cdylib, bound from TS (napi/wasm) and Py (ctypes/pyo3 — the bridge already links libdregg). `Assurance`/`Finding`/`Locus` are Serialize+Deserialize → wire shape settled; the lane is the glue + an SDK `analyze()` sugar at `.sign()`-time.
- **DreggDL node `POST /deploy` ingress** (follow-up to the landed `dregg-deploy` + its TS/Py bindings, a7734efcc/a49448d09): a node endpoint accepting a DreggDL doc → `dregg-deploy::check` (refuse non-conserving/amplifying up front) → lower + submit per-root turns → return receipt chain + resolved factory_vks/cell-ids. Static check = pre-submission gate; executor stays the trust boundary. `dregg-deploy apply` = the same flow SDK-side. → node, post-flip.
- **sdk-py self-contained wheel**: (carried — packaging the Py binding as a standalone wheel that bundles libdregg). → sdk-py.

## APPS-POLISH lane (starbridge-apps demo-worthiness)

- **compute-exchange/ + gallery/ stub dirs** carry only a `manifest.json` (no crate) — decide: build them or delete the stubs.
- **escrow-market follow-ups** (escrow-market, 12 tests green): (a) the no-burn equality is settle-scoped in `child_program_vk` but NOT in the executor-installed flat `state_constraints` (executor installs `Predicate(state_constraints)`, evaluated unconditionally — apply.rs); to enforce exact conservation on the settle turn, either teach factory-birth install to use the cell's `Cases` program (`child_program_vk`) OR add a settle-gated relational atom. Until then no-burn rests on `build_settle_action` emitting a balanced split. (b) real ledger-balance binding — ESCROWED/RELEASED/REFUNDED are slot integers, not moved balance; wire settle to a real value transfer (trustline/flashwell `.turn()`) for the organ-true version. → starbridge-apps/turn, post-flip.
- **userspace-verify integration point** (depends on the landed toolkit): escrow's `released+refunded==escrowed` conservation predicate is the first app-level customer for the static checks — lift it to a published checker. Same shape for agent-provenance `verify_chain` + bounty-board lifecycle monotonicity.
- **polis factory-birth co-location**: polis's executor-path teeth live in `sdk/tests/polis_*_e2e.rs`, not a `polis/tests/factory_birth.rs` like the other apps — co-locating a birth test makes it self-contained.
- **privacy-voting ballot unlinkability** (named in its README): the app gives one-vote-per-ballot + monotone tamper-evident tallies, NOT ballot/voter unlinkability (no mixnet/nullifier-set). True secrecy is a separate, stronger lane.

## HANDOFF READINESS (the pug bar — a stranger evaluates dregg as a finished, usable thing)

*(ember 2026-06-12: hand the system to pug to evaluate usefulness/usability for HIS purposes.
Everything here is judged by "works without ember in the loop.")*

- FRESH-CLONE BUILD: clone → documented steps → running node, no tribal knowledge. The FFI archive seeding (elan on PATH, lake build, seed-dregg2-closure.sh) is tribal-knowledge-heavy + bit US twice this session — it must be ONE documented command (or build.rs does it) with a loud, teaching failure mode.
- QUICKSTART re-verified against POST-ROTATION reality, every command actually run (it was verified pre-rotation; #110's closure predates the organs + rotation).
- The organs reachable as a STRANGER would: SDK two-nouns + trustline/channel/mailbox/storage nouns each with a copy-paste example that runs against a local node; error messages that teach.
- An evaluator's README: what dregg IS, what it guarantees (AssuranceCase in human terms), what it does NOT yet do (honest scope), the three things to try in the first ten minutes.
- The site/playground consistent with the shipped system (no stale pre-rotation surfaces).
- One real end-to-end story pug can run start-to-finish (two agents · trustline · channel · mailbox — money moves, messages flow, a removed member goes dark, every receipt checkable). The demo IS the evaluation artifact.

## Crypto / protocol artifacts (bounded, sequenced after the rotation)

- DKG ceremony-as-cell-app: rounds over blocklace broadcast + seal-pair channels + slashable complaints (core landed 29509149d; transport is the artifact). Slash itself defers to the court→obligation-cell lane (node-closures adjudication item).
- ECVRF per-agent sortition: LANDED (federation/src/vrf.rs — RFC 9381, sortition_select/verify_sortition, SDK surface in sdk/src/identity.rs). REMAINS: full compile+test gauntlet (authored in-sprint); ticket transport serde (byte codecs only); dalek `decompress` canonicality vs §5.5 unaudited; juror-seat binding of ticket pubkey → key-set opening is documented, not yet a checked verb.
- KERI identity event-log export: LANDED (node/src/identity_export.rs — portable KEL, route GET /identity/export/{cell}). REMAINS: full compile+test gauntlet; per-cell state-commitment openings against `ledger_root` (today the snapshot↔turn binding rests on the exporting node's commit log); cooling-window length check needs charter data.
- Proactive resharing anchored in epoch-transition certs; proactive-deletion requirements (dkg.rs NOTES).
- drand-style beacon chaining (only once heights can fork; one line in beacon_message).
- OCapN netlayer adapter (2–4 week artifact): the enabling `Netlayer`/`ocapn://` trait LANDED in captp (captp/src/netlayer.rs). REMAINS the adapter: Syrup codec + `op:start-session` handshake + descriptor translation onto our session/gc tables + a wire Goblins speaks → a Goblins peer holding a dregg sturdy ref.
- MLS/TreeKEM fan-out swap for channels (replaces only `seal_epoch_key_to_roster`; cell interface unchanged).
- VRF-grade public beacon (its own later effort; ORGANS §6).

## PRIVACY/OFFLINE-CELL lane

- **Rust private-participant turn role** (design + Lean model landed: docs/PRIVATE-OFFLINE-CELLS.md + Dregg2/Distributed/PrivateLeg.lean, keystone joint_turn_sound_with_private_legs, #assert_axioms-clean). To SHIP: a private-participant leg type in `coord/src/atomic.rs` — an AtomicForest participant whose contribution is (commitPre, commitPost, proof) not an applied action, with a commit-path verify-gate implementing MixedAdmissible (every private leg's STARK verifies + binds the shared jid); the AIR the `CarrierEncodesPrivLeg` hypothesis names (recKExecAsset + recStateCommit state-root opening, producible offline); state-root continuity across turns (commitPost[i]=commitPre[i+1], mirroring HistoryAggregation.ChainBound). Liveness out of scope (a dark private participant aborts the all-or-none turn). Crypto floor = STARK extractability (no new assumption). → coord/turn, post-flip.

## seL4 / DreggDL lane (design+scoping landed)

*(Scoping docs: docs/SEL4-EMBEDDING.md (bootable-image roadmap; THE blocker = libuv-free/IO-free
Lean leanrt+GMP on musl/seL4) + docs/CAPDL-POLYGLOT-DX.md (DreggDL = describe the cap graph once,
3 SDKs instantiate it). The dregg-deploy parser crate + TS/Py bindings + sel4 verifier-PD scaffold
ALL LANDED (a7734efcc / a49448d09 / 152e6b3a5). Remaining lanes:)*

- **sel4 cross-build tail** (verifier-PD scaffolded, `no-lean-link` PROVEN Lean-free at HEAD): the actual cross-build to `aarch64-sel4-microkit` (needs Microkit SDK + rust-sel4 toolchain, absent here) + `getrandom`-custom / `p3-maybe-rayon` serial-fallback for the bare target. → sel4/.
- **Lean runtime bottom-half port (THE blocker, weeks–quarter)**: IO-free, libuv-free `leanrt`+GMP so `libdregg_lean.a` links on musl/seL4. Blocks the **executor PD only** — the verifier PD is UNBLOCKED (`no-lean-link` proves it links Lean-free). Until the port, `no-lean-link` builds the node marshal-only (shadow-off) — bring-up scaffold ONLY, never the authoritative ship.
- **First rbg→seL4 port: `DirectoryFactory` → `seL4_Untyped_Retype`** (sel4/RBG-TO-SEL4.md): the smallest real port turning an rbg idea into a kernel-enforced mechanism (factory's slot-caveat becomes the Untyped retype template). Additive, NOT gated on the Lean-runtime blocker; belongs in a `sel4/factory-pd/` sibling once rust-sel4 is wired.

## STARBRIDGE-V2 (native gpui shell — embedded verified executor)

*(The master interface EMBEDS the real verified executor + runs a live local dregg world natively
— headless heart gpui-free + `cargo test`-able, 16 tests green; the window OPENS via gpui
`runtime_shaders`. Build-out lanes from docs/STARBRIDGE-V2.md coverage matrix:)*

- **organ panels** (trustline/channel/mailbox/court — types catalogued) + whole-graph ocap layout (per-cell edges live) + intents/factories/obligations/nullifiers panels.
- **proof-attach + STARK verification-status view**; native federation/remote-node panel (NodeClient::Http exists; reqwest gated to sel4-thin for now); seal/unseal/destroy/burn/factory-birth verbs (reachable via World::turn — UI affordance); multi-action call-forest composer.
- **live node connection** — move reads to gpui's async executor; wire `/api/events/stream` SSE into ReceiptInspector with `cx.notify()` (snapshot today).
- **seL4 framebuffer backend** — a gpui renderer targeting a framebuffer cap (SEL4-EMBEDDING end state) + **seL4 channel transport** (a `NodeClient::Channel` over an seL4 endpoint, same contract over IPC not TCP).
- **single-source wire types** — replace `starbridge-v2/src/model/` hand-mirrors with a shared `dregg-wire-types` crate depended on by both node + shell.
- **finish-the-window (HOST gap, not a crate defect)**: the runtime-shader path opens the window; the offline Metal Toolchain download is blocked by a damaged Xcode `DVTDownloads.framework`. The remaining ahead-of-time-shader option = provision the Metal Toolchain on a healthy Xcode.

## DREGG-ANALYZER (forensic/observability trace analysis)

*(New crate dregg-analyzer/ — ingests CAPTURED TRACES, ATTESTS via the REAL verifiers, 14 tests.
Build-out lanes:)*

- **live-capture hooks** — a node trace-export mode emitting `BlocklaceCapture`/`ReceiptStrandCapture`/`WalCapture` from the running node (the on-disk/wire types are already exact, so an export endpoint is a thin dump). → node.
- **Studio/Workbench visualization binding** — render the `AnalysisReport` (DAG w/ equivocation fork, finality bar, receipt link graph, WAL replay overlay) in the Starbridge/starbridge-v2 shell (report is already JSON-serializable).
- **gossip capture provenance** — the network source is `Observed`-only (gossip = liveness); a signed dissemination-receipt would graduate some eclipse signals to `Verified`.

## Decisions pending (ember)

- #93 proof-audit: build a harness, or declare `#assert_axioms` + non-vacuity-both-polarities + the Convergence gauntlet its successor and close. (Recommendation: the latter — WRITTEN UP as docs/ASSURANCE.md §4 with the close-rationale; awaiting ember's flip to close.)
- Hosted key custody posture (above).
- starbridge-apps stub dirs compute-exchange/gallery: build or delete (above).

## Research tier (explicitly not scheduled)

- Transcendental-syntax S3 (substructural recovery from the dregg side) + S5 (stella instantiation).
- UC-security / CryptHOL (#31) + research pillars (revocation/info-flow/metadata).
- Hypersystem/simplicial joint turns (dregg4 vision).
