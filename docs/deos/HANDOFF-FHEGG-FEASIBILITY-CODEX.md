# HANDOFF — fhEgg / Dark Bazaar current implementation ledger

*Current at HEAD on 2026-07-22. This is the durable implementation handoff, not a
roadmap. Verify every claim against the named source, theorem, test, and captured
gate result before repeating it.*

## 0. Status language

- **GATED** — the named artifact exists and the named gate passed after the
  relevant implementation landed.
- **BUILT, UNGATED** — the implementation exists, but no successful run of the
  relevant current target has been captured.
- **PENDING GATE** — the HEAD source and exact target exist, but no result has
  yet been supplied for this implementation revision. This says nothing about
  whether the target compiles or passes.
- **MIXED** — a target or composed lane has both captured greens and a captured
  red/pending member; only the individually named results carry authority.
- **PARTIALLY GATED** — every named result is green, but at least one composed
  member remains pending or the evidence is split across focused invocations.
- **OPERATIONAL** — the execution substrate is available for the named work.
  Hardware discovery alone is not a code verdict; only attached gates count.
- **OPEN** — the construction, proof, or production boundary does not exist yet.

Do not turn an earlier, compiled-out, or predecessor test into a current green
claim. A Lean theorem proves the model stated in that module; it does not silently
prove the Rust codec, cryptography, transport, or refinement hidden behind an
explicit backend premise.

## 0.8. July 22 live-finality and shielded-v4 checkpoint

This section supersedes sections 0.5–0.7 and section 14 wherever they describe
exact FNSP-v3 as having no production caller, the hosted Bazaar as having no
worker, the exact accumulator as requiring an online full-prefix scan, or
consensus time as unauthenticated. It records banked commits through
`54407562c`. Current dirty-tree ACK, private-spool, promise-resolution,
Descent-census, and BFV-terminal work is deliberately excluded until each lane
banks its own coherent checkpoint.

### What is in the live exact-v3 finalization path

- `c0aed47d2` places exact FNSP-v3 in the production blocklace finalizer. The
  strict SignedTurn is validated first; the exact-v3 route is classified before
  the legacy v2/generic charge path; the proof is verified and reexecuted
  off-lock; the lock is reacquired; actor, cursor, signer, history, and state
  coordinates are revalidated; and only a fresh durable result publishes the
  ledger, receipt, artifacts, and observer events. Legacy faithful-only
  NoteSpend growth is refused after exact activation.
- `d52c2e9ea` makes the first activation and every exact successor a single
  redb transaction over activation, faithful/exact/frame state, receipt,
  attested root, commit record, and the complete executor consensus-state
  snapshot. Pending-promise resolution is applied to the retained post-executor
  before the successor snapshot. `f60a1919b` fixes nonempty-prefix activation:
  the first frame sequence is the activation exact generation, rather than a
  hard-coded zero.
- `8a052f3af` replaces online full exact-prefix reconstruction with sparse
  authenticated nodes, ordered leaf/position indices, and head history: lookup
  is logarithmic in the predecessor/path and fresh mutation is proportional to
  tree depth. Boot still reconstructs from canonical durable records. The
  analogous receipt-predecessor boundary is maintained incrementally by
  `aeab921eb` and authenticated across the active suffix by `4e932492a`.
- The live exact path is still explicitly **solo-only**. Its v3 frame identity
  binds the local executor key, so committee validators would derive different
  frame chains. It is also not the private-value apex: its public statement
  exposes value, asset, nullifier, and exact coordinates, and the characterized
  execution slice admits the value-zero form. These are protocol boundaries,
  not documentation caveats to erase.
- A current whole focused exact-v3 gate has not completed cleanly against the
  concurrent node redesign. The production call graph and narrow component
  gates are real; do not promote them to a current full-suite green.

### The actual shielded and federation successor

- `d3560fa1e` defines the strict 100-lane ShieldedExactApexV4 ABI. Clear
  value/asset are absent. The statement binds a full-width nullifier, sixteen
  u16 lanes each for value and asset, the consumed input, market consequence,
  output-note root, and exact before/after endpoints under distinct `FNI4`,
  `FNS4`, `FXC4`, and `FXA4` domains. Its compatibility token is explicitly not
  same-opening authority.
- `bce9d2b63`, registered by `f29768fd5`, supplies the Lean relation over one
  hidden `NoteOpening`: full nullifier derivation, wide value/asset binding,
  selected consumption, fixed market rule, per-asset conservation, exact
  output notes/root, and one-step exact append. Collision reductions and the
  still-uninhabited pinned-verifier knowledge-soundness contract are explicit.
  The registered tree passed the full local `lake build Dregg2` gate.
- `0ea02a76a` makes v4 consensus identity signer-independent. Canonical
  `EXA4`/`EXR4`/`EXF4` cores determine activation, deterministic receipt, and
  frame identity; the separate `EXE4` local envelope requires both Ed25519 and
  ML-DSA-65 and is checked against an independently expected validator
  identity. Receipt identity excludes local timestamp and signature bytes.
- V4 is not live yet. It has no emitted/pinned shared-witness verifier and VK,
  no persistent v4 activation/frame/state writer, no node selector, no atomic
  output-note installation, and no committee finality/threshold certificate
  over the fixed core. The ABI, Lean relation, and consensus-core substrate are
  the right pieces, not a deployed shielded market.

### Consensus time and durable finalization outcomes

- `1df9bb868` adds a strict fixed-record consensus-time claim and a versioned
  timed-turn payload. Canonical block payload bytes bind time and artifacts, so
  both Ed25519 and ML-DSA signatures and the BlockId authenticate the same
  claim. Admission enforces immutable genesis, monotone predecessor time, a
  protocol upper bound, strict legacy refusal after enablement, and no local
  wall-clock decision in the blocklace relation.
- `54407562c` replaces the repeated ancestor walk with an authenticated derived
  frontier proportional to immediate predecessor count, requires an empty lace
  at greenfield enablement, and routes generic local creation through the same
  fallible validation boundary. `dregg-blocklace` checks green at this cut.
- The node still must carry the authenticated time into a typed
  `FinalizedExecutionContextV1`; receipt validity, expiry, capability refresh,
  and rate windows must consume that context rather than `SystemTime::now`.
  Separately, the poller must advance the executed-block cursor only for a
  durably terminal `Committed` or `DeterministicallyRejected` outcome. A
  `RetryableOperational` failure must stop the prefix without consuming the
  block, and `FatalIntegrity` must stop rather than launder corruption into a
  rejection. `3b2cbef99` is the banked contract; the live typed-ACK repair is
  active working-tree work, not yet a banked guarantee.

### Hosted private Bazaar and game consequence

- `d13b2e0de` adds the production worker abstraction. A bounded
  `FinalizedPrivateBazaarReceiptSource` feeds a durable worker whose authority
  phases are `Prepared` → `Dispatching` → `Applied` → `Committed`. The worker
  persists claim/outbox/cursor state, recovers a crash after target dispatch
  from the immutable target receipt, avoids duplicate Dungeon XP, and publishes
  only a viewer-blind journey. Private blind/input, winner, and raw receipt stay
  in worker custody. The focused worker gate was green.
- This commit does not provide a concrete node/queue/network source or an
  auto-spawned supervisor. A strict append-only 0600/fsync spool and deployment
  runner are active in the dirty tree and their transport units are 4/4, but
  they are not implementation authority until banked. Full host restart also
  needs deterministic restoration of the exact settlement receipt (or a
  semantic reissue protocol anchored to the claim/cursor); weakening fork
  refusal is not an acceptable substitute.

### Durable executor side-state and GPU/FHE boundary

- `9af0f439b`, `4fd4ad745`, `174f9a46c`, and `96288b41b` persist and restore
  reactive registry/nullifiers, the complete finalized executor state, and
  per-cell receipt provenance across compaction. `fc8704c86` makes the separate
  React replay domain explicit in Lean. The old post-commit resolution journal
  has been replaced: `a0199c1e0` atomically writes the canonical typed outbox
  with its source commit, `397ccb234` bounds hostile rows/batches before decode,
  `74e0e61d2` exposes resumable HTTP/WebSocket cursors, and
  `b8ba574c4`/`a58038562` attach and Fresh-only publish it from exact and generic
  finalization. The second `NodeState` pending-registry owner is deleted.
- `51030b01b` binds the real q0 N=8/N=4096 BFV forward/inverse table carrier and
  threshold-decrypt terminal relation to transform boundaries. **Do not treat
  `92c881a0a` as proof authority.** It emits and verifies a real N=4096 composite
  HidingFRI artifact for a Lean-authored q0/±2^80 terminal descriptor, but the
  relation does not yet link the hidden product to the carrier coefficient,
  prove the carrier butterfly arithmetic, or pin the required carrier geometry.
  A trivial product/smudge assignment can therefore satisfy the terminal rows.
  The timing (about 72ms prove, 54ms verify, 285.5KB) measures an **unsound
  prototype** only. Repair must bind the full transform/LogUp carrier and
  terminal arithmetic before expanding it to all RNS limbs or DKG authority.
- The measured strict Descent/Bazaar custody proof remains CPU-bound: the
  latest captured release run was about 514.6 seconds on persvati, down from
  1086.0 seconds but still far from an interactive game loop. Portable WGPU
  BFV/TFHE kernels are real; the live `fhe_clear`, Dark AMM multiplication, and
  classical Bulletproof/Ristretto custody path are not thereby GPU-resident or
  post-quantum.

### 0.8.1. Subsequent banked closures through `f23393aed`

- `386b3a1b5` and `a58038562` close the turn-finalization ACK cut described
  above. Only a durable commit or authenticated durable rejection advances the
  identity cursor; retry stops without consumption; fatal persists the earlier
  terminal prefix and terminates the task. Timed-turn restart rows are checked
  as turn authority rather than trusted as inert served IDs. The latter commit
  also joins generic executor consensus state, React state, and promise outbox
  to the same finalized writer. Prover-feature node library checks passed on
  both hbox and persvati. Membership/checkpoint durability is still separate.
- `29a2528a1` and `05ea68be2` are the registered Lean causal-time and durable
  outcome-prefix laws. Commit/reject are terminal; retry/fatal do not install or
  ACK; the recovered cursor is derived from the durable ordered terminal prefix
  and stops at the first hole.
- `74e0e61d2`/`d47e2df4c` install and enforce the rolling faithful↔exact
  induction boundary. `cbdccedd6`/`cc3c74e56` add the non-Clone authenticated
  historical-root token and stale/tamper falsifiers. `0625c82f4` consumes that
  token through exact commit, and `a58038562` deletes the remaining duplicate
  per-active-exact full-history load. Full replay remains intentionally at open
  and first activation; the steady-state path is O(1) in history length.
- `a0199c1e0`/`397ccb234` persist a bounded typed PromiseResolution batch and
  manifest atomically with the source turn. `74e0e61d2` exposes cursor-based
  HTTP/WS observation; `b8ba574c4`/`a58038562` attach and publish exact/generic
  batches only after Fresh durable success. Ready-to-execute observation never
  carries or auto-submits a Turn; the private dependent-turn scheduler is a
  separate active feature.
- The concrete Bazaar file spool was accidentally co-banked with the ACK files
  in `386b3a1b5`; this mixed provenance is preserved rather than rewritten.
  `1c0799467` adds O_NOFOLLOW, pinned file identity, dev/inode checks,
  regular/nlink/owner/mode enforcement, an exclusive writer lock, and hostile
  symlink/hardlink/replacement tests. Focused spool tests are 6/6. Restart-stable
  semantic clearing identity and an auto-spawned production source remain.
- `fdb63254a` makes Descent's eight relic objects authoritative over its
  counters. Six Lean-authored exact-census teeth cover every verb; Lean/Rust
  mutation canaries reopen the attacks when those teeth are deleted; generated
  JSON drift passes; the real executor integration is 17/17. The current tooth
  is fixed-eight executor admission, not yet a heap-aggregate AIR/custom-VK.
- `d3b895d84` is the Lean-authored fixed-100-PI ShieldedExactApexV4 descriptor
  over one shared opening. `e7aeec218` composes shared-witness acceptance,
  FNS4/output notes, activation/frame, causal time, signer-independent receipt,
  and terminal ACK, with failure nonmutation and local envelope/clock
  noninterference. The descriptor is Lean-green; emitted bytes and the real
  HidingFRI producer/verifier are still being gated.
- `b28e9a181` must not be consumed as the finalized receipt identity in its
  original form: review found a validator-local execution ordinal and an
  unproved legacy-hash-to-core-id reinterpretation. `f23393aed` is the repaired
  substrate. Its context contains only signed BlockId, deterministic DAG round,
  and authenticated time. Its predecessor is explicitly `Genesis`,
  `LegacyCutover`, or `Core`, and the new core ID and legacy receipt index/hash
  remain separate during dual-chain cutover. The strict no-default-feature turn
  check and focused 5/5 pass; live persistence/consumer migration remains.

### 0.8.2. Subsequent banked closures through `a283c3423`

- `d7ea8b9c5` emits the domain-separated ShieldedExactApexV4 descriptor as the
  registered JSON artifact. This closes the Lean-to-descriptor emission step,
  not the live v4 selector/persistence/output-note/committee-authority cut.
- `6ed2ca903` makes the unsound q0 terminal composite fail closed in code: the
  public producer and verifier cannot mint authority while product/carrier
  linkage is absent. `8ba2b7ae1` repairs the quarantine test's compile path.
  The internal arithmetic prototype remains useful for repair work, but its
  proof and timing are not release authority.
- `6ed2ca903` also banks the first FRC1 persistence substrate;
  `8c9e30016` pins restart reauthentication to the exact activation executor
  rather than accepting an attacker-selected self-signed row. FRC1 now shares
  the atomic finalized transaction and has byte-exact replay/restart teeth; the
  focused set is 5/5. Public query and production consumer migration are still
  active and must not be reported as complete.
- `1d5d27818` replaces the private Bazaar's restart-unstable envelope identity
  with a fixed-width v2 spool and a restart-stable semantic settlement core.
  A fresh proof/local receipt envelope may revise the same logical cursor
  append-only, while semantic forks, cross-deployment replay, corrupt cores,
  and stale pre-restart envelopes fail closed after live-market revalidation.
- `7e2030739` adds a bounded bearer-gated private dependent-turn scheduler.
  Ready turns remain XChaCha-sealed in custody; the public API exposes only
  arm/status/cancel; a destructive pre-submit claim feeds ordinary validated
  blocklace ingress and restart scan. The prover-feature node library check is
  green. A crash-uncertain `Claimed` item is reconciled through finalized lookup
  and never blindly resent, so at-most-once currently may sacrifice liveness
  until ingress reservation/idempotency is complete.
- `2593ebfaa` binds `VerifiedDkgTranscript` to a domain-separated digest of the
  exact serialized collective BFV public key and includes it in the v2 setup
  transcript digest. `fd86eb091` preserves serial Fiat-Shamir derivation but
  evaluates the public decrypt relation with one dalek Pippenger MSM instead of
  tens of thousands of individual scalar multiplications; its complete legacy
  equation-fold differential and the earlier parallel-order canaries are
  green. `a283c3423` adds a dependency-isolated heavy proof tooth. On hbox in
  release it completed verified 2-of-3 DKG, two concurrent full ZK decrypt-share
  proofs, verification, plaintext combine, and forged-response refusal in
  201.983 seconds. This is a baseline for that exact two-custodian crypto tooth,
  not an apples-to-apples replacement for the older three-custodian persvati
  game measurement.

## 0.5. July 22 superseding checkpoint

This section supersedes older residual sentences below where they disagree. It
records banked artifacts, not active working-tree intention.

- `bb95eec3f` proves the full ordered chosen-input-VOLE cross-term identity in
  Lean, party-local endpoint mask cancellation, and direct composition into the
  authenticated-bit batch check. Omitted-cross-term and diagonal-only
  constructions are executable counterexamples. Privacy, malicious/PQ VOLE,
  selective-failure resistance, routing, and robustness remain adapter
  obligations.
- `3118f74a4` adds strict typed `FHTRI005` composition: real threshold-BFV DKG
  and relinearization, exactly 129 private candidates per kept gate,
  party-local candidate custody and public commitments, distributed MAC
  manifest/key custody, and joint beacon. The real 129-row gate required the
  new exact degree-8192 correlation profile; the former degree-4096 profile
  refuses. The state machine deliberately ends at `AwaitingCrossTermProvider`.
  It contains no production ideal-OT path and is not yet the live triple source.
- `37332746f` makes certified `FHTRI004` rows durably one-shot. Public party
  runners and raw transport constructors synchronously refuse certified
  material; a private, non-forgeable authorization exists only while a pinned,
  descriptor-relative ledger reservation is held. The hostile ledger suite is
  14/14 green across process/thread races, abrupt exit, restart, torn append,
  ownership/mode, symlink/FIFO/hardlink/replacement, and stable-correlation
  recertification attacks. The old direct market-apex caller now correctly
  refuses and must be welded to the durable transport constructor.
- `45afb75e5` is the first Dregg-owned collaborative tensor-code foundation:
  tensor-axis encoding commutes, encode/fold commutes, fewer than `t` observed
  Shamir rows support every secret vector, and `t` rows pin it. This is an
  information-theoretic support theorem, not distributional ZK or malicious
  collaborative-PCS soundness.
- `1f532e7c9`/`b106efd1a` add a Dregg-owned generalized-bilinear accumulation
  floor. Component-valid checks accumulate; the converse is explicitly false,
  with two invalid nonzero-weight checks that cancel. Random challenges,
  degree/cardinality bounds, transcript/commitment binding, extraction, and
  PCS/PCD refinement remain above the theorem.
- `1894e4c86`, `f66dcd723`, and `4cfdaedbf` take exact FNSP-v3 through full
  16×3760 relation composition, real HidingFRI prove/verify, strict
  full-consumption transport, a canonical 76-lane statement, and generated
  by-name descriptor identity. It remains outside live `PredicateKind`, turn
  acceptance, durable exact-nullifier state, and block finalization.
- `a2b0ad947` plus `6f7c1b60b` give the catalog and Telegram a common typed
  viewer-blind consequence publication. A multi-reader Telegram route cannot
  return raw actor/session/operation/payload/diagnostic/state-head/result-value
  data; DMs retain the rich direct receipt path.
- `62e488353` records the primary-source research verdict. The intended new
  proving stack is Dregg-owned and modular: keep Lean/DescriptorIR as the
  semantic relation, keep Plonky3 HidingFRI as a differential reference, and
  prototype share-native tensor-RS/BaseFold PCS plus stateless holographic
  accumulation. Collaborative IVC is classical/Pedersen as published;
  FRIttata and distributed PIPFRI do not supply coalition privacy; UltraFold
  supplies distribution/layout rather than no-viewer security.

## 0.6. July 22 typed-boundary checkpoint

This section supersedes section 0.5 and older exact-FNSP residual sentences only
where they disagree. Every item below is banked; the active lanes listed after
them are not.

- `b1bbe1e47` batches the four deployed N4K4 BFV odd-NTT polynomials across all
  three RNS moduli with `RequireWgpu`: one input upload, fourteen dispatches,
  one queue submission, and one readback. Exact CPU differential and inverse
  recovery are retained. The hbox RX 6750 XT measured 8.912–9.315ms sequential
  versus 2.496–2.746ms batched, a **3.303–3.732×** improvement.
- `4272ac0e8` makes exact FNSP-v3 verification yield a privately constructible,
  non-`Clone` acceptance token carrying the exact accepted 76 lanes and
  independently recomputed prior/successor `FNS3` anchors. `c4d11dc89` binds
  that token to the complete proof-carrier bytes in the authenticated signed
  effect, refusing same-coordinate proof swaps and malformed carriers. This is
  an acceptance boundary, not live finalization authority.
- `534396df6` adds strict `FHUAC001` exact uniform-allocation certificates,
  fhIR worker request/session/replay binding, and the corresponding Lean exact
  certificate laws. The checker independently selects the volume-maximizing
  price under the lowest-index tie rule, recomputes exact volume, and verifies
  inactive-zero and deterministic largest-remainder/index-order fills against
  a caller-supplied grid; the worker cannot select its own grid.
- `f545810e1` adds the exhaustive versioned canonical fixed-record codec for the
  typed `EffectVmDescriptor2` algebra. Explicit tags, fixed field order,
  fixed-width little-endian integers, length-prefixed strings/vectors, full
  consumption, bounded/fallible allocation, a 64MiB cap, and a depth limit make
  the typed object recoverable and hashable without JSON spelling ambiguity.
  Raw Lean-emitted JSON is parser/build provenance only, not protocol relation
  identity.
- `98a66d1d3` repairs idempotent exact historical replay: the store reconstructs
  and validates the original before/after accumulator coordinates from the
  complete durable prefix even after later appends, checks exact faithful-root
  history membership, and neither writes nor rewinds the current head. Wrong
  values, forged successors, missing records, and corrupt/partial snapshots
  refuse.

Active but **not banked or gated at this checkpoint**: the canonical executable
FNSP relation/VK envelope and verifier cut-in; the CAS-last exact/legacy
transaction; the node finalization candidate; the collaborative Shamir-row
handoff; and the payload-free Dark Bazaar enter/refresh journey. Do not copy
their working-tree state forward as implementation authority.

The remaining live cut is architectural, not merely codec work: explicitly
migrate receipt/state identity from the legacy nullifier-root commitment to
`FNS3(root8,count)`; mint finalization authority only inside the executor and
carry it opaquely into the live selector/registry; install the house-blind BFV
apex in the player-facing host; and deploy the common journey through the real
web, Discord, and Telegram surfaces.

## 0.7. July 22 exact-chain, hosted-Bazaar, and executor-state checkpoint

This section supersedes sections 0.5–0.6 and older exact/Bazaar/side-table
sentences where they disagree. It separates banked substrate from the active
production weld and records newly found blockers rather than hiding them behind
the amount of code landed.

### Exact FNSP-v3 authority: global exact chain, independent player receipts

- `9b2b72f24` makes exact proof admission a consumed one-shot executor token;
  `8d790147f` reconstructs per-agent receipt heads from the validated durable
  receipt log and fences the exact route to its characterized single-root,
  single-spend Rust producer shape; `6202521e7` banks the activation authority.
- `0cb8b2dd8` banks the signed activation/frame log, exact-head CAS, and atomic
  receipt/faithful/exact/frame writer as explicit **non-live WIP**. It is useful
  persistence substrate, not evidence of a production call site.
- The first frame design incorrectly made every later exact spend extend the
  previous exact frame's player receipt and full state. That would have made
  Alice → ordinary turn → Bob impossible. `ea28662e0` and `e6f58f9b9` replace
  this with the correct Lean law: one global exact-nullifier/frame chain, while
  every frame independently authenticates the latest durable receipt of its
  own player at an exact receipt-log index and the global commit boundary.
  Activation authority now explicitly covers cursor/tip shape, durable cutover,
  exact head, federation, and executor policy. The updated module passes
  `lake env lean`.
- `89a1e112e` is the aligned Rust turn API. The activation hash binds
  federation, executor key, exact initial head, and dense receipt cutover
  cursor/optional tail. Frames carry the current receipt index plus a paired
  same-agent predecessor index/hash, enforce index order, and advance exact
  state globally across arbitrary players without imposing false full-state
  adjacency.
- `9611b43c6` is the aligned persistent authority: arbitrary-player frames over
  one global CAS, canonical receipt decoding, exact current-row and per-player
  predecessor proofs, same-snapshot CAS/validated-transition authority, and
  O(R+F) recovery. Its library check is green; the focused suite reached 8/9,
  with the remaining test stopped earlier than its old assertion because the
  concurrent online receipt-head hook now rejects the stale predecessor at
  generic append time (the stronger production behavior is being moved into
  that hook's own test).
- `aeab921eb` replaces the live receipt-predecessor scan with a maintained
  per-agent receipt-head index. Full open still validates the hostile durable
  prefix before deriving the index; online append then checks and advances the
  authenticated head incrementally. `4e932492a` additionally authenticates the
  active suffix boundary rather than trusting a derived cache across recovery.
  The exact accumulator's analogous sparse O(log N) witness/cache cut is still
  active and is not implied by these receipt-index commits.
- `b530a5239` adds an opaque, non-`Clone` durable actor authority reconstructed
  from full checkpoint + tombstones, with locked revalidation and hybrid-
  attested compacted-root authority. Restart/drift/tombstone/compaction and
  duplicate-signer/solo boundaries are covered. The adapted node activation,
  execution, and finalizer compile green with `dregg-node --lib --features
  prover` and are banked as explicit WIP in `5eba0b254`; `03f106d08` updates the
  actor test API. The files are coherent authority substrate, but still have no
  production blocklace caller at this sentence.
- The node/persist redesign and real blocklace selector are still active. At
  this checkpoint `prepare_exact_fnsp_v3_finalization` has no production caller;
  strict v3 is rejected by the legacy v2 carrier path before generic execution.
  The intended branch must preserve the validated-signed-turn token, divert v3
  before the v2 decoder and every RAM overlay/event/proving side effect, commit
  the exact durable CAS last, and install RAM only after fresh durable success.
- A federation audit found a second architectural boundary: v3 activation and
  frame identities transitively commit the local executor public key. Distinct
  honest validators therefore derive distinct v3 frame chains. `e0eb1aea9`
  records the corrective protocol in
  `docs/deos/EXACT-FRAME-CONSENSUS-IDENTITY.md`: v3 is explicit solo/devnet-local
  only and must refuse committee mode; v4 uses signer-independent activation
  and frame core IDs, with each validator's hybrid signature in a separate
  local envelope and finality/attested-root (or an optional threshold
  certificate over the fixed core ID) as federation authority. No threshold
  frame signer is claimed to exist today.
- Honest cryptographic scope: current v3 proves exact anti-double-spend/receipt
  continuity and hides its witness, but its 76 public inputs expose historical
  height/root, nullifier, value, asset, exact roots/counts, and outer anchors.
  The currently characterized executor slice additionally requires `value = 0`
  and no value commitment/conservation proof. It is **not** the private-value
  Dark Bazaar apex. Hidden amount/asset settlement still requires the
  ShieldedTransfer/fhEgg conservation/range layer to compose into this exact
  global authority. In particular, the existing
  `verify_stark_with_wide_bindings` composition joins the ring proof to the
  full-u64 sidecar through one BabyBear `legacy_binding` field (about 31 bits).
  Equality of that scalar is not cryptographic-strength same-opening and admits
  chosen-pair collisions at an unacceptable scale. A private-value successor
  must use one shared witness relation or make both proofs open the same
  faithful full-width commitment; v3 plus the current sidecar does not close it.

### Hosted private Bazaar: mounted contract, missing production worker

- `ff7a7fd36` banks the typed private-Bazaar game consequence: deployment-owned
  policy/market identity, durable Enter → LIST journey, concrete Dungeon XP
  adapter, signed/final exact-event verification, recovery, and viewer-blind
  public receipt. `a619f51b4` mounts the same opt-in deployment contract through
  web, Telegram, and Discord and deletes the old string-flattening compatibility
  entry point.
- The typed `apply_private_settlement` / `recover_private_settlement` boundary is
  real, but only tests invoke it. No production private-worker listener yet
  consumes an out-of-band clearing receipt and calls that boundary. Frontends
  must never receive the private witness, winner, or raw private receipt.
- `7a873d5d2` repairs restart identity. A worker-private persisted commitment
  blind is bound to one exact market instance + proof session/rule + canonical
  private-order input; reuse with changed bids refuses. The durable source key
  is the typed semantic clearing claim (order root, price, volume, winner), not
  a timestamped receipt or chained turn envelope. Fresh proof/turn/receipt
  evidence is independently reverified. The strict binding/root unit and full
  catalog restart→reissued-evidence→exactly-once-XP gates join the six authority
  tests for 8/8 green in isolated clean snapshots. The integration run set
  `DREGG_ALLOW_UNAUDITED_PQ=1` because the remote archive lacks the verified PQ
  authority; this is functional evidence, not a PQ assurance claim. The
  remaining production seam is the actual
  finalized-private-receipt worker listener and replay loop, including private
  custody of the blind/input record.

### Executor consensus side state: repaired layers and live residuals

- `77c8da611` fail-closes the Lean producer for effects whose Rust path mutates
  unprojected consensus accumulators; a stale Lean root is no longer restamped
  over a different Rust side-table successor.
- `a977c996d` stages rate-count/sum deltas per action, exposes them within the
  same forest, publishes only after final Rust + Lean acceptance, supports
  active `Cases`, rejects ambiguous multiple windows, widens sums to `u64`, and
  adds a canonical bounded snapshot codec. Six transactionality and three codec
  tests are green. The snapshot still needs to join the node's same redb
  finalized-turn transaction and restart seed.
- `a0591caec` binds Promise/Notify/React to the registered actor and condition,
  makes the reactive registry canonical, and journals rollback. `d502ecfd2`
  adds candidate resolve/commitment/snapshot APIs so blocklace can mutate the
  isolated candidate executor rather than a disconnected NodeState registry.
  `64477cd9c` separates React replay nullifiers from note-spend nullifiers.
  `9af0f439b` now joins the canonical pending registry and that dedicated React
  nullifier set to the durable executor-state stage/replay/truncate path, with
  domain-separated predecessor CAS, exact successor checks, restart loaders,
  and divergent-tail rollback. The final nonempty-registry focused replay tooth
  remains pending a shared remote cargo lock; do not promote the prior
  compile-green checkpoint into a completed full-suite claim.
- `5d0c79da5` adds a bounded canonical factory restart image, rolls back factory
  quota after late rejection, and extends the producer-reference checkpoint
  across factory/budget/rate/reactive/migration/accumulator/receipt scratch.
  Two cell and three turn tests are green. The live persist/reseed hook remains
  part of the same executor-state weld.
- `d34a35787` adds lossless durable note commitment `(commitment,value,seq)`,
  revocation `(key,height,seq)`, and bridged-nullifier/insertion-ordinal tables,
  strict canonical snapshots, same-transaction finalized-turn hooks, sparse
  rate snapshot loading, fail-closed bounds/legacy handling, and divergent-tail
  rollback. `dregg-persist --lib` is green and its focused suite is 5/5. Live
  blocklace capture and fresh-executor reseed are still active; the persist-only
  green does not claim they are already in use.
- `182ca73de` proves the pure per-cell receipt-head reconstruction law across a
  compacted-prefix baseline plus dense live suffix, preserving provenance for
  removed cells and refusing malformed floor/gap/duplicate records. Durable
  baseline/current tables, compaction/tail recovery, and executor reseed remain
  to be welded.
- `af090f03c` adds canonical local custom-program registry persistence,
  write-before-publish deployment, fail-closed restore/revalidation, and fresh
  executor seeding. It is node-local administration, not yet a consensus-ordered
  deployment protocol. Validators with unequal registries can diverge. A live
  deployment receipt must bind prior/new registry roots, canonical descriptor
  content/availability, VK and version policy, authority, federation/epoch, and
  finalization height. The DFA verifier registry remains categorically separate.
- `a3679f739` repairs a generic blocklace atomicity bug which was not
  exact-v3-specific. `execute_finalized_turn` now keeps the complete candidate
  isolated through the durable outcome and publishes ledger, receipt head,
  pending resolutions, activity, artifacts, and events only on fresh success,
  matching the existing Lean
  `Dregg2.Exec.Durability.durableApply_reject_stays` law. The hostile test covers
  a targeted store failure, nonfresh response, and real post-prologue body
  rejection. A focused node build has not yet completed against the concurrent
  exact-v3 API redesign; it stopped on foreign exact-v3 compile drift without a
  blocklace diagnostic, so this commit is banked WIP rather than a current full
  node green. Typed durable charged-rejection receipts, replacement of the
  temporary reactive NodeState mirror by its redb CAS, and atomic/recoverable
  proof-artifact persistence remain separate residuals.

### Optimizer and portable GPU truth

- The strict `FHUAC001` fhIR allocation certificate is green: the checker
  independently recomputes the caller-grid maximum-volume price, lowest-index
  tie, exact volume, inactive-zero fills, and deterministic largest-remainder
  allocation. The typed request/session/replay digest covers `(K, ordered
  side/quantity/limit)`; it is not JSON and is allocation authority, not hiding.
  Hbox results are solver 9/9 and fhIR 10/10; the eight Lean certificate
  keystones are axiom-clean.
- The portable WGPU path is real Vulkan, not HIP/CUDA. Exact BFV odd-NTT and
  TFHE compare/select kernels are differential-green on the hbox RX 6750 XT and
  persvati AMD Strix iGPU; the 32 selection-mask PBS lanes now batch key switch,
  transform, extraction, pair-add, and one readback. Loaded timings are
  machine/contention-sensitive and should not be promoted into a stable ratio.
- Live `fhe_clear` still uses CPU tfhe-rs, and Dark AMM multiplication still
  uses CPU fhe.rs because the complete BFV extended-basis/tensor/relinearization
  GPU seam is absent. The exact WGPU Ristretto verifier is intentionally disabled
  for performance (about 4.643s versus 9.827ms dalek at 4096 terms).
- `e46ff8450` installs the owned exact host-parallel Bulletproof prover and
  canonical bounded-nesting quorum scheduler without changing proof bytes.
  The real six-share Descent/Dark-Bazaar custody settlement is green in release
  on persvati's 24-core CPU in 514.36s (nextest 514.612s), versus the historical
  1086.009s: 2.111x end-to-end and 52.6% less wall time. The embedded signer,
  quorum, order, nonce, and replay refusal teeth also pass. This run used
  `DREGG_REQUIRE_LEAN=0 DREGG_ALLOW_UNAUDITED_PQ=1` only because the remote
  fixture lacks the verified ML-DSA bootstrap; exact BFV/VSS/Bulletproof custody
  remained enabled. It is still about 8.6 minutes and runs on Rayon CPU, not
  GPU, so it is not gameplay-ready. The next hard cut is a native-PQ
  HidingFRI/AIR range/conservation relation over the existing odd-NTT/table
  substrate, not the slower WGPU Ristretto verifier.

## 1. The honest current sentence

The repository has a transferable, source-row-bound BFV/Poseidon same-opening
proof; a composite quorum + HidingFRI + same-opening verifier; public-only hosted
verifier reconstruction; and a green full-profile integration wiring the exact
encrypted rows through a live authenticated PartyMPC crossing into atomic
Bazaar/game consequences. The same-opening proof, composite verifier, hosted
registry, live crossing, custody envelope, fhIR raid allocation, and the
full-profile apex gate are green. The Warden's Keep crown consequence is also
green at its exact heavy-release gate.
The decisive current hbox run passed 1/1 under the full nextest profile with
both DREGG_REQUIRE_LEAN=1 and DREGG_REQUIRE_PQ_CORES=1 and no authority-core
fallback: 85.923s proof, 7.956s sealed PartyMPC crossing, and 167.008s internal
total.
The exact relation prover has since been accelerated without changing its proof
format or verifier: the fixed production relation now proves in **23.445s** in
its hostile standalone gate, about **3.66×** faster than that strict-apex
capture. A new full-apex timing has not yet replaced the 167.008s authority run.
The newer composed-game evidence has also advanced: the complete offerings
target is 117/117, the private-raid surface is 8/8 in one current invocation,
the narrated private-raid relic capstone is 1/1, the incarnation-bound common
game spine is 21/21, Telegram's combined game journey is 77 tests, and the viewer-safe web rail is
green at its exact focused gates. The lower private-raid forest is now 2/2 at
its focused engine gate; the Discord Chutes weld remains pending at this ledger
checkpoint.

This is **not** a no-single-viewer system. The deployed same-opening prover still
receives the complete private witness and BFV openings in one process; source
verification sees plaintext orders and encryption randomness; PartyMPC arithmetic
now refuses uncertified or malformed Beaver rows but still trusts the certifying
preprocessing authority; and the distributed-custody
surface now proves committed-share custody, the first three share-native linear
zero constraints, and owner-local kind/quantity ranges, 128-way one-hot
selection, nine-slot semantic message derivation, and all 12,288 BFV short
coefficients in `[-32,31]`, linked to the exact distributed commitments without
reconstructing the witness. The exact fhe.rs polynomial message-table/BFV
equations, Poseidon/root, and clearing constraints still run inside the
monolithic Bulletproof/R1CS backend.

This is also **not an end-to-end post-quantum apex**. Native clearing quorum and
PartyMPC transport now have separately green ML-DSA and ML-KEM-backed profiles,
and BFV is lattice-based. The sealed route-root replacement is now full-apex
green with six transport signs and six verifies rather than thousands of per-
frame operations. More importantly, the exact ciphertext/root relation is a
Bulletproof over Ristretto/Pedersen with a discrete-log + Fiat–Shamir security
floor, and distributed custody still uses Ristretto/Pedersen. HidingFRI,
Poseidon, BFV, and the wide Lean/Rust bindings have their own stated
soundness/security floors; their presence does not convert the remaining
classical seams into a post-quantum composition.

## 2. Current status at a glance

| Surface | State | Exact authority |
|---|---|---|
| BFV/Poseidon same-opening proof | **GATED** | private_book_bfv_zk: 2/2 release green; hostile proof test 65.765s |
| Composite private clearing verifier | **GATED** | private_bfv_attested_clearing: 1/1 release green; 62.958s |
| Exact source rows and ingress weld | **GATED in Lean and the full-profile apex** | DarkBazaarPrivateIngressCutover: 11 clean; apex 1/1 green |
| Public-only hosted verifier registry | **GATED** | two hostile registry tests: 2/2 green |
| Authenticated live PartyMPC crossing | **GATED; NATIVE PQ PROFILE SEPARATELY GATED** | original crossing 2/2 release; native ML-DSA + ML-KEM/X25519 integration 5/5 and transport units 5/5 |
| Sealed native-PQ PartyMPC crossing | **GATED IN STRICT FULL APEX** | protocol teeth above plus strict full apex 1/1; 7.956s crossing vs v4 1,202.240s timeout, exactly six transport signs + six verifies independent of 1,302 gates |
| Certified PartyMPC preprocessing | **LIVE FHTRI004 GATED, AUTHORITY-OPERATED; DURABLE ONE-USE CUSTODY GATED; FHTRI005 STAGED** | live FHTRI004 certificate still uses the authority-operated formation; durable ledger suite 14/14 and every raw certified runner/transport constructor refuses; FHTRI005 real-BFV party-local ceremony 9/9 reaches `AwaitingCrossTermProvider` without production ideal OT, but is not the live source |
| Binary triple sacrifice | **COMPOSED INTO LIVE FHTRI004** | one kept +128 sacrifice candidates/gate; commit before challenge, authenticated rho/sigma/tau openings, opaque release only after every equation; legacy factory/session downgrade and pre-gate row substitution refuse; this is still authority-operated preprocessing, not dealer-free malicious MPC |
| Native clearing quorum | **GATED** | full canonical ClearingClaim under roster-pinned ML-DSA + Ed25519: 1/1 hostile native gate; classical compatibility 6/6 |
| Cell-owned PQ turn identity | **GATED CLASSICAL RUNTIME; LEAN ROW GATED; COMPOSED PROOF PATH FAILS CLOSED** | runtime gates above plus Lean-authored 127-column rotation descriptor, exact 108-PI/120-constraint/111-range shape and Rust parse canary; outer ML-DSA composition remains unwired |
| Restartable live private-clearing apex | **GATED, NOT END-TO-END PQ** | strict v5 authority run 1/1 in 167.054s nextest / 167.008s internal; its proof was 85.923s, while the subsequently accelerated identical fixed relation is 23.445s in its hostile gate; sealed crossing 7.956s, audited Lean PQ cores required; exact relation still classical Bulletproof |
| Distributed input custody | **GATED** | custody/semantic/shortness private_book_distributed_inputs: 5/5 release green |
| Distributed private-order proof | **GATED THROUGH FINAL EXACT BFV + POSEIDON ROOT LINK** | base custody, exact 4×384 quotients, worker 65,536-coordinate relation, and mandatory four-owner nonlinear root certificate; production A/B substitution refuses 1/1 in 190.133s |
| Distributed real same-opening prover | **FHDBE002 FOUR-CERT ENVELOPE GATED; CLEARING/PQ COMPOSITION OPEN** | workers never reconstruct orders/openings/quotients; 6,663-byte root cert ties exact BFV input commitments to the deployed Poseidon root; full production gate 1/1 in 190.926s; clearing certificate, exact sampler image, distributed source-viewer, and PQ replacement remain |
| Bazaar crown consequence | **GATED THROUGH REAL SHIELDED SPEND + DURABLE ORCHESTRATION + TELEGRAM CONTROLLER** | exact private-BFV apex + persist spend + signed Dungeon crown; three one-use resources reserve atomically; apex 1/1, orchestration 3/3, journal 4/4, Telegram public-only controller 4/4; long-poll mounting and durable apex custody remain |
| fhIR exact raid allocation | **GATED** | Rust integration 6/6 release green; FhIRRaidAllocationBinding: 7 clean |
| Narrated Dungeon and relic-oath composition | **GATED BY TARGET** | narrated Dungeon 3/3; repaired relic oath 2/2 |
| Common game-operation spine | **DURABLE EPOCH CUSTODY GATED FOR CATALOG + TELEGRAM** | bound routing 21/21; atomic/fsynced incarnation + monotone per-session generations 4/4; Telegram hostile epoch callbacks 2/2; web/Discord/WeChat/native migration remains |
| Telegram and viewer-safe web journey | **GATED BY TARGET; COMMON VIEWER-BLIND PUBLICATION BANKED** | prior Telegram/web gates remain; shared Telegram status and shielded operation returns now accept only the catalog-audited `PublicGameReceipt`, with hostile typed projection 2/2 and ordinary DM/group/document paths green |
| Private Bazaar → Dungeon consequence | **GATED AT TWO REAL GAME MECHANICS; STRICT TELEGRAM COMMAND AVAILABLE** | verifier apex→Mender plus persist spend→Red/Blue crown; one-use orchestration 3/3 + 4/4 and `/shielded-crown` controller 4/4; deployed bot policy/routing still must mount it |
| Private-raid capability/Arena and narrated-relic composition | **GATED BY TARGET** | relic capstone 1/1; surface 8/8; lower atomic forest 2/2 (engine semantics only; its persvati fixture opted into the unaudited PQ test backend) |
| Chutes → Dungeon closed-command weld | **PENDING GATE** | HEAD target contains 3 tests; no result supplied |
| Lean-native Descent offering/campaign | **GATED** | both targets are green inside the current dreggnet-offerings 117/117 invocation |
| hbox build substrate | **QUALIFIED FOR GPU LANES** | current filesystem probe: 64GiB free after pruning four inactive, reconstructible build targets; active GPU/game/node/PQ lanes and deployed services were preserved |
| Collective GPU additive fold | **GATED** | 1/1 on real RX 6750 XT; GpuResident via wgpu/Vulkan, not HIP |
| Portable HidingFRI GPU path | **TRANSCRIPT + EXACT EXT4 COMMIT PATH GATED; DISTRIBUTED FOLD/QUERY OPEN** | byte-identical full proof 2/2 with five mapped transcript buffers; standalone BabyBear^4 fold matches pinned Plonky3 at arities 2/4/8 through 2^20 and is up to 3.55× faster; the full PCS commitment hook is banked, while distributed fold/orchestration and query privacy remain new work |
| Portable Ristretto verifier MSM | **GATED FOR CORRECTNESS, PERFORMANCE RED** | exact adaptive radix-16/radix-128 required mode through 4096 terms; fixed radix-128 4096 was 4.722s GPU vs 9.563ms dalek and standalone adaptive was 4.643s vs 9.827ms, so disabled by default |
| Portable encrypted TFHE PBS | **GPU-RESIDENT FULL-RADIX PUBLIC COMPARISON GATED** | all 16 carry-clean radix blocks stay resident through one final readback; strict 3/3, same late comparison 1.891881s→0.741850s (2.55×), encrypted predicate drives `if_then_else`; ciphertext-to-ciphertext/min/select and broader shapes remain |
| Exact BFV + wide PQ Lean boundaries | **NATIVE/WGPU SUBSTRATE GATED; q0 TERMINAL AUTHORITY REJECTED, REPAIR ACTIVE** | the first complete 4,096-term equation, the proved 2^20×48 odd-NTT schedule (1,032,192 rows), exact q0/q1/q2 WGPU transforms, reusable 2^18 key certificate, and concrete q0/N8 butterfly AIR/permutation teeth remain real substrate; `92c881a0a`'s HidingFRI artifact is not sound proof authority because its terminal product is not linked to the carrier coefficient and its butterfly arithmetic/geometry are not pinned; all-RNS expansion must wait for that faithful transform/LogUp join |
| Additive PQ share commitment | **EXPERIMENTAL ALGEBRA/KAT; PRODUCTION REFUSED** | context-bound BabyBear/SIS-style additive commitments, exact links, randomized hiding coordinates, and short-kernel extraction are Rust/Lean green; dimensions are not estimator-approved and live wide Ristretto shares are not bounded coordinates, so `productionPqReady = false` |
| Wide shielded value binding | **GATED, TRANSITIONAL** | Turn shielded 7/7 and circuit wire/alias 4/4; live no-mint still retains the classical conservation proof and old note/root seam |
| Faithful wide note tree and history | **LIVE V2 SPEND + LIVE SOLO EXACT-V3 FINALITY** | live FNO2/FNC2/FNF2 custody remains; exact v3 verifies its signed HidingFRI carrier before generic execution and atomically advances activation, faithful/exact/frame state, receipts, artifacts, observer events, and typed resolution outbox; the rolling faithful↔exact bridge refuses faithful-only growth once installed. The current authority is deliberately solo/devnet-local because frame identity still binds the local executor; federation-wide deterministic frame identity remains open |
| Canonical typed relation encoding | **GATED AS A CODEC; FNSP VK/VERIFIER CUT-IN PENDING** | exhaustive fixed-record `EffectVmDescriptor2` encode/decode and semantic fingerprint are strict, bounded, full-consuming, and JSON-spelling invariant; JSON is provenance only. The active FNSP relation envelope must still be banked and the verifier must execute the recovered canonical program bytes before this becomes live verifier identity |
| Hostile external fhIR optimizer protocol | **GATED, INCLUDING EXACT UNIFORM ALLOCATION** | existing problem/session/nonce/manifest/certificate/checksum/replay binding remains; `FHUAC001` independently verifies the caller-grid optimum, lowest-index price tie, exact volume, inactive-zero fills, and deterministic largest-remainder/index fills, with fhIR worker replay binding and Lean exact certificate laws |
| Lean handler-cutover export | **GATED** | credential-preserving export accepted genuine/rejected forged; archive symbol present, zero unresolved non-toolchain initializers; 44.60s warm closure rebuild |
| Aggregate Market metatheory | **GATED** | lake build Market green at 8747 jobs after the live-host/optimizer additions |

## 3. Transferable BFV/private-root same-opening proof

### What is implemented

**fhegg-fhe/src/private_book_bfv_zk.rs** implements a fixed
\(N=4, K=4, n=4096\) Bulletproof R1CS relation. This proof seam has a
**classical-security** floor: it uses Bulletproofs over Ristretto/Pedersen and
the discrete-log + Fiat–Shamir assumptions. One proof binds the same hidden
order selectors, quantities, and private-root blinding to both:

1. the deployed Poseidon2 private-book root; and
2. the exact four public-key BFV ciphertext rows, using the pinned RNS equations
   and bounded short witnesses in [-32, 31].

The relation uses the actual fhe.rs SIMD encoding. It applies 128
transcript-derived Rademacher compressions per modulus after commitment. The
2^-128 statement applies only to that equation-compression error; it is not a
claim about total protocol security. Total security also depends on BLAKE3,
Poseidon2, and the implementation. The yoloproofs dependency is an
experimental/reference implementation, not a production certification. The
lattice basis of the BFV ciphertext relation does not make its Bulletproof
carrier post-quantum.

The proof does **not** establish:

- exact membership in a seeded sampler image, seed entropy, seed distinctness,
  or a CBD distribution;
- DKG correctness or collective-key well-formedness;
- owner-separated witness custody;
- maliciously secure distributed proving.

### Exact Rust gate

**fhegg-fhe/tests/private_book_bfv_zk.rs**:

- proof_wire_is_bounded_versioned_and_fail_closed
- exact_pk_bfv_and_poseidon_relation_refuses_every_public_substitution

Captured result: **2/2 green in release**. The hostile proof/substitution test
took **65.765s**. It refuses substitutions of the public key, ciphertext
coefficient, private root, session, modulus, and layout.

## 4. Composite receipt and exact source-row binding

### Composite verifier

**dreggnet-market/src/private_bfv_attested_clearing.rs** defines
PrivateBfvAttestedClearingVerifier. Acceptance is the conjunction of:

1. the pinned authenticated committee quorum;
2. the HidingFRI clearing proof; and
3. the BFV/private-root same-opening proof.

new_source_bound pins the full claim nonce, public clearing statement,
parameters, collective public key, four exact ciphertext rows, and canonical
source input pairs. The verifier derives the packed fold from those exact rows.
The claim layout includes:

- the exact four proof ciphertext rows and private root;
- each live source message commitment paired with its exact proof-row
  ciphertext;
- the packed fold ciphertext; and
- the board commitment.

Digest-only verification is intentionally insufficient: verify() returns false
and relying code must call statement-directed verify_claim.

**dreggnet-market/tests/private_bfv_attested_clearing.rs** contains:

- receipt_requires_quorum_hidingfri_and_exact_bfv_root_proof

Captured result: **1/1 green in release**, **62.958s**. This gate validates the
composite proof and hostile public substitutions, but its clearing transcript is
still produced with simulate_public_transcript; it is not the live PartyMPC gate.

### Exact ingress rows

The current **dreggnet-market/tests/private_clearing_apex_e2e.rs** constructs four
canonical PrivateBookCiphertexts. The three live seller/bid board inputs use
those same proof rows; the fourth is canonical padding. Source
messages/signatures and exact row ciphertexts occupy WriteOnce board slots, and
the packed fold in the receipt is computed from those exact rows. There is no
second re-encryption whose equality is merely asserted by committee signatures.

This closes the detached-dual-encoding bug at the public statement boundary. It
does not make ingress private from the process performing source verification:
that process still sees the order and encryption randomness.

Relevant Lean authority:

- **metatheory/Market/PrivateBookEncryptionBinding.lean** states the exact-opening
  law and preserves the RED detached-statement counterexample.
- **metatheory/Market/DarkBazaarPrivateIngressCutover.lean** proves the exact
  ingress/proof/claim weld and refuses row, order, auxiliary-value, root,
  session, and quorum substitutions. Direct gate: **11 clean**.
- **metatheory/Market/DarkBazaarAttestation.lean** retains the older RED result
  showing why digest-only composition did not bind BFV rows. That
  counterexample describes the weak boundary, not the repaired proof path.

## 5. Hosted verifier registry and restart boundary

**dreggnet-market/src/fhegg_verifier_registry.rs** replaces a quorum-only hosted
verifier slot with FheggVerifierRegistry, which dispatches both:

- legacy AuthenticatedQuorum; and
- PrivateBfvAttested.

The registry carries verifier_id, verify, and the load-bearing
statement-directed verify_claim. PrivateBfvHostedVerifierConfig owns public
deployment material only:

- an independently pinned verifier ID;
- the ordered quorum verification-key roster and threshold;
- value bits;
- BFV public identity;
- claim nonce and clearing statement;
- BFV parameters and collective public key;
- the exact ciphertext rows; and
- the canonical source inputs.

It owns no private-book witness, BFV seeds, secret key, or decryption shares.
Installation reconstructs the complete verifier, checks that the BFV-opening
roster agrees with the signature roster, recomputes the verifier ID, and
compares it to the independent pin. DarkBazaarOffering preserves the legacy
with_fhegg_quorum path and adds registry/private-attested constructors.

**dreggnet-market/tests/fhegg_private_verifier_registry.rs** contains:

- exact_public_config_installs_full_private_verifier_in_hosted_operation_registry
- pinned_reconstruction_refuses_every_public_substitution

The hostile test changes the pin, nonce, clearing session/root/result/rule, BFV
identity, source message/row/coefficient, roster order/threshold, value bits,
and BFV-opening roster. Captured result: **2/2 green**.

**metatheory/Market/DarkBazaarLiveApexHost.lean** proves that exact pinned public
configuration reconstruction is required and that verifier-ID equality alone is
not sufficient. Its direct gate is **16 clean**. Its live-MPC conclusion still
depends on the explicit LiveMpcBackend.sound premise.

## 6. Live PartyMPC crossing

### Transport and crossing code

**fhegg-fhe/src/mpc_party/transport.rs** now implements two explicit transport
profiles:

- `NativePostQuantum` roster-pins ML-DSA-65 identities and authenticates every
  frame under the native profile;
- each native frame combines a fresh ML-KEM-768 encapsulation with the existing
  X25519 contribution through dregg's canonical hybrid combiner before
  XChaCha20-Poly1305 protects the peer payload;
- `ClassicalCompatibility` is explicit rather than an implicit downgrade;
- signatures bind the profile, identity, session, circuit role, route,
  sequence, payload, and roster key;
- CrossingPartyMachine and CrossingCoordinatorMachine drive the crossing;
- prepare_private_book_crossing_input validates the exact packed private-book
  shape;
- verify_public_crossing_transcript reconstructs and verifies the public reveal
  transcript; and
- fresh_crossing_preprocessing_seed separates invocations.

The native profile removes Curve25519-only confidentiality and Ed25519-only
frame authentication from this boundary, but it makes no forward-secrecy claim:
recipient ML-KEM and identity-DH keys are long-lived. More importantly,
authenticated transport does not imply honest arithmetic. The crossing
protocol remains semi-honest. Its Beaver rows are now authority-certified and
globally checked, which closes the earlier unauthenticated malformed-triple
acceptance wound; it is not a distributed maliciously secure preprocessing
protocol and still has no proof of honest private-input share formation.

### Certified preprocessing boundary

**fhegg-fhe/src/mpc_party.rs** now hard-swaps certified custody to `FHTRI004`.
For every kept multiplication row the authority generates and commits 128
sacrificial candidates, fixes two GF(2^128) MAC lanes before challenge, and
authenticates the rho/sigma and tau openings through distinct commit/check
barriers. Only an opaque successful sacrifice capability releases the kept row.
ML-DSA-65 and Ed25519 then sign the same canonical statement over the exact
roster/base session, unique ceremony, candidate manifest, setup/opening/
challenge digests, 128 rounds, two lanes, and kept-row commitments. Keygen,
sign, and verify require the installed verified Lean cores even if
`DREGG_ALLOW_UNAUDITED_PQ=1` is set.

The live runtime boundary was audited after the first green. Certified sessions
now reject the legacy dealer factory, every runner and transport machine
revalidates the exact certificate/party row before private ingress or gate zero,
and FHDBv002 restart transport carries and verifies the full hybrid formation
certificate rather than promoting compact binding bytes. The parser cross-
checks receipt/base/roster/party/gate coordinates and refuses FHTRI003,
trailing bytes, hostile counts, and row/certificate substitution. Allocation
ceilings are checked before reserving candidate/MAC storage; the full 1,302-gate
apex uses 335,916 candidates and 1,007,748 authenticated bits.

Current gates are release checks green, verified-core certification **5/5 in
23.100s**, sacrifice/authentication/transport **17/17**, FHDB restart **1/1 in
7.768s**, and strict full apex **1/1 in 222.487s**. This closes the concrete
lying-response and certified-session bypasses; it does not establish malicious
MPC. One centralized authority still constructs all candidates, sees the MAC
keys, and supplies the beacon; the receipt is an authority-signed digest summary
rather than a publicly replayable ceremony transcript; identical protected row
bytes have no durable compare-and-set consumption tombstone; private-input
validity remains semi-honest; and no quantified joint PQ reduction exists.

**fhegg-fhe/tests/party_mpc_crossing_transport.rs** starts with the exact four BFV
proof rows, folds them, masks and threshold-opens only a one-time-padded
carrier, gives each party its local nine-slot share, and checks that
authenticated machines reveal only (p*, V*). It contains:

- exact_packed_rows_drive_authenticated_crossing_and_bind_every_public_bit
- packed_private_input_refuses_wrong_shape_or_noncanonical_share

The original exact-crossing target passed **2/2 in release**, **1.099s**. After
the native profile cutover, the focused end-to-end native integration passed
**5/5**, including exact packed private crossing and hostile replay, downgrade,
and roster-key substitution cases; transport units passed **5/5**. Those native
PQ tests used the explicit unaudited test backend because the remote lane lacked
the verified Lean cores, so they are control-flow/transcript evidence rather
than verified-core evidence.

### Apex cutover

The current **dreggnet-market/tests/private_clearing_apex_e2e.rs** no longer calls
simulate_public_transcript. It:

1. retains the threshold parties from collective key generation;
2. derives shares from the packed exact proof rows;
3. runs the authenticated crossing machines;
4. verifies the public crossing transcript; and
5. requires the resulting (p*, V*) to equal the HidingFRI statement before the
   committee signs the composite receipt.

This is the correct code-level crossing. The decisive hbox invocation used
**--profile full**, **DREGG_REQUIRE_LEAN=1**, and
**DREGG_REQUIRE_PQ_CORES=1**. The first verified run passed **1/1 in 114.033s**.
The pre-v5 exact-attribution rerun passed **1/1 in 124.159s nextest elapsed**
(**124.116s** on the test's internal timer) with the current-source Lean splice
and required verified ML-KEM/ML-DSA authority cores; no unaudited authority-core
fallback was enabled. The BFV same-opening proof, HidingFRI proof, live PartyMPC
crossing, hosted verifier reconstruction/restart, verified ML-DSA
turn-authority core, atomic consequence, and replay refusal all ran.

The current sealed-v5 recapture passed **1/1 in 167.054s nextest elapsed**
(**167.008s** internal) under the same strict Lean/PQ-core requirements and
unchanged 1200-second ceiling. Proof construction took **85.923s** and the
packed fold plus complete sealed PartyMPC crossing **7.956s**, versus the v4
per-frame-signature crossing's 1202.240-second timeout. The n=2 transport used
exactly six ML-DSA signs and six verifies independent of 1,302 gates; the two
quorum signatures were each checked in four composite verifier contexts.

The same proof format and verifier now have an exact host-parallel prover path.
Rayon schedules independent constant-time dalek commitment-MSM chunks, sibling
R1CS commitments, and inner-product rounds without changing transcript order or
group arithmetic. The production fixed-N hostile relation gate passed **1/1 in
64.631s**: proof construction was **23.445s** (23.074s inside R1CS), honest
verification was **8.213s**, and all four cryptographic substitutions plus two
structural substitutions still rejected. An independent 131,073-term exact MSM
differential measured **1.226s serial / 0.396s parallel** on 16 threads. This is
about **3.66×** faster than the 85.923s proof in the strict apex recapture; the
full strict apex has not yet been recaptured with this optimization.

That is a verification statement about the required authority cores, not an
end-to-end post-quantum claim. The apex still depends on the classical
Bulletproof/Ristretto/Pedersen
exact-relation seam and the separately stated HidingFRI/Poseidon soundness
floors. BFV's lattice security does not remove those assumptions.

The first hbox invocation used the default nextest profile. It built the current
Lean material but ran **0 tests** because the apex binary is deliberately
excluded as heavy. That invocation is build evidence only, not a gate. The
full-profile invocation is the authoritative green.

The archive used by the apex run emitted warnings for **five unresolved
initializers** and did not export **dregg_exec_handler_turn**. That later
residual is now closed independently: the replacement export retains
`lowerForestG` credentials, runs the four-leg gate on the exact pre-state before
handler dispatch, and fails closed in strict test mode. On hbox the ABI tooth
accepted the genuine credential and rejected the forged one in 0.188s; the
archive defines the export and has zero unresolved non-toolchain initializers.
The resumable bounded-parallel closure rebuild is 44.60s warm. Earlier
unaudited-fallback, local archive-closure, remote install-abort, and compiled-out
runs remain historical diagnostics only.

### Timed attribution and GPU priority

The exact timed run is captured in
**/tmp/private-clearing-apex-cpu-timed.log**. WGPU precompute was unset, so this
is the current CPU baseline for the exact relation seam:

- BFV/Bulletproof prove: **63.153s**;
- four full BFV proof verifications: **28.998s** total;
- prove + four verifies: **92.151s**, or **74.2%** of the 124.116s internal
  end-to-end time;
- generic Bulletproof cryptography after subtracting relation synthesis:
  approximately **60.838s proving + 19.959s verifying = 80.8s**;
- HidingFRI: **22ms**; and
- packed fold + PartyMPC: **621ms**.

The immediate GPU priority is therefore the classical Bulletproof/Ristretto
MSM path, followed by any relation-specific acceleration that preserves exact
semantics. The already-GpuResident additive fold is not the apex bottleneck in
this fixture, and accelerating it cannot turn the classical Bulletproof seam
into post-quantum security.

The exact host-parallel path has now taken the first large cut out of that
bottleneck. The portable WGPU public Pippenger remains disabled because its
measured group MSM is dramatically slower than dalek; the retained WGPU
scalar-preparation context is not presented as the source of the 3.66× result.

The Lean companion, DarkBazaarLiveApexHost.lean, models the weld from exact
ingress through same-opening evidence, live MPC output, claim, hosted verifier,
and consequence. Its 16 clean theorems do not discharge
LiveMpcBackend.sound; that premise is precisely where malicious arithmetic,
codec, and implementation refinement remain.

## 7. Custody and the no-single-viewer residual

### What the custody surface does

**fhegg-fhe/src/private_book_distributed_inputs.rs** lets four owners expand only
their own local witness vector: order kind, quantity, 128 option-selector
coordinates, nine semantic message coordinates, BFV u/e1/e2, and the owner-0
root blinding. Owners distribute n-of-n additive Ristretto shares to workers,
commit with vector Pedersen commitments, receive local packet
acknowledgements, and produce a canonical public certificate. Under the stated
confidential-channel and distinct-principal assumptions, any strict subset of
workers has uniformly masked shares under the CSPRNG/BLAKE3 scalar-sampling
assumption.

This layer assumes confidential authenticated private packet transport. Packets
deliberately have no production wire codec. The public certificate binds custody
events; it is not the R1CS proof and does not establish the same-opening
constraints.

**fhegg-fhe/src/private_book_distributed_prover.rs** adds worker-process and
coordinator APIs. The coordinator API never accepts scalar shares or openings.
The generic fixture backend still returns public digests only, but it is no
longer the strongest backend.

**fhegg-fhe/src/private_book_canonical_backend.rs** uses the owned Bulletproof
fork's logarithmic `LinearProof` to prove four exact committed-share openings
per worker. At degree 4096 each owner proof is 992 bytes rather than 12,436
opening scalars (12,435 vector coordinates plus the blinding). The same
artifacts prove the first share-native constraint
layer: for each owner 1..3, request-derived random coefficients compress the
eight root-blinding coordinates and the verifier checks that the workers'
committed linear images reconstruct to zero. The challenge is derived only
after the complete request, certificate, ordered commitment vector, roster,
worker/owner order, widths, and generator namespace are bound; prover nonces are
fresh CSPRNG output committed before that challenge.

Each owner certificate now also carries:

1. one four-value Bulletproof range proof over
   `[kind, 7-kind, quantity, 15-quantity]`;
2. one Bulletproof R1CS proof with 73,856 multiplication gates at production
   degree: 128 gates make the option coordinates boolean and exactly one-hot,
   select `16*kind + quantity`, and derive the private relation's eight unary
   demand/supply slots plus its injective `kind + 8*quantity` root-code slot;
   the other 73,728 gates range every `u/e1/e2` coefficient in `[-32,31]`; and
3. one transcript-derived random-linear `LinearProof` linking all 12,427
   non-root scalar commitments used by those proofs to the exact first 12,427
   coordinates of the same owner vector commitment whose worker commitments
   sum to it.

Thus the exact finite semantic order row is proved without disclosing it or
asking a worker/coordinator to reconstruct it. The batch link has
`1 / |Scalar|` random-linear-compression soundness error in the random-oracle
model. The proof digest is covered by the owner signature and the v4
session/deal/certificate domains. The strict per-owner artifact is 400,869
bytes at production width (8,293 bytes in the degree-16 fixture); the complete
four-owner/three-worker certificate is 1,605,710 bytes.
The commitments, proofs, and owner/worker signatures remain classical, not
post-quantum.

The banked v5 continuation (`fhegg-fhe/src/private_book_distributed_bfv.rs`)
starts only after that complete certificate and joint commitment. Its first
Fiat--Shamir challenge fixes 384 signed RNS quotient coordinates per owner.
Each owner supplies additive worker shares whose continuation-generator vector
commitments reconstruct to its owner commitment, proves every quotient in the
24-bit shifted interval with the conservative exact bound
`|q| ≤ 1,130,496`, and random-linearly links the R1CS commitments back to those
coordinates. The owner signature is verified before proof work, every worker
must acknowledge the private packet, and the public certificate contains no
shares. Production geometry is fixed at 16,384 coordinates per owner and
65,536 for the final worker proof. Focused release gates are **2/2 in 12.620s**.

Quotient construction is now exact rather than caller-supplied. Each owner retains a non-cloneable
continuation of its committed local witness. After the base certificate fixes
the challenge, it evaluates the canonical equations, requires exact divisibility
by every RNS modulus, and constructs its 384 bounded quotients. The real
production gate derived and completed custody for **4 owners × 384 equations**
from actual degree-4096 `fhe.rs` key/ciphertexts/openings; a
mutated ciphertext failed through the internally derived relation digest. The
production session constructor no longer accepts an arbitrary digest, and its
focused target is **5/5 in 6.507s**.

The final distributed BFV linear relation is now proved. A second challenge is
derived only after the complete quotient certificate. It collapses all **1,536**
exact rows; each worker proves one masked image of its committed base and
quotient shares in a four-owner, **65,536-coordinate** `LinearProof`. No worker
or coordinator reconstructs an order, encryption opening, or quotient vector.
The public coordinator requires all roster-signed proofs and checks that the
masked images plus the independently derived public constant sum to zero. The
real degree-4096 all-owner gate, including quotient custody, all three worker
proofs, and the final public certificate, is **1/1 in 91.204s**. A shared lazy
production generator table made this faster than the prior quotient-only
173.204s gate; the reduced success/adversarial relation tooth is **1/1 in
14.063s** and rejects bad signatures and a wrong public constant.

The complete public ceremony now has a strict canonical transport envelope.
`FHQCT001` quotient custody, standalone `FHRWP001` worker frames, the
`FHRLC001` final relation certificate, and a mandatory nonlinear root-link
certificate compose under `FHDBE002`. Exact component
lengths and EOF are checked before cryptography; roster/session and the complete
public BFV relation remain verifier-supplied; cheap digests, commitment sums,
and signatures precede every expensive proof; nested certificates are verified
exactly once. Hostile truncation/trailing/count/length, forged-signature, wrong-
relation, recomputed-checksum, and old-three-certificate downgrade mutations
refuse. The 6,663-byte root certificate proves the deployed Poseidon relation
and uses four signed owner-local links to the exact distributed input
commitments. The production book-A/B substitution attack refuses **1/1 in
190.133s**; the full BFV/root/wire gate is **1/1 in 190.926s**. Clearing
composition, exact sampler image, distributed replacement for the current
whole-book HidingFRI source viewer, and PQ replacement remain.

`private_book_bfv_exact` is the one public lowering shared by monolithic and
distributed backends. It internally derives the public key/ciphertext rows,
real 128-entry message table, transcript signs, negacyclic correlations, and
relation digest; no caller supplies public coefficient vectors. The monolithic
proof still runs its complete seeded 98,304-equation preflight after the
refactor. A real degree-4096 `fhe.rs` fixture evaluated all **384** owner-local
compressed equations, proved exact divisibility by each RNS modulus and the
1,130,496 quotient bound, and rejected degree 16. The focused release
differential was **1.051s**; the encoder **128/128** and native HidingFRI hostile
gates remained green.

### Exact test inventory

**fhegg-fhe/tests/private_book_relation.rs** currently contains:

- exact_bfv_rows_open_the_same_private_root_and_refuse_every_substitution
- metadata_slot_keeps_zero_quantity_side_and_limit_injective
- duplicate_bfv_randomness_is_refused_before_encryption
- packed_fold_consumes_the_exact_proof_rows_and_refuses_a_detached_shape
- authenticated_ingress_emits_the_exact_proof_ciphertext_not_a_second_encoding

**fhegg-fhe/tests/private_book_distributed_inputs.rs** currently contains:

- reused_rng_stream_is_session_separated_before_any_worker_sees_a_share
- every_semantic_option_row_is_exact_and_constraint_omissions_fail_closed
- all_local_openings_bind_one_public_certificate_without_reconstruction
- private_packet_equivocation_and_public_signature_forgery_fail_closed
- exact_production_layout_and_session_separation_are_pinned

The captured relation/distributed-input run was **8/8 green before later custody
hardening**. The current custody-hardened distributed-input target has now also
passed **5/5 release**, including the exhaustive 128-row semantic table and
deliberately malformed-but-well-shaped assignments for every load-bearing
selector/message/shortness constraint. HEAD has ten tests across the relation
and distributed-input targets; the captures cover the relation baseline and
the current five-test custody target without pretending they were one combined
invocation.

**fhegg-fhe/tests/private_book_distributed_prover.rs** contains:

- each_process_consumes_one_share_and_coordinator_sees_only_public_digests
- duplicate_missing_misbound_and_forged_worker_material_fail_closed

Captured result: **2/2 green**. This gates the process/custody envelope and its
fixture backend, not a real distributed Bulletproof/R1CS prover.

**fhegg-fhe/tests/private_book_canonical_backend.rs** exercises exact local
openings, rejection of arbitrary digests and cross-certificate reuse,
roster-signed corrupt-share proofs, and cross-worker/request/owner-order replay.
The canonical target passed **5/5 release in 0.359s**; the generic distributed
target passed **3/3 release in 0.236s** after the request-wire tooth was added.
With the selector/message/shortness layer, the three distributed targets passed
**13/13 release in 8.952s**. That run exercises the full production-width
73,856-gate owner proof, not only the reduced-degree fixture. Hostile cases
change canonical range and selector proof responses, recompute the artifact
checksum, and re-sign with the legitimate owner; verification still rejects
`OrderRangeProofRejected`. Valid selector proof bytes transplanted across
owners or ceremony requests also reject after checksum refresh and legitimate
re-signing. A forged owner signature rejects before any expensive proof
verification; the test-only verifier counter stays exactly zero.

### Exact residual before any no-single-viewer claim

A production distributed backend now carries these committed shares through the
exact fhe.rs polynomial/BFV equations and a mandatory Poseidon-root link. The
remaining no-single-viewer boundary is the nonlinear HidingFRI/root proof's
source process, which still receives the complete witness/openings, plus the
clearing relation itself. Those must become share-native and be consumed by the
actual apex before any no-single-viewer claim.
The system also still needs malicious share-formation and MPC-gate proofs,
production authenticated private-packet wire transport, DKG/key-domain
validation, and rollback/replay treatment. A colluding decryption threshold can
decrypt. Until those boundaries are closed and gated, “no single viewer” is
false for the deployed path.

## 8. Consequences in the game

### Atomic Bazaar settlement

The current private apex builds a real provenance-carrying Descent loot asset
and gives the winning buyer 3 DREGG. Its intended full path:

1. records the exact source-bound private receipt;
2. reconstructs the public-only verifier after replaying a pre-operation
   FileResumeStore;
3. invokes the same frontend-neutral fhEgg operation used by hosted adapters;
4. journals the operation result;
5. atomically transfers the exact Descent asset and 3 DREGG; and
6. refuses replay.

The implementation is in
**dreggnet-market/tests/private_clearing_apex_e2e.rs**:

- private_bfv_receipt_survives_restart_and_authorizes_the_real_bazaar_consequence

Captured current result: **1/1 full-stack sealed-v5 integration green in
167.054s nextest / 167.008s internal** under the full profile with verified
ML-KEM/ML-DSA authority cores required and no fallback. This is not an end-to-
end post-quantum result: the exact same-opening proof remains classical, and
the game consequence is one-host atomic rather than distributed atomic commit.

### Warden's Keep crown

**dreggnet-market/src/private_clearing_consequence.rs** defines a process-local
corroborated gate from a settled private-clearing receipt to one cap-bounded game
turn, with a derived replay ID and recovery observer.

**dreggnet-market/tests/private_clearing_crown_consequence.rs** contains:

- proven_bazaar_winner_claims_the_writeonce_keep_crown_exactly_once

The test targets the real Warden's Keep WriteOnce crown and includes hostile
target, root, turn, receipt, replay, and recovery cases. It uses the older Tier-1
private-clearing producer, which sees the order witness; the consequence gate is
process-local and is not the transferable BFV composite verifier. It is
**GATED: 1/1 green in the heavy release profile**. Only the pinned receipt may
authorize the crown; target/root/turn/receipt substitution, replay, and crash
splice cases refuse.

### fhIR raid allocation

The green optimizer/game consequence is separate from the private BFV apex.
**circuit-prove/tests/fhir_verified_raid_allocation.rs** verifies a canonical
FHQPB001 artifact, derives the certificate-selected one-hot roster assignment,
binds the exact objective and ordered roster into a witnessed cell claim, and
lets the ordinary executor mutate the actual relic-carrier slot only for that
assignment.

Its six exact tests are:

- exact_fhir_certificate_commits_the_certificate_selected_raid_assignment
- host_cannot_spend_a_valid_certificate_on_a_different_raid_assignment
- corrupted_or_different_program_certificates_cannot_authorize_the_outcome
- same_winner_with_a_different_objective_cannot_reuse_the_cell_claim
- objective_and_ordered_game_roster_are_part_of_the_cell_claim_and_vk
- approximate_tolerance_cannot_authorize_the_exact_game_allocation

Captured result: **6/6 green in release**.

## 9. Composed Dungeon, raid, Chutes, and Descent burn-down

Every path in this section is verified present at HEAD. Results are attached to
their exact targets only: these lanes are not promoted by the private-clearing
apex 1/1 or fhIR raid-allocation 6/6 results.

### Narrated Dungeon and relic-oath substrate — mixed

**dreggnet-offerings/tests/dungeon_narrated_operation.rs** exercises the typed
closed-command narrator boundary over the real hosted Dungeon. Prose is bound
into the receipt but is not state authority; stale-room, injection-shaped, and
world-exposure attempts are refusal teeth. Its exact three tests are:

- opt_in_narrated_turn_records_the_real_receipt_and_prose_is_not_power
- stale_wrong_room_and_injecting_proposals_are_anti_ghost_refusals
- narrator_view_tracks_the_hosted_session_without_exposing_the_world

**dungeon-on-dregg/tests/relic_oath_branch.rs** supplies the consequential
two-oath relic branch that later composition consumes. Its exact two tests are:

- the_sunblade_oath_refuses_the_crown_route_and_replays_to_mercy
- the_thorn_crown_oath_refuses_mercy_and_replays_to_a_cursed_tribute

Captured status:

- dungeon_narrated_operation — **3/3 GREEN**.
- relic_oath_branch — the prior 0/2 LinkageBroken run was repaired; the current
  target is **2/2 GREEN**.

### Private raid, party capability, Arena, and narrated relic — gated by target

**dungeon-on-dregg/tests/private_raid_atomic_forest.rs** is the lower-level
executor composition of a real HidingFRI raid-assignment receipt, proof sigil,
party role/focus cells, and a tactical Arena as one journaled forest. Its tests:

- real_proof_sigil_party_and_arena_commit_as_one_four_root_forest
- custom_vk_refuses_a_non_receipt_without_leaking_any_raid_prefix

Its own module comment keeps the boundary honest: the Party cells reproduce the
public executor semantics rather than importing the privately owned production
World, and executor-local atomicity is not distributed-consensus finality.

**dreggnet-surfaces/tests/private_raid.rs** is the broader hosted/player surface:
fhIR allocation or hiding assignment selects exact roster capabilities, the
party forms and spends them in a real Arena, operation and move timelines
restart, and web/chat encodings traverse the same flow. Its exact eight tests
are:

- fhir_optimum_selects_a_real_party_member_and_role_with_executor_and_replay_teeth
- fhir_member_role_allocation_survives_host_operation_and_move_replay
- hiding_assignment_authorizes_exact_capability_claims_and_a_real_arena_turn
- operation_and_moves_restart_exactly_while_roster_order_substitution_fails_closed
- catalog_lobby_forms_the_exact_roster_then_restarts_through_proof_and_capability_claim
- web_binary_and_chat_streaming_reach_one_join_proof_claim_burn_act_game
- chat_proof_stream_refuses_oversize_chunks_and_has_a_finite_turn_budget
- live_adapter_sources_keep_the_text_and_binary_routes_the_flow_requires

**dungeon-on-dregg/tests/relic_raid_narrated_forest.rs** is the new cross-lane
capstone: oath and guardian consequences precede one atomic two-root forest in
which the private raid proof materializes the exact Mender and a receipt-bound
narration awakens the relic. Its exact test is:

- relic_raid_allocation_and_narration_compose_in_one_receipt_chain_and_forest

Captured status:

- private_raid_atomic_forest — **2/2 GREEN** in one focused persvati invocation.
  That fixture uses `AuthRequired::None`; persvati lacked the verified ML-DSA
  archive, so the run explicitly set `DREGG_REQUIRE_LEAN=0` and
  `DREGG_ALLOW_UNAUDITED_PQ=1`. It qualifies the executor/HidingFRI/customVK/
  journal composition, not a strict PQ production runtime or distributed
  finality.
- dreggnet-surfaces private_raid — **8/8 GREEN** in one current feature-enabled
  invocation. The prior 310,767-byte proof replay failure is closed.
- relic_raid_narrated_forest — **1/1 GREEN**.

The already-green fhIR allocation checker and private-book apex remain separate
evidence.

### Durable game epochs and the first private-fhEgg game consequence

`dreggnet-catalog::GameEpochLedger` now owns a random host incarnation and a
monotone generation for each `(offering, session)`. Persistence is atomic and
fsynced; corruption fails closed; close/reopen advances the generation while an
exact process restart preserves incarnation, generation, state head, and valid
callbacks. The catalog gate is **4/4 green**. Production Telegram requires this
ledger plus its move-log store, encodes a 45-byte opaque digest of the complete
bound `GameActionRef`, and re-inspects the live bound view before execution. Its
hostile epoch gate is **2/2 green**. This is single-writer custody, not an
active/active lease system, and the other frontend adapters still need the same
migration.

The feature-gated private-fhEgg consequence accepts no caller-fabricated public
authority. It projects only from a verifier-minted native-PQ-quorum
`PrivateBfvLiveApexReceipt`, revalidates the atomic settlement audit, and binds
the exact verifier, claim/certificate/authority, root/session, roster,
settlement turn, sold asset, public winner/result, configured winner-to-game-key
route, epoch, action preimage, and current head. It then invokes the signed
common spine itself for one Warden's Keep raid-Mender recovery. The focused
release gate is **2/2 green**; the real HidingFRI raid path took **76.070s**,
landed HP **30→50**, survived durable restart, and refused wrong signer,
cross-incarnation substitution, and replay. Private order/opening/score/viewer
data never crosses this API.

The second mechanic consumes a private-field `FinalizedFaithfulSpend` minted
only after the FNSP-v2 note/nullifier/receipt/root transaction is durable. It
joins that one-shot tender redemption to the same exact private-BFV apex,
requiring the spend value to equal the clearing price and binding asset type,
federation, submitter, winner signer, Dungeon epoch/head/action, and either the
Red or Blue crown. The common signed spine lands the real Dungeon `WriteOnce`
claim; the rival crown, replay, wrong signer, missing/wrong tender, and receipt
mutation all refuse. The feature/check and policy teeth are green; the linked
verified Lean/PQ archive gate is **1/1 in 19.464s**. It accepts no raw proof or
caller-reconstructed attested root.

The faithful spend, Bazaar asset settlement, and later game turn are not one
distributed transaction. FNSP redemption is a one-shot payment, not a recipient
output proof. Deployments must durably record the authorization id after
success; the Keep/crown `WriteOnce` fields and host signed-counter journal
independently make the concrete action one-shot across the persistence window.
The existing
strict-v5 apex remains the full-stack authority evidence, but its newly authored
game block has not yet completed a fresh strict recapture: that attempt stopped
before market code at a concurrent distributed-BFV test-cfg compile error. The
production feature itself passed its release check.

### Chutes → Dungeon weld — pending

**discord-bot/tests/dungeon_chutes_weld.rs** uses the production
OpenAI-compatible client against a loopback server carrying the response shape
served by Chutes. The model proposes only a typed closed-channel Dungeon
command; the real Dungeon executor remains authority, narration is
receipt-bound, and refused/failed proposals must release player credit without
mutation. Its exact tests are:

- chutes_tool_call_resolves_as_one_real_dungeon_turn
- failed_or_refused_narration_releases_player_credit_and_never_mutates
- provider_schema_is_not_authority_wrong_room_and_injection_still_refuse

Status: **PENDING GATE**. This is an adapter/protocol test using a loopback
provider fixture, not evidence of an external Chutes service deployment.

### Lean-native Descent offering and campaign — gated

**dreggnet-offerings/tests/native_descent_offering.rs** checks the generic
Offering seam over Lean-authored native Descent, including the complete crowned
line, receipt replay/tamper refusal, actor binding, and anti-ghost affordances.
Its exact tests are:

- complete_crowned_run_banks_on_a_real_terminal_receipt
- public_record_resumes_by_reexecution_and_rejects_tampering
- affordances_follow_the_native_mover_and_refusals_are_anti_ghost

**dreggnet-offerings/tests/descent_campaign.rs** composes that native run with
the real region-cell campaign. Only a manually played crown may clear the Keep
and open travel; terminal-without-crown and hostile replay/substitution paths
must not mint campaign progress. Its exact tests are:

- crown_is_manually_played_and_is_the_only_region_unlock
- terminal_run_without_crown_cannot_mint_campaign_progress
- restart_and_hostile_substitutions_reexecute_exactly

Both targets are green inside the current **dreggnet-offerings 117/117** default
invocation. They remain distinct from the private-clearing apex, which transfers
a Descent loot asset, and from the fhIR raid-allocation target.

### Common session and frontend transport rail — gated with authority residuals

`dreggnet-catalog::game_spine` gives Dungeon, Descent, private raid, and Bazaar
operations one resumable descriptor/receipt shape. It binds the exact session,
actor, operation, payload, prior head, result, and successor head, rechecks the
operation descriptor/capability, and preflights replay material. The later
authority-bound route additionally carries a nonzero host/federation
incarnation and monotone session generation through action preimages and outer
receipts. Cross-incarnation replay, close/reopen generation rollback, and
receipt/session substitution refuse; same-incarnation restart replay remains
exact. The expanded hostile target is **21/21**. `dreggnet-telegram` carries the same game journeys, including
the canonical private-raid proof through Telegram's document/getFile path; its
combined current evidence is **77 tests**. The web session rail and reviewed
no-viewer projection are **2/2 + 2/2**.

These are coherent routing/presentation and replay boundaries, not actor
authentication. Current chat actor values are asserted, the presentation head
is not the canonical ledger root, and the consequence book is process-local.
Deployment custody and monotone allocation of the new incarnation/generation
values remain external; existing Telegram/web callers are explicitly
`LegacyUnbound` until migrated. Discord's direct binary path is being moved to
the same durable journal rather than promoted from its current in-memory/stamp-
only behavior.

### hbox and artifact custody — operational facts, not build evidence

Current hbox ground truth:

- Intel i9-12900, 24 hardware threads;
- 123 GiB RAM;
- AMD RX 6750 XT visible through Vulkan;
- no ROCm/HIP installation; and
- **86 GiB free** on the filesystem used for the work at the latest direct
  probe. Four inactive, reconstructible build-lane copies were removed; the
  current GPU lane, games deployment, private node, and service binaries were
  preserved.

The hbox required-authority-core apex gate above and the collective GPU fold
below are now successful
execution evidence. Keep ordinary Rust CPU gates on persvati for cache and
contention economy; hbox now has enough headroom for the GPU-specific gates it
is meant to run.

**fhegg-fhe/tests/collective_gpu_additive.rs**:

- collective_rows_fold_with_explicit_backend_and_feed_masked_threshold_boundary

Captured result: **1/1 GREEN** on the real RX 6750 XT. Both fold phases reported
GpuResident and matched the CPU byte-level oracle before feeding the
party-owned masked threshold boundary. The current implementation stack is
**wgpu/Vulkan**, not ROCm/HIP. This is a real retained collective additive fold,
not a claim that every BFV/MPC operation is GPU-resident.

The portable GPU frontier is now broader and exactly scoped:

- the hard correctness matrix is **8/8 core + 3/3 private**, covering 20
  deterministic parity shapes and 22 adversarial refusals for resident BFV
  folds, the degree-2048 TFHE torus negacyclic MAC, the degree-4096 three-prime
  BFV NTT, and the exact private-book signed-dot workload;
- the private-book relation's 196,608 signed dots cover 805,306,368 exact
  sign/add operations and run in 0.014s warm versus 0.683s CPU (**48.62×**), but
  the unchanged CPU verifier remains authoritative and the complete hostile
  production test is green;
- one-shot BFV upload/readback does not beat CPU through N=256 in the frozen
  hbox qualification; persistent residency wins at larger repeated shapes, so
  batching/residency—not magical dispatch—is the optimization contract; and
- the current Bulletproof fork now has a complete portable public-scalar
  verifier mega-MSM path as well as the extended-Edwards group-add tooth. Its
  adaptive Pippenger follow-up uses radix 16 below 2,048 terms and radix 128
  above it, with ordered dispatches and one readback, and passed the required-
  mode 17/256/1024/4096 matrix plus a real R1CS verification. Dalek independently
  recomputes the returned point. This remains a performance red: fixed radix-128
  at 4096 terms was **4.722s GPU vs 9.563ms dalek**; the final standalone
  adaptive qualification was **4.643s vs 9.827ms**. The backend therefore
  remains disabled by default. In every case this only accelerates the
  transitional classical Bulletproof proof; secret prover MSM stays on CPU
  because verifier Pippenger's window access pattern is not secret-safe.

The HidingFRI GPU path now retains LDE buffers device-to-device through salted
leaf construction and keeps every Merkle digest layer resident until the root
is complete. At depth 2048 it produced the exact CPU proof with six resident
blits; five Merkle commits materialized 77 opening layers in exactly five
whole-tree readback batches, and measured **0.717s GPU vs 3.081s CPU**. The FRI
transcript path now consumes 2,736 authentication digests without 21,888 tiny
allocations and retains byte-identical seeded proof output. The actual
BabyBear^4 extension fold is now exact on WGPU for Plonky3 arities 2/4/8 through
2^20; at that size it measured **14.060/6.789/6.043ms GPU** versus
**17.541/19.274/21.429ms CPU**. A minimal patch exposes the hardcoded Plonky3
fold strategy and checks against the pinned revision, but the current full PCS
has not applied it yet; full-proof GPU-fold parity remains the live gate. The TFHE path also has a portable
encrypted CMUX/external-product implementation with signed gadget decomposition
and an exact four-prime (~120-bit) RNS NTT. Portable WGSL performs exact
16-bit-split Montgomery arithmetic; the forced coefficient/NTT matrix through
N=4096 and a hostile base-log-31/two-level case passed **3/3**. At N=2048 the
warm medians were **2.401ms CPU / 4.160ms quadratic GPU / 2.721ms NTT GPU**; at
N=4096 exact NTT was **4.816ms GPU vs 10.052ms CPU**. The next exact rung keeps
two accumulators and a coefficient-domain standard BSK resident across one
dependent blind-rotation chain: native modulus switch, LUT/monomial rotation,
signed gadget decomposition, and four noisy GGSW selector steps use one command
submission and one final readback. The combined N=2048 strict hbox suite passed
**4/4** against an independent tfhe-rs oracle and decrypted semantic check;
warm GPU was **2.865ms vs 5.914ms CPU** (71.087ms cold). The next PBS-shaped
path continues in the same submission through exact degree-zero GLWE sample
extraction and a standard native-torus LWE key switch, with one final
post-key-switch LWE readback. The strict independent-tfhe-rs combined target
passed **5/5**. At N=2048, GLWE size 2, full 2048-coordinate extracted input,
and an 8-coordinate output, retained-context first execution was 57.652ms and
the warm GPU path was **4.673ms vs 5.763ms CPU**; the standalone warm median was
**6.474ms vs 13.377ms CPU**. A prepared plan owns the full envelope's actual
memory and addressing geometry: all 918 input-mask slots, a 57.38 MiB standard
BSK, the exact 2048→918 standard key switch with a 57.44 MiB KSK, and all 919
output coefficients. Its dense deployed gate now uses a real encrypted input
under a generated 918-bit LWE secret, a noisy GGSW for every BSK bit, and
rejection-samples until every modulus-switched mask rotation is nonzero. The
strict hbox target passed **1/1**; one-time plan/upload was **125.152ms**, first
dense execution **449.309ms**, and the three-sample warm median **421.617ms**
versus **1,493.795ms CPU**. All 919 outputs equal tfhe-rs; the far BSK slot is
load-bearing, host mutation cannot change the uploaded plan, and a 917-slot mask
is refused. The complete 1,836-dispatch command exceeds the deployed Vulkan
command/descriptor allocation, so the exact route submits at most 256 ordered
CMUX steps at a time while both accumulators, scratch, BSK, and KSK remain
device-resident and only the final LWE is read back. This is the honest linear
coefficient-domain baseline.

The transform-resident successor is now real: it precomputes all 918 noisy GGSW
selectors into four-prime NTT form and runs exact signed decomposition, forward
NTT, spectral product, inverse NTT, centered CRT, accumulator addition, sample
extraction, and the deployed key switch with one final readback. The strict real-
encrypted-input gate is **1/1** and all 919 coefficients match tfhe-rs; the warm
918-step path measured **115.746ms** against **422.847ms** coefficient GPU and
**1,380.391ms** CPU. The actual default high-level order has now been closed for
one selected radix block too: retain the `CompressedServerKey`, expand its exact
coefficient BSK/KSK, perform 2048→918 KS, centered-mean transform PBS, and
2049-coefficient big-key reconstruction, then return an ordinary `FheUint32`.
tfhe-rs decrypt parity and a subsequent normal high-level addition pass **1/1**.
On hbox, preparation took **317.965ms** and the first typed call against that
prepared plan took **143.891ms**; this is not a repeated-call median. The first
full-radix branch is now live as well: carry-clean `FheUint32 > public u32`
runs an encrypted radix-4 lexicographic state machine through all 16 blocks,
using exactly one deployed-order KS→transform-PBS per block, and returns an
ordinary encrypted 0/1 `FheUint32` that drives high-level `if_then_else`. Four
strict hbox cases match tfhe-rs, including encrypted `32768 + 32768 > 65535`;
preparation was **414.382ms** and full comparisons were **1.842–1.901s**. The
resident successor removes those host round trips: all radix LWEs/LUTs upload
once, the encrypted 0/1/2 state remains on-device through 64 ordered command
chunks with no intermediate waits, and only the result is read back. The same
late-decision case improved **1.891881s→0.741850s (2.55×)**; strict hbox is
**3/3** and dirty carries still refuse. Output is not native `FheBool`, and
ciphertext-to-ciphertext comparison/min/select plus broader shapes remain.

Lean arithmetic specifications for the BFV NTT and TFHE torus MAC are
axiom-clean; they specify arithmetic/refinement boundaries, not hardware
execution. `Dregg2.Circuit.TfhePbsRefinement` now additionally fixes the exact
native-torus GLWE/LWE semantics, degree-zero extraction signs, subtractive key
switch, fail-closed shape, and narrow plus 918×918 production coefficient
geometry. Its composed WGPU theorem requires an explicit external
implementation-equality premise; WGSL buffers, limbs, and dispatch are not
silently declared verified. Frozen details live in `FHEGG-WGPU-VALIDATION-MATRIX.md`,
`HBOX-WGPU-QUALIFICATION-2026-07-21.md`, and
`BULLETPROOFS-MSM-DISPATCH-INVENTORY.md`.

No build, verified artifact, or gate is promoted merely from custody activity.
The PQ lane supplied the apex-required verified ML-KEM/ML-DSA authority cores;
the separate credential-polarity ABI tooth and static archive audit are the
evidence that closed the handler/initializer residual.

### Wide post-quantum binding and the live shielded boundary

Two narrower-but-load-bearing replacements now exist:

- `metatheory/Market/PrivateBookBfvBindingAir.lean` checks the fixed private-book
  relation as **98,304 exact BFV equations** at the Lean model boundary.
- `metatheory/Dregg2/Shielded/WideNativePqCommitment.lean` commits the native
  shielded statement through **16 canonical BabyBear lanes**, rather than one
  field that aliases `x` with `x + p`.

The model boundary now has its first executable native-field member.
`Market.PrivateBookBfvSliceDescriptor` proves one complete 4,096-term
negacyclic equation—order 0, ciphertext polynomial 0, RNS modulus 0,
coefficient 0—together with the same hidden Dark Bazaar order/root relation and
an eight-lane commitment to all 4,096 ordered public-key coefficients. It is
not a random scalar projection. The real `fhe.rs` message-table differential is
**128/128 green**; the real HidingFRI proof/serialization/verification hostile
gate is **1/1 green in 22.414s** and rejects wrong key, ciphertext, and private
root. The checked 394,129-byte artifact has SHA-256
`459fa946690540ef0142c5feba0f8d03c1ace116ec3e42bca3c9b6b6a7b8526f`.
The first slice is not accepted as a complete BFV opening or a replacement for
the classical apex, but the scaling plan is no longer 98,303 unrelated copies.
`Market.PrivateBookBfvNttFamily` formalizes odd forward/inverse NTT semantics,
functional public-key certification, spectral-stage composition, and the bridge
back to the existing exact coefficient opening. Twelve shared `u` transforms,
98,304 pointwise rows, 24 inverse transforms, and 49,152 dual terminal rows make
**1,032,192 live rows**, padded once to **2^20 × 48**—a 384× reduction from the
literal padded-row family. The reusable dynamic public-key certificate is
147,456 live rows, padded to **2^18**. All eight coefficients across production
q0/q1 execute with mutation refusal, and the Lean root is green. The Rust/WGSL
path now also exposes standalone scheduled odd forward/inverse transforms, pins
all three deployed spectra to Lean's exact roots (including q2, where generic
root search previously selected a different valid but witness-incompatible
root), streams the six exact butterfly residues without allocating the full
matrix, and decodes every physical row of the `2^20 × 48` family. The fail-closed
hbox tooth is **1/1 green in 0.163s** on the RX 6750 XT/Vulkan and compares every
forward/inverse q0/q1/q2 residue with CPU; root/stage/modulus/input/output
mutations refuse. The first concrete 48-column butterfly AIR slice is now green
too: exact radix-2^14 product/add/sub carry chains, canonical q0/N8 witness,
schedule selectors, and an exact cross-stage `List.Perm` bus reject arithmetic,
schedule, bus, and omitted-row mutations; eleven keystones are kernel-clean.
This is not yet the full production prover: twist/bit-reversal ingress,
inverse normalization, terminal quotient rows,
recursive key-certificate join, and production `OddNttRefines` remain. The
formal faithful-table condition has since landed: each boundary table is an
exact permutation of both preceding writes and following reads, generically
instantiated at N=4096/logN=12, and duplicate schedule/bus rows that pass the
old membership-only AIR now refuse. The remaining table seam is deployment:
Rust IR2 must carry the corresponding committed multiset/grand-product evidence.

An experimental additive PQ-share commitment also exists in Rust and Lean. It
binds context and slot, commits exact BabyBear-coordinate shares with randomized
hiding coordinates, verifies additive links, and extracts a short nonzero SIS
kernel vector from a false exact link. The KAT and focused tests are green, but
the dimensions have not been estimator-approved and the live Ristretto scalar
shares are wide/uniform rather than bounded BabyBear coordinates. Production is
therefore programmatically refused (`productionPqReady = false`); this is an
algebra/encoding rung, not a type-only replacement for the classical commitment.

The Rust `ShieldedInputPayload` now carries a mandatory 16-lane wide value
binding plus its hiding proof. The effect hash binds every lane, and executor
admission verifies both the existing spend/conservation evidence and the wide
proof before absorbing those lanes into the conservation transcript. Focused
gates are **7/7 Turn shielded** and **4/4 circuit wire/alias**.

The faithful note-tree substrate now exists beside that value binding.
`Dregg2.Circuit.CommitmentTreeWide` proves that the exact 32-byte → sixteen-u16
codec has a left inverse and is injective, defines the KAT-real domain-separated
eight-lane Poseidon2 leaf/node/root and fail-closed 4-ary membership semantics,
and pins Lean-computed protocol vectors. The Rust tree and persistence wrapper
match those vectors **8/8**, `dregg-commit` is **141/141**, and the focused
persistence recovery/hostile target is **6/6**. The legacy and faithful trees
advance together during the transition. A strict authenticated history now
also binds exact session/federation/epoch, predecessor/successor faithful roots,
height, note count, and block id; hybrid Ed25519-and-ML-DSA verification plus
restart/replay/fork/truncation teeth are **6/6**.

The live finalization path now reconstructs all nested `NoteCreate` leaves,
advances the faithful tree, plans and hybrid-signs the exact successor edge, and
commits the finalized record/indexes, receipt, leaves, authenticated history
edge, exact eight-felt `StoredAttestedRoot`, and cursors in one redb
transaction. The node signs/publishes only after that transaction succeeds;
restart rebuilds the depth-16 tree and replays the authenticated history.
Forks, truncations, mismatched roots, unauthenticated records, and legacy scalar
aliases fail closed. The spend-side custody cut now adds a strict versioned
`FNSP` carrier for a bounded proof and historical `u64` height, replays the
hybrid-authenticated root history, and requires the exact `(height, root8)`
pair. Finalized commit, note leaves, exact `(nullifier, value, sequence)`
records, receipt, faithful history, attested roots, and cursors share one redb
transaction; duplicate/replayed nullifiers and wrong successor roots fail
before mutation, and restart seeds the executor from the durable records. Lean
proves refusal is state identity and success publishes exactly the persisted
successor root.

The faithful `NoteSpend` proof is now composed and live (`6cd2ddca2`). The
Lean-authored `faithful-note-spend-v2` relation uses the complete 16-lane
Poseidon2 bus and checks exact FNO2 spending-key-to-owner-address, FNC2 note
commitment, faithful depth-16 membership, and FNF2 nullifier derivation. Owner
address, spending key, nonce, randomness, leaf, position, and Merkle path remain
hidden; height, historical root8, nullifier, value, asset, and successor root8
are public. The 96,535-byte checked artifact has 1,623 main columns, 44 public
inputs, 393 constraints, and four tables. Its real HidingFRI hostile gate is
**1/1 green** (0.76s after build), and the production executor installs the
strict verifier without a legacy/non-hiding fallback.

This is still not the final PQ no-mint theorem. The circuit binds the planned
successor root but does not recompute accumulator insertion in AIR; the
deployed nullifier root still folds the nullifier to one felt, and value/asset
are public. The authoritative conservation proof remains
Ristretto/Pedersen/Bulletproof-based. Solo-mode already-applied finalization,
committee rollover, and O(all-leaves) recovery also remain.

The wallet no longer asks the node for a target note, position, membership
quote, or nullifier context (`5f0999ab9`). Its only supported mirror request is
a deny-unknown three-cursor record; the node returns fixed pages of 256 note
commitments, 16 hybrid-authenticated FNHR edges, and 256 public nullifier rows.
The SDK pins the mirror head and FNHR authority, reconstructs both accumulators
locally, and creates the membership, nullifier, successor, and HidingFRI proof
without disclosing which note it owns. Focused SDK tests are **7/7**, the node
request-shape tooth is **1/1**, and the node library check is green. The audit
follow-up is now **8/8 SDK + 2/2 node cache**: one immutable exact-head snapshot
reconstructs the note root from the durable commitment bytes, authenticates the
history/attestation/nullifier image, signs FNMS once, and serves every fixed
page without repeated full-chain or ML-DSA work. This closes
target lookup before proof construction, not submission anonymity: the public
FNSP turn still exposes nullifier/value/asset and can be correlated with the
receiver/IP absent a relay, mix, or oblivious ingress. The current head is a
threshold-1 pinned-node statement rather than federation finality/freshness.
The cache retains one O(chain-state) snapshot; privileged raw DB mutation after
publish is not observed until restart or an authenticated head change.

The exact successor design now covers the complete nullifier domain
(`3e313161e`). Lean uses tagged `BOT | REAL raw256 | TOP` leaves rather than
stealing raw all-zero/all-FF values as sentinels, proves bracketed sorted
insertion and duplicate refusal, and binds append-order physical update, two
depth-16 arity-4 root rewrites, authenticated indices, and the full 33-bit
terminal count. The FNSP-v3 descriptor plan is 2,442 columns × 16 rows with 76
public inputs; targeted builds and full `lake build Dregg2` (9,918 jobs) are
green. The rotated-state weld is also Lean-green at 3,760 columns/76 PI:
`FNS3(root8,count4)` replaces the old nullifier group, wide before/after commits
replace caller checkpoints, all 179 input cells are carried, and the other 171
output cells are preserved. The exact Rust twin is focused **7/7** with Lean
hash KATs, O(depth) sparse insertion, two authenticated paths, transactional
refusal, and strict durable-sequence replay. It is not yet a checked live
artifact: the current accumulator is still sorted-dense FNL8/FNN8. The node now
prepares and independently applies each finalized transition, including a
multi-spend batch whose adjacent FNS3 anchors and persistence sequences must
chain exactly (**3/3 hbox**). The canonical staged descriptor is emitted at
**431,214 bytes, width 3,760, 76 PI, 1,258 constraints**, SHA-256
`dac87d07f12ec01cc32e34ec131db0786244b2492d5bc153f90bbf062e577b6e`.
The repaired compiler-mode refinement target and full **9,922-job** Dregg2 build
are green. A genuine 16-row/200-constraint `Satisfied2` witness now covers
`BOT < REAL(ff..ff) < TOP`, count 1→2, append slot/base-4 quotient, both 16-limb
lex gadgets, bit/radix/count/depth continuity, and 64 real range-table lookups;
the remaining witness residual is hash/path/FNS3/rotated-wide composition, not
basic arithmetic/range. The descriptor is intentionally unregistered with no VK. Cutover still must call
the batch preparation from finalization, retain/fill the full witness and table
envelope, rotate the VK/registry, and retire the old root atomically.

### Cell-owned PQ identity and rotation

`Cell` now commits an ML-DSA-65 public-key commitment plus a dedicated monotone
key epoch. `CreateHybridCell` is sponsor-mediated but requires epoch-zero
new-key possession; `RotatePqIdentity` must be authorized by the current hybrid
identity and separately proves possession by the next key. The canonical cell
commitment and all faithful authority-digest lanes move on install/rotation,
the journal restores the exact prior anchor on failure, restart preserves it,
and SignedTurn admission treats the carried ML-DSA bytes only as an opening of
the live committed anchor. A host registry exists only as an independently
configured pre-v10 migration bridge and never learns from the envelope.

Exact gates: create/rotate/hostile later-effect rollback **1/1**; node restart
**1/1**; enrollment/no-TOFU/substitution **3/3**; hostile SignedTurn validator
**4/4**; cell identity/commitment/wire **3/3**; Rust registry **3/3 + 1/1** and
Lean registry green. Both proof producer and verifier projection explicitly
refuse these effects **3/3** because the PQ-authority row is not yet composed
with its outer cryptographic boundary; they are committed classical-runtime
transitions, never a silent `NoOp`. The Lean-authored rotation descriptor now
exists and is gated: it losslessly carries every 32-byte object as sixteen
canonical u16 limbs, every epoch as four limbs, and proves exact target/
expected-epoch continuity, overflow-free +1, and key change over a 127-column,
108-public-input row. ML-DSA authorization and new-key possession remain
explicit outer predicates, not a prover-chosen verified bit.
Pre-v10 postcard snapshots need a store migration, and unknown agents cannot
self-admit their first outer SignedTurn without a sponsor.

## 10. What the fhIR optimizer proof does and does not say

The optimizer is an untrusted finder. Acceptance authority is the exact
certificate/checker path:

- `fhir/src/optimizer_protocol.rs` now makes the out-of-process worker boundary
  hostile by construction: the complete problem digest, solver manifest,
  session, nonce, certificate bytes, length, exact EOF, checksum, and replay id
  are bound before the existing checker and Cert-F authority are invoked. The
  focused protocol/checker target is **69/69 green**. A worker returning a valid
  certificate for a different problem, session, or solver context has supplied
  no authority.

- Market.SddPsd proves that an arbitrary finite rational SDD matrix with
  nonnegative diagonal is PSD. The exact checker constructs and verifies that
  witness. SDD is sufficient, not complete: the module includes a PSD rank-one
  matrix outside SDD.
- Rust ExactSddPsdCertificate is embedded in the compiled QP, rechecked at
  consumption, and bound bit-exactly to the backend's P matrix. Its strict wire
  family is FHSDD001.
- FHQPB001 joins the PSD admission with an exact KKT certificate and binds the
  complete public fixed-point problem (P,q,A,l,u).
- Exact-zero KKT plus the same admitted matrix proves global optimality for the
  bound convex QP. Market.QpExternalProgramBinding prevents reuse under a
  changed public field, including the dangerous same-P, different-q case.
- A positive tolerance is not exact optimality.
  Market.QpApproximateBound proves a quantitative objective-loss/feasibility
  bound only from the stated residual and displacement/radius assumptions. Rust
  connects its reported maximum residual coordinate-by-coordinate.
- The raid mechanic deliberately requires the zero-tolerance capability and a
  one-hot certified assignment. A valid positive-tolerance artifact cannot
  authorize the exact game allocation.

Residuals:

- source f64 to exact fixed-point scale refinement is not generally proved;
- a product using the positive-tolerance theorem must supply its own valid
  feasible-set radius or L1-displacement bound;
- SDD rejects some PSD matrices;
- wire checksums detect corruption but are not authentication;
- the broader fhIR Rust grammar is not wholly refined into Lean;
- the fixed clearing/raid claims are narrower than “the optimizer is proved.”

**metatheory/Market/FhIRRaidAllocationBinding.lean** is the game-facing
composition law. It binds the exact QP, ordered roster, one-copy assignment,
selected seat and actor, and recomputed objective. It proves feasibility and
global optimality through an explicit backend extraction premise and refuses
roster, P, q, reported-objective, and selected-actor substitutions. Direct gate:
**7 clean**.

## 11. Lean authority ledger

The aggregate command lake build Market is green at **8747 jobs** after adding
the live-host and optimizer/game modules. The immediately relevant direct gates
are:

- Market/DarkBazaarPrivateIngressCutover.lean — **11 clean**
- Market/DarkBazaarLiveApexHost.lean — **16 clean**
- Market/FhIRRaidAllocationBinding.lean — **7 clean**

Additional imported authority includes:

- Dregg2/Shielded/WideNativePqCommitment.lean — canonical 16-lane native PQ
  commitment and anti-aliasing laws;
- Market/PrivateBookBfvBindingAir.lean — exact fixed-shape BFV binding equations
  and extraction boundary;
- Market/PrivateBookEncryptionBinding.lean — exact opening law and detached
  encoding counterexample;
- Market/PartyMpcTransportBoundary.lean — authenticated transport does not
  imply arithmetic honesty;
- Market/SddPsd.lean — exact SDD-to-PSD theorem and incomplete-cone
  counterexample;
- Market/QpCertificateBundle.lean — same-matrix exact KKT composition;
- Market/QpExternalProgramBinding.lean — complete public-program binding; and
- Market/QpApproximateBound.lean — bounded-residual quantitative result, not
  exact optimality.

These modules make the missing premises visible. They do not prove the
Bulletproof implementation, BFV/DKG security, PartyMPC malicious security,
canonical wire decoding, GPU execution, or the complete Rust-to-Lean refinement
from first principles.

## 12. Exact captured verification ledger

### Green

- private_book_bfv_zk — **2/2 release green**; hostile proof test **65.765s**.
- private_bfv_attested_clearing — **1/1 release green**; **62.958s**.
- then-current private_book_relation + private_book_distributed_inputs —
  **8/8 green before later hardening**.
- custody-and-shortness-hardened private_book_distributed_inputs — **5/5
  release green**, including all 128 valid semantic rows and explicit omitted-
  constraint witnesses.
- private_book_distributed_prover — generic request/envelope **3/3 release
  green**; canonical committed-share backend **5/5 release green** with four
  opening PoKs and three share-native linear constraints per worker; owner
  range/selector/message/shortness/link layer brings the combined distributed
  targets to **13/13 release green in 8.952s**, including the production-width
  73,856-gate proof. Exact fhe.rs polynomial opening, Poseidon, clearing, and
  live apex proof generation remain monolithic.
- fhegg_private_verifier_registry — **2/2 green**.
- party_mpc_crossing_transport — **2/2 release green**, **1.099s**.
- native PartyMPC PQ transport — **5/5 integration + 5/5 units green**;
  explicit unaudited test backend, so transcript/control-flow evidence only.
- sealed native-PQ PartyMPC crossing — small full crossing/token/barrier hostile
  **1/1**, route asymmetry + coordinator-key-alias **2/2**, strict claim-source
  **1/1**, typed-apex structural build green, and strict full apex **1/1**.
- native clearing quorum — **1/1 hostile native + 6/6 classical compatibility
  green**; the native authority transcript covers the complete canonical claim.
- private_clearing_apex_e2e — **1/1 strict v5 full-stack integration green**,
  **167.054s nextest / 167.008s internal**, including 85.923s classical proof
  and 7.956s sealed crossing; DREGG_REQUIRE_LEAN=1 and
  DREGG_REQUIRE_PQ_CORES=1, unaudited fallback unset. This requires the real
  ML-KEM/ML-DSA cores, not end-to-end PQ.
- accelerated fixed-N private-book relation — **1/1 hostile green in 64.631s**;
  proof **23.445s**, honest verify **8.213s**, exact 131,073-term commitment MSM
  **1.226s serial / 0.396s parallel**. Same proof/verifier; full strict-apex
  timing not yet recaptured.
- fhir_verified_raid_allocation — **6/6 release green**.
- hostile external fhIR optimizer protocol — **69/69 fhir + 118/118
  fhegg-solver green**; streamed problem binding is zero-allocation at the
  comparison boundary; exact KKT `Ax` revalidation is also zero-allocation and
  preserves hostile lift-error/overflow precedence. The typed exact-zero view
  borrows the bundle-owned certificate, eliminating the 2,117,632-byte dense
  clone measured at n=256.
- private_clearing_crown_consequence — **1/1 heavy-release green**.
- shielded crown orchestration — **3/3 feature + 4/4 durable journal green**;
  apex-use, finalized-spend-use, and composed action are atomically reserved
  before dispatch, with corrupt/missing restart state failing closed.
- Telegram shielded-crown controller — **4/4 hbox green**; public-only command
  re-derives the game action and loads typed custody, but long-poll mounting and
  durable apex retention remain.
- dungeon_narrated_operation — **3/3 green**.
- relic_oath_branch — repaired target **2/2 green**.
- relic_raid_narrated_forest — **1/1 green**.
- dreggnet-surfaces private_raid — **8/8 green** in one current feature-enabled
  invocation.
- dreggnet-offerings — **117/117 green**, including native Descent/campaign and
  typed private-game consequences.
- incarnation-bound common game spine — **21/21 green**; Telegram combined journey **77 tests**;
  web session/no-viewer rails **2/2 + 2/2**.
- collective_gpu_additive — **1/1 green** on the real RX 6750 XT with
  GpuResident via wgpu/Vulkan.
- portable HidingFRI GPU — **2/2 exact parity green**, with the depth-2048 path
  measuring **0.717s GPU vs 3.081s CPU**, retaining six device blits, and
  reducing five Merkle trees to five whole-tree readback batches; standalone
  ext4 fold is **2/2** through arities 2/4/8 and 2^20, with the full PCS hook
  still pending application.
- portable Ristretto verifier MSM — exact adaptive radix-16/radix-128 required-
  mode matrix **1/1 green** with dalek authority through 4096 terms; the final
  standalone 4096-term qualification is 4.643s GPU versus 9.827ms dalek and
  therefore disabled by default.
- portable TFHE encrypted PBS — exact coefficient/RNS-NTT and
  four-selector device-resident blind rotation combined strict GPU **4/4**,
  exact extraction/key-switch combined strict GPU **5/5**, and the genuine
  dense 918-CMUX reverse-order qualification envelope **1/1**; all 919 outputs match tfhe-rs and
  transform-resident warm GPU was **115.746ms** versus **422.847ms** coefficient
  GPU and **1,380.391ms CPU**. The actual default-order one-block
  KS→transform-PBS→big-key `FheUint32` adapter is also **1/1**, including a
  following high-level op; full 16-block `> public u32` is **1/1** across four
  semantics at 1.842–1.901s/comparison and drives encrypted `if_then_else`.
- wide shielded binding — **7/7 Turn + 4/4 circuit wire/alias green**; the old
  note/root and classical conservation leg remain.
- native exact-BFV HidingFRI slice — exact 4,096-term coefficient equation plus
  the same hidden order/root relation **1/1 green in 22.414s**; real encoder
  table **128/128**; the full 98,304-equation odd-NTT family is now formalized as
  one 2^20×48 schedule; exact q0/q1/q2 scheduled WGPU forward/inverse parity is
  **1/1 green in 0.163s** on hbox and all 1,048,576 rows decode/recompose, while
  butterfly AIR/full witness bus/terminal quotient/recursive join remain open.
- faithful wide note tree/history — Lean authority green, Rust correspondence
  **8/8**, dregg-commit **141/141**, tree persistence **6/6**, authenticated
  history **6/6**; live finalized `NoteCreate` leaves, history edge, exact
  eight-felt attestation, receipt, and cursors commit atomically. Historical
  `(height,root8)` admission and exact nullifier/value/sequence plus successor
  persistence are atomic. The new faithful IR2 relation and strict production
  verifier produce/verify a real HidingFRI proof **1/1** while hiding owner,
  key, nonce, randomness, leaf, position, and path; accumulator insertion is
  still host-computed and public value/asset are an explicit boundary.
- cell-owned PQ identity — create/rotate/rollback **1/1**, restart **1/1**,
  enrollment/substitution **3/3**, SignedTurn hostile **4/4**, cell wire/
  commitment **3/3**, EffectVM fail-closed refusal **3/3**; Lean-authored
  rotation authority row and Rust parser canary green, outer ML-DSA composition
  still absent.
- lake build Market — **8745 jobs green** before the final live-host/optimizer
  additions, then **8747 jobs green** afterward.
- direct Lean: private ingress **11 clean**, live apex host **16 clean**, fhIR
  raid allocation **7 clean**.

### Not green

- any earlier full-apex result that omitted the target because its manifest
  feature was absent — **not evidence**.
- No remaining handler-cutover archive residual: the exact strict ABI tooth and
  static symbol/U-minus-D audit are green. This does not alter the separate PQ
  identity-binding residual.

### Superseded or non-gate captures

- The earlier apex 1/1 in 63.951s with DREGG_ALLOW_UNAUDITED_PQ=1 remains useful
  semantic history but is superseded by the required-authority-core full-profile
  gate.
- The first current-source hbox invocation built Lean material but selected
  **0 tests** under the default profile because the heavy apex was excluded. It
  is not a test green.
- The prior relic-oath 0/2 LinkageBroken run and private-raid 7/8 chat replay red
  are repair history; their replacement focused gates are green.

### Pending composed-game gates

- dungeon_chutes_weld — 3 tests present; result pending.

## 13. Executable closure gates

These are the next truth-producing gates:

1. Capture the still-pending Discord Chutes→Dungeon target in section 9; do
   not inherit a green from its Dungeon/narrator organs.
2. Replace the remaining whole-book HidingFRI source viewer with a share-native
   nonlinear prover and compose the clearing relation into FHDBE002. Exact BFV
   and the Poseidon root link are now mandatory; clearing, sampler image, and
   distributed/PQ nonlinear proof generation remain before no-single-viewer.
3. Replace FHTRI004's centralized candidate/MAC/beacon setup with a distributed,
   jointly unpredictable ceremony, add durable compare-and-set consumption for
   protected rows, and prove private-input share formation. The live sacrifice
   and response authentication are now composed, but authority-signed setup
   alone still cannot satisfy `LiveMpcBackend.sound`.
4. Register/rotate the emitted exact tagged FNSP-v3 descriptor and VK, call the
   staged multi-spend AAFI batch from finalization, fill/retain its full witness
   and table envelope, then compose conservation authority and retire the old
   root atomically. Separately compose the PQ-identity AIR row with both outer
   ML-DSA predicates before removing either proof-path refusal.

Heavy Rust proof gates belong in the release-only nextest heavy profile and on
the build node. Lean stays local with the warm metatheory/.lake cache.

## 14. 2026-07-22 checkpoint correction: what is banked, and what is live

The older “unbanked lanes” wording in this handoff is superseded by the
following commits:

- `a8ea35b8d` banks the canonical executable exact-FNSP relation envelope.  The
  validated fixed-record typed descriptor plus code-owned relation version,
  manifest, ordered ABI, AIR fingerprint, and backend identity are executed and
  checked.  Lean-emitted JSON remains parser/build provenance, not semantic
  protocol identity.
- `4ec3896a0` + `817c6a6d9` bank the collaborative Shamir-row handoff.  It has
  receiver/owner/frozen-round authenticated encryption, custody assignments,
  zeroization, and receiver-local fold transcripts; malicious polynomial
  consistency, live key establishment/replay storage, and a PQ share-native PCS
  remain open.
- `f0fa44145` banks the CAS-last dual faithful/exact persistence transaction;
  `98a66d1d3` banks immutable-prefix historical replay after later appends.
- `4b5a19522` banks an honest **WIP** exact receipt-epoch and executor-authority
  scaffold.  It is not registered live.  The key correction is that the exact
  proof's stable-frame `FNS3` subtransition cannot equal a real receipt's full
  post-state after nonce/fee/other effects.  The live cut needs an owned exact
  subreceipt joined to a genuine executor-produced full-turn authority, an
  authorized epoch/head CAS, frame signature/quorum, and finalizer revalidation.
- `24fcd81bf` banks the private Bazaar player journey as WIP and `5c80e447d`
  checkpoints the shared game/frontend surfaces.  Remaining P0/P1 work is a
  deployment-owned roster/reward policy, durable global exactly-once
  consequence/outbox identity, opaque exact-effect authority, prepare-before-
  dispatch recovery, full market identity, and real hosted web/Discord/Telegram
  mounting.  Fixture-only publication is not a deployment claim.

The current policy is intentionally simple: useful in-progress substrate is
committed and labelled WIP; genuinely superseded code is deleted once its typed
replacement lands.  A WIP commit is continuity, not protocol endorsement.
