# GOAL — make the corpus RUN FOR REAL on the living federation (and know WHY)

(nextop's standing goal — distinct from GOAL.md which is Alif's STORAGE-IN-LEAN goal; don't clobber that.)

## North star
A real agent (confined + attested) executing real turns that stream-finalize, cross-node,
on a real dregg federation — VERIFIED, not marshal — every claim empirically demonstrated,
not modeled. Turn "assembled from real parts" into an actually-running machine.

## Live state (2026-07-06 night)
- ember's n=4 federation LIVE on hbox(192.168.50.39) + nextop(192.168.50.130), streaming,
  marshal-only (`full_turn_proving=false`), idle at height 22 (advances per turn).
  DREGG_NODE_URL = http://192.168.50.39:8420. Left running.
- Fleet is federation-capable (NodeTarget::Local | Federation, `--features http`, DREGG_NODE_URL
  + DREGG_NODE_BEARER). commit 313d42712.
- n=3 plateaus; n=4 streams. Root-cause IN FLIGHT (lane a6137a773): the block finalizes but the
  TURN is rejected at execute_finalized_turn — chasing the exact reject reason + fundamental-vs-
  real-bug verdict.

## Current thrust
Depth-crown the living federation: get a real flagship's ATTESTED turn to stream-finalize
cross-node (solve submit-auth: passphrase+bearer). Marshal now; verified next.

## Next 3 moves
1. [firing] Depth-crown on marshal n=4: passphrase → fleet bearer → a flagship attested turn
   finalizes cross-node, receipt on both machines, attestation verifies. (unit #3)
2. VERIFIED upgrade: cut the HEAD-matching Lean seed (warm cache on nextop) → rebuild both nodes
   verified → restart n=4 verified (`full_turn_proving=true`) → verified streaming finality.
   (unit #2; also produces the seed artifact David's homelab needs.)
3. Finish n=3 root-cause (lane in flight) → surface the fix if it's a real bug (don't fire
   consensus changes unsupervised). (unit #1)

## Done-log
- (pending)

## Done-log / findings (07-07)
- AUTH SOLVED (#3): node `/turn/submit` gates on a bearer token (POST /cipherclerk/unlock
  mints it; random salt so not passphrase-derivable). Proven: no-token 401 / wrong 401 /
  correct 200. Fleet already sends it (HttpNode::with_bearer). Token capture required.
- ⚠ REAL WALL behind auth (#3, consensus-layer, NOT faked): on a fresh-genesis n=4 marshal
  mesh, HTTP-submitted turns commit ONLY to the entry node's local cipherclerk receipt chain —
  they do NOT inject into the blocklace DAG, block_height stays 0 since genesis (despite 258
  DAG blocks + live tau), execute_finalized_turn never fires. The lane REFUSED to run paper_fund
  to a fake green (landed() checks node0's local receipt → would look like the payoff while
  height=0). Reframes the earlier "n=4 streams to 22" — that was likely internal operator turns,
  not submitted ones. THIS is the genuine blocker to the payoff. Overlaps the n=3 lane (finality).
- ⚠ VERIFIED-QUIC (#2 blocker): nextop's verified (Lean-linked) node's BLOCKING executor STARVES
  the async QUIC/gossip runtime (every dial times out — raw UDP works, so it's the binary, not
  the net). The A1/blocking-FFI class again. The verified upgrade needs the executor OFF the async
  worker (spawn_blocking) to gossip. Consensus/kernel — ember's call.
- IN FLIGHT: n=3 root-cause (a6137a773, the finality-gate verdict), seed cut (a285968e4, #2 prereq),
  real Nemotron (a4829f241, build-lock queued).
- NEXT: synthesize n=3 + depth-crown findings → the coherent "why don't submitted turns finalize
  on the live mesh" root cause + fix design → surface to ember/consensus-owners (do NOT fire a
  consensus change). The two make-it-real units (#2,#3) are consensus-blocked pending this.

## Submit-path diagnosis (4a0623cdd) — the payoff blocker, precisely
- VERDICT: DESIGN GAP (not a broken wire). blocklace.submit_turn injection IS present+correct
  (api.rs:3147/3407/6938; cadence drains staged→round blocks blocklace_sync.rs:3439). Client
  turns are stopped UPSTREAM by how the handlers author+gate them:
  * POST /turn/submit — confused-deputy hardening (api.rs:2891) discards the body `agent`,
    rewrites to the node's OWN operator cell (exists only on clean-boot genesis; absent on
    joiners → `cell not found`). = the depth-crown's 4fc1e09c wall.
  * POST /turns/submit (caller-signed) — DOES inject to blocklace, but requires the client cell
    to pre-exist (no actor-provisioning) + gates on the node operator's cclerk chain (serializes
    all clients through one node-owned chain). = the node0 local-receipt observation.
  * /api/faucet works cross-node only because its actor is the genesis-provisioned faucet cell.
  * Root: execute_finalized_turn provisions only Transfer DESTINATIONS, never the turn's ACTOR.
- FIX DESIGN (grounded, NOT fired — ember/consensus-owner's call): (1) make /turns/submit THE
  external client path, decouple its receipt gate from the operator cclerk (optimistic ack;
  finalization authoritative, faucet scratch-clone pattern); (2) provision the actor cell at
  finalization deterministically from SignedTurn.signer (derive_raw(signer,"default"), zero-stub
  if absent — safe: signer in-block + sig-verified → identical stub every node, same uniformity
  as transfer-dest provisioning); (3) keep /turn/submit operator-only.
- THE PAYOFF NEEDS BOTH: submit-path (turn INTO the DAG) + n=3 finality-gate (DAG turns actually
  super-ratify+execute cross-node). Sequential gates on one pipeline.

## n=3 finality-gate VERDICT (N3-ROOTCAUSE.md) — decisive, instrumented
- Consensus is HEALTHY at n=3 (produce/deliver/cite all COMPLETE — instrumented: perfect-lockstep
  DAG, full-cohort citation, no equivocation; plan_round_block IS supermajority-gated). NOT a race,
  NOT fundamental degeneracy.
- Rust `ordering::tau` on the live DAG finalizes ALL 3 turns (45/49 blocks).
- THE BUG = a 5th step the framing missed: (e) the authoritative verified-LEAN tau-order finality
  GATE (DREGG_FINALITY_GATE, default ON) finalizes a strict SUBSET of what Rust tau finalizes on
  the SAME DAG. Flipping gate Lean→Rust (DREGG_FINALITY_GATE=0) → the SAME n=3 committee streams 3/3.
- ⚑ "n=4 fixes it" was a CONFOUND — the n4 mesh ran gate-OFF (Rust tau, streams); the n3 harness ran
  gate-ON (Lean, stalls). NODE COUNT IS SECONDARY; the finality-gate MODE is the real variable.
  (ember's "is there an algorithmic issue at n=3?" skepticism was RIGHT — n4 masked, not fixed.)
- This is a DIFFERENTIAL DIVERGENCE: the verified-Lean finality gate finalizes fewer turns than the
  Rust sibling — the exact class the rust↔lean differential exists to catch. Connects to the
  tau-FFI memoization (tauOrderFast_eq) / A1 work.

## SYNTHESIS — why the payoff (a real flagship turn cross-node) doesn't land, and the fix
Two sequential gates on one pipeline:
- GATE 1 (submit-path, design gap): external client turns don't reach the DAG. Fix: route clients
  through /turns/submit + provision the actor cell at finalization from SignedTurn.signer.
- GATE 2 (finality-gate, Lean divergence): the verified-Lean gate stalls where Rust tau finalizes.
  IMMEDIATE unblock = gate-OFF (DREGG_FINALITY_GATE=0, Rust tau, CORRECT — a config, not a code
  change). REAL fix = reconcile the Lean finality gate with Rust tau (Lean/circuit — Alif/consensus).
- IMMEDIATE PATH TO THE PAYOFF: submit-path fix + gate-off (Rust tau) → a real flagship turn should
  finalize cross-node on the live mesh. NO verified executor needed for finality (gate-off Rust tau
  is correct); the attestation is separate/real regardless. → SURFACE TO EMBER (decision).

## ═══ FULL INTEGRATION (07-07) — the picture is complete ═══
### n=3 finality-gate: DEFINITIVE (b08c738ca) — it's PERFORMANCE, not correctness
- Mechanism CONFIRMED by logs: "Rust ordering::tau differential AGREES" — NEVER DIVERGENCE — with
  `finalized` stuck at 27 while the DAG grows to 49. A *completed* poll on the grown lace would log
  Rust=45 → DIVERGENCE. It never did ⇒ the poll NEVER COMPLETED: the serial finality-executor is
  BLOCKED awaiting the slow O(history) Lean `compute_order` FFI. Slowness, not divergence.
- Gate-OFF (DREGG_FINALITY_GATE=0, Rust tau) → 3/3 streams. Gate-ON (Lean, default) → 2/3 stall.
  n=4 was a CONFOUND (ran gate-off). FIX (designed): memoize compute_order via tauOrderFast/
  tauOrderFast_eq; and/or bounded-timeout fail-open to already-computed Rust tau (A1 neighborhood).
### #2 seed: DONE (1c58283fe) — a verified node LINKS against HEAD
- HEAD-matching Lean seed CUT + VERIFIED on nextop (Darwin-arm64, 21min warm): 8 C-ABI exports +
  tauOrderFast present (absent in stale seed = clean HEAD-differential), FFI round-trips. dregg-node
  built verified (exit 0, zero marshal warnings, lean_available()==true). Installed + pinned +
  fetch-asset staged (~/dregg-seed-staging, Darwin-arm64). TAG empty (publish = ember-gated push).
- ⚠ PLATFORM: seed is Darwin-arm64 (Mach-O). hbox=Linux-x86_64+cold, persvati unreachable → hbox +
  David's lassie need their OWN Linux seed (cut on a Linux box; can't cross-produce from macOS).
### #4 real LLM: DONE + GREEN (ffc8cdd7e) — the last modeled edge closed
- REAL Nemotron (nvidia/llama-3.3-nemotron-super-49b-v1) call WORKED in-env (fresh-nonce-verified,
  not recorded, curl-shell transport) through the unchanged brain code → ZkOracleAttestation VERIFIES
  (authentic∧well-formed∧injection-free); injection caught; tamper refused. Rebuilt exact bytes green.
- Honest wall: the FULLY-confined in-jail live call is bounded by a macOS fork()+objc crash (not
  reqwest-TLS — network reachable), needs a Linux seccomp PD. Named, not faked. Jail+door teeth proven.

## ═══ THE PAYOFF NEEDS EXACTLY 3 CONSENSUS/KERNEL FIXES (all designed, ember's call) ═══
1. SUBMIT-PATH (design gap): route clients through /turns/submit + provision the actor cell at
   finalization from SignedTurn.signer. Touches execute_finalized_turn (commitment path).
2. FINALITY-GATE (perf): memoize compute_order / fail-open bounded-timeout. IMMEDIATE lever = gate-off
   (config, DREGG_FINALITY_GATE=0, Rust tau proven-correct) — no code change.
3. VERIFIED-QUIC (A1 class): the verified binary's blocking executor starves the async QUIC runtime →
   spawn_blocking. Needed for a VERIFIED (not gate-off) live mesh.
- IMMEDIATE PATH: submit-path fix + gate-off → a real attested turn finalizes cross-node (marshal
  finality). + fixes 2&3 → VERIFIED. "know WHY" = DONE; "run for real" = gated on these 3 (ember).

## THRUST (07-07, ember-approved "draft + locally prove all 3")
- ONE coherent lane (ac2c145fb) implements the 3 fixes + LOCALLY PROVES a real attested turn
  stream-finalized cross-node on a local VERIFIED n=4 (isolated target dir, swarm-safe, no live
  deploy — ember gates the live mesh). Single owner of the consensus path (hot tree: distributed-deos
  on api.rs). NEXT: integrate its diffs + local proof → surface to ember for the LIVE-mesh deploy.

## PAYOFF PROOF — in progress (07-07, live-observed)
- LIVE-OBSERVED on a LOCAL VERIFIED n=4 (all 4 federation_mode=full, gate-ON Lean, consensus_live):
  latest_height CLIMBED 0→1→2 (round-1 faucet turn finalized cross-node) — finality STREAMS, NOT
  frozen-at-0 like every pre-fix mesh. Fixes 1 (memoized tauOrderFast) + 3 (spawn_blocking) CONFIRMED
  working live. This is the first verified-gate n=4 that advances height at all.
- Round-2 (the fresh client's OWN signed Transfer) surfaced a real subtlety → fix 2a (74f83d472:
  provision Transfer DESTINATIONS on the ingress scratch too). model-finds-the-bug. Confirming run
  pending (lane ac2c145fb, → /Users/ember/.claude/jobs/5d12f365/tmp/payoff-final.log).
- NEXT: read the confirming-run verdict → if PASS (uniform height + receipt on all 4 + attestation),
  the payoff is locally proven on a verified n=4 → surface the 3 diffs + evidence to ember for the
  LIVE-mesh deploy call. Fixes committed: c976f76ab, 8e7497958, d25e5bddc, 74f83d472, db9b02d6b(harness).

## PAYOFF PROOF — HONEST VERDICT (07-07): PARTIAL, not achieved
- CLEAN run (mine, durable log payoff-mine.log, EXIT 101 FAILED under REQUIRE_FINALITY):
  * ROUND 1 (faucet funds fresh client): HTTP 200 → "client cell funded on ALL 4 nodes" ✓.
    PROVES fixes 1+3 (verified gate-ON n=4 finality STREAMS: height 0→1 uniform) + cross-node cell
    provisioning + the faucet submit→DAG→finalize→execute path. A REAL milestone.
  * ROUND 2 (fresh client's OWN signed Transfer via /turns/submit): HTTP 200 accepted:true BUT
    proof_status="proof_pending", has_witness=false → heights FROZEN at [1,1,1,1], destination
    (false,0) on all 4 for the full 90s. The client turn was ACCEPTED but NEVER FINALIZED.
- The harness note ("residual is loopback QUIC mesh speed") is NOT credible — 0/4 for 90s with
  proof_pending is a turn stuck awaiting a proof, not slow mesh. Likely a 4th gap: VERIFIED-MODE
  PROVING is not wired for /turns/submit external caller-signed turns (the faucet finalizes because
  it's operator/proof-exempt). Diagnosing (proof-gap vs mesh-speed) — do NOT accept the rationalization.
- SO: the payoff (a real attested CLIENT turn finalized cross-node) is NOT achieved. What IS proven:
  verified finality streams on n=4 (fixes 1+3), faucet turn finalizes cross-node, client cell
  provisions cross-node. The remaining wall = external-client-turn finalization in verified mode.

## Round-2 diagnosis — NARROWED to consensus ordering (not proving, not execution)
- Gate-ON reproduced: client turn accepted, height [1,1,1,1], 0/4, 60s. Node stderr (RUST_LOG=warn):
  NO finalized-turn reject, NO verified-order fallback → the Lean tau-order was LIVE and the client
  block simply NEVER ENTERED TAU'S FINALIZED PREFIX (never reached execute_finalized_turn).
- ELIMINATES: proof-gap (my wrong guess — proof_pending doesn't gate finality) AND re-execution-reject.
  The wall is CONSENSUS ORDERING/FINALIZATION: the client block isn't tau-finalized, though the
  faucet turn (byte-identical submit) is. Submit path is byte-identical to faucet (api.rs:3344 vs 6863).
- OPEN (gate-OFF experiment running): block-in-DAG-but-unratified vs never-disseminated; gate-sensitive
  (Lean tau) vs deeper. NOTE the n=3 finding was Lean-gate SLOWNESS — is round-2 the same (client block
  not reached by the slow poll) or genuinely unratifiable? The experiment settles it.

## ★★★ PAYOFF ACHIEVED (07-07) — a real attested client turn stream-finalized cross-node on n=4 ★★★
- DECISIVE gate-off experiment (pre-built green fix-2a binary run directly, bypassing a concurrent
  terminal's broken circuit/src/garbled.rs): gate-OFF (Rust tau) → test result: ok, 1 passed, 29.65s.
  * ROUND 1 faucet funds fresh client → all 4 nodes.
  * ROUND 2 the FRESH CLIENT'S OWN caller-signed attested Transfer via /turns/submit →
    turn ed08c0412a… FINALIZED, destination funded 1000 on ALL 4 nodes, heights [1,1,1,1]→[2,2,2,2].
  THIS IS THE PAYOFF: a real external-client attested turn stream-finalized cross-node on n=4
  (federation_mode=full verified executors), locally proven, reproducible.
- VERDICT on the round-2 wall = the SAME as n=3: the VERIFIED Lean finality GATE is too SLOW
  (O(history)) to reach/finalize the client block; gate-OFF (Rust tau, proven-correct) finalizes it
  in ~30s. gate-ON reliably stalls (0/4, 90s), gate-OFF reliably passes (4/4, ~30s). Lean-gate-specific.
  Fix-1's tauOrderFast memoization covered round-1 but NOT round-2's deeper DAG state → complete it.
- SO: payoff REAL under Rust-tau finality (correct, fast). For FULLY-VERIFIED finality (Lean gate ON),
  the finality-gate perf fix must be completed (extend tauOrderFast memoization / bounded-timeout) —
  same n=3-class perf, KNOWN fix direction. Then gate-ON also finalizes → fully-verified payoff.
- EMBER-GATED next: (a) complete the verified-gate perf (fully-verified payoff), (b) deploy the
  payoff (gate-off) to the LIVE mesh, (c) both.

## Payoff REPRODUCIBLE + plan (ember chose BOTH: complete verified-gate → deploy fully-verified)
- Confirming gate-off re-run PASSED again (turn 997dab21, dest 1000 on all 4, [2,2,2,2], 21.8s).
  Payoff reliably reproducible under gate-off / Rust-tau. ✓
- PLAN (ember-approved): (1) complete the verified-gate perf so gate-ON (Lean tauOrderFast) also
  finalizes round-2's client turn → fully-verified payoff, proven locally; (2) deploy the
  fully-verified payoff to the LIVE mesh (192.168.50.39). Tree is RED (concurrent garbled.rs WIP) →
  builds wait for green; diagnosis/design proceeds now.
- fix-1 wired VerifiedFinality::compute_order (finality_gate.rs:148) → dregg_tau_order FFI = memoized
  tauOrderFast; covers round-1 but round-2's deeper DAG still stalls gate-ON. Completing the perf.

## Verified-gate perf: root cause + design (0cc225a7e, docs/VERIFIED-GATE-PERF.md)
- ROOT CAUSE (confirmed): the serial finality executor (blocklace_sync.rs:3660) recomputes the ENTIRE
  O(n²) verified-Lean order FROM SCRATCH every poll — build_wire formats the whole lace, CStrings it,
  Lean rebuilds PastCache/RoundCache over the full lace then discards them; BlocklaceHandle has NO
  cross-poll cache. As round-2's DAG grows, per-poll cost outpaces block production → finalized prefix
  never reaches the client block in-window. fix-1 killed the within-call blowup (enough for round-1's
  small DAG), NOT the cross-poll recompute. Same N3 class.
- DESIGN (layered): PRIMARY (Rust-only, ship first) = cross-poll order cache keyed on a lace
  fingerprint (skip both FFIs when frontier unchanged) + incremental build_wire + in-flight guard —
  closes the BOUNDED payoff window. DEEPER (Alif's Lean) = stateful/resumable export persisting the
  memo O(Δ)/poll for durable sustained op. FALLBACK (ember-only, FAIL-OPEN-LAW-sensitive) = timeout→Rust tau.
- BLOCKED on: tree RED (concurrent garbled.rs WIP) → implement PRIMARY + prove gate-ON when GREEN.

## Verified-gate perf: IMPLEMENTING (tree green)
- Tree GREEN (dregg-circuit compiles again; the garbled.rs terminal finished). Lane a72e54fd
  implementing the PRIMARY cross-poll cache: BlocklaceHandle.last_order_fingerprint +
  last_lean_order; skip the O(history) Lean compute_order FFI when the lace (sorted block-id
  fingerprint) is unchanged since last poll. Then PROVE gate-ON round-2 finalizes.
- If PASS → fully-verified payoff → deploy to live mesh. If round-2 still stalls gate-ON → the
  residual is the Lean per-call O(n²) itself → DEEPER (Alif's Lean stateful export). Anti-thrash:
  run the test to a durable log, don't offload to a waiter (I take over the run if it thrashes).

## Verified-gate perf: RUST LEVERS EXHAUSTED — the wall is Alif's Lean (measured)
- The cross-poll cache (ba411561c) is implemented, SOUND, built green, working (6-10 hits/node) — but
  CANNOT close gate-ON. Instrumented (7cf197230): the Lean tauOrderFast per-call cost is SUPER-LINEAR
  in lace size: 28 blocks→54ms, 31→663ms, 32→870ms, 34→6770ms, 35→9169ms (~170x for +7 blocks). Once a
  poll takes seconds, the serial executor can't keep 1-block/s pace → runaway → round-2 client block
  never reached on lagging nodes. No reject/divergence — pure perf. Rust-side levers EXHAUSTED
  (incremental build_wire won't help; the dominant cost is the Lean recompute).
- FULLY-VERIFIED gate-ON needs ALIF'S LEAN: a stateful/resumable dregg_tau_order export persisting
  mkPastCache/mkRoundCache across FFI calls (each poll pays only the block-delta → O(Δ)/poll). Well
  characterized in docs/VERIFIED-GATE-PERF.md. NOT a Rust change; do NOT edit Lean source (Alif's).
- ★ The GATE-OFF payoff (real client attested turn cross-node, Rust-tau finality, proven+reproducible)
  is DEPLOYABLE to the live mesh NOW. Fully-verified live deploy waits on Alif's Lean.
- EMBER DECISION PENDING: deploy gate-off milestone to live now / hold for Alif's fully-verified /
  ember-only fail-open (gate-ON timeout→Rust tau, weakens the guarantee).

## CORRECTION + the real fix (we OWN the Lean; not a stopping point)
- ember: we fully own everything incl. the Lean — there is NO handoff to Alif. The verified-gate
  perf fix is OURS.
- ROOT CAUSE (grounded in BlocklaceFinality.lean): the finality caches are LIST-backed — mkPastCache
  (:310) builds causalPastIncl (:143, O(n²) via acc.dedup/contains) per block = O(n³) to BUILD every
  FFI call; cachedPast (:318) + roundLookup (:82) do O(n) List.find? per lookup ×O(n²) calls. That's
  the measured super-linear blow-up (35 blocks→9.2s), recomputed every poll.
- FIX (lane ae93e407): @[implemented_by] HashMap/HashSet-backed fast runtimes for causalPastIncl +
  cachedPast + roundLookup — PURE List defs kept for ALL theorems/#guards (cachedPast_eq, tauOrderFast_eq,
  TauPrefixMonotone, tauGolden), MANDATORY differential #guard proving fast≡pure on a round-2-shaped n=4
  DAG (implemented_by is TRUSTED → the guard is the soundness net; flag the small TCB add to ember).
  Then rebuild the Lean seed + node + PROVE gate-ON round-2 finalizes = the FULLY-VERIFIED payoff.
- Then deploy fully-verified to the live mesh = THE FULL GOAL.

## ★★★ FULLY-VERIFIED PAYOFF ACHIEVED (07-07) — gate-ON, the verified Lean finality gate ★★★
- The @[implemented_by] fix (02c4e1709) WORKS: gate-on-fixed.log shows a CLEAN gate-ON pass —
  fresh client's attested Transfer stream-finalized cross-node on the VERIFIED n=4 (verified Lean
  tauOrderFast gate, NOT gate-off): turn fd3b912e, dest funded 1000 on ALL 4 nodes, heights→[2,2,2,2],
  test result ok, 29.10s (vs the 90s-timeout FAIL pre-fix). The O(n³)→O(1)-HashMap Lean fix closed it.
  Differential #guards (fastCausalPastIncl==causalPastIncl, tauOrderFast==tauOrder) green (build-checked);
  implemented_by TCB add flagged for ember.
- FLAKY at the margin (an earlier run: [2,2,1,1], 2 nodes lag — loopback QUIC mesh variance). Verifying
  reliability myself (3 gate-ON runs, bs6x1jfew). The fix is REAL; margin is tight on this loopback box.
- The seed with the fix is at payoff-target/.../out/libdregg_lean.a (07:33); the INSTALLED
  dregg-lean-ffi/libdregg_lean.a is still the OLD 03:59 seed → must install the fixed seed for the live deploy.
- NEXT (ember: BOTH): confirm reliability → install fixed seed → deploy fully-verified to LIVE mesh
  (check it's safe to restart) → real attested client turn finalizes on the LIVING verified federation = THE GOAL.

## ★★★ FULLY-VERIFIED PAYOFF — ROBUST (07-07): 3/3 gate-ON passes ★★★
- My reliability check: 3/3 gate-ON runs PASSED — all [1,1,1,1]→[2,2,2,2], dest funded on all 4,
  ~30s each. The earlier [2,2,1,1] was concurrent-build contention, not the fix. The verified Lean
  finality gate now RELIABLY finalizes a fresh client's attested Transfer cross-node on n=4. The
  CORE GOAL is met LOCALLY: a real attested agent turn stream-finalizes on a VERIFIED n=4, robustly,
  and the mechanism is fully known (O(n³) List caches → @[implemented_by] O(1) HashMap/HashSet).
- REMAINING: the LIVE persistent-mesh demonstration + push. Deploy friction to scope: the fixed seed
  is Darwin-arm64 (nextop); the live mesh's hbox is Linux-x86_64 and needs its OWN Linux seed (cold
  Lean build). Checking the live mesh topology/safety before the deploy approach.

## LIVE CROSS-MACHINE DEPLOY — underway (07-07, ember back + pushed on hbox)
- hbox (fast 24-core Linux, full elan toolchain) BUILDING the fixed verified node + Linux Lean seed:
  pushed fed-verified-deploy branch (HEAD 04113bb4, Lean-fix present), checked out, cargo build
  -p dregg-node --release + DREGG_REQUIRE_LEAN=1 running (dregg-lean-ffi build-script = the Linux seed
  compile). Log: hbox:~/hbox-seed-build.log.
- Plan: cross-machine verified n=4 (hbox + nextop), gate-ON, submit a real attested client turn →
  verify cross-node finality on the LIVING verified federation = THE FULL GOAL. nextop has the fixed
  Darwin seed (payoff-target); build/confirm its fixed node. Reuse the depth-crown's ~/n4fed launch scripts.

## hbox seed build — invocation fix (07-07)
- `cargo build` does NOT build the Lean seed (build.rs requires a pre-seeded libdregg_lean.a + fails
  loud if absent — correctly, never ships marshal-as-verified). Must run ./scripts/bootstrap.sh FIRST
  (lake-builds metatheory/Dregg2 → the seed), THEN cargo build the node. Running bootstrap.sh on hbox
  now (source ~/.elan/env; log hbox:~/hbox-bootstrap.log). Then cargo build -p dregg-node --release →
  cross-machine verified n=4 deploy.

## hbox bootstrap — phantom caught + really running (07-07)
- CAUGHT: my first bootstrap launches silently failed to detach (log file never created); the
  "bootstrap alive: YES" was a pgrep SELF-MATCH (grep -f bootstrap.sh matched my own ssh cmd). Waited
  ~26min on nothing. verify-never-fake caught it (log MISSING + 0 fresh oleans + real-ps empty).
- FIXED: relaunched via setsid + </dev/null (survives ssh close). NOW genuinely running: log grows,
  real proc bash scripts/bootstrap.sh, in the "lake exe cache get" mathlib phase (fast path; 3057
  mathlib oleans already present) → then Dregg2 closure → leanc → the Linux seed. Watching the SEED
  FILE (dregg-lean-ffi/libdregg_lean.a), not pgrep.

## ★ hbox Linux seed BUILT + verified (07-07, 18:46): 536MB, 14 exports (dregg_tau_order,
## dregg_exec_full_forest_auth,...), round-trips the verified Lean kernel. Reflects the Lean-fix
## (02c4e1709 implemented_by). Node build (cargo -p dregg-node --release) launched setsid-detached,
## links the seed → the fixed VERIFIED Linux node. Then cross-machine deploy.
