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
