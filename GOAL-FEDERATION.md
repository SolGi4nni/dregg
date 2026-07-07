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
