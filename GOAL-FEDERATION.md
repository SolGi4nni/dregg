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
