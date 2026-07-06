# LIVE-BYZANTINE — adversarial audit of the deployed distributed protocol

Attacks the **live** consensus/federation a Byzantine node runs (the layer the
N3 testnet exercised) — NOT an idealized model. The single-turn soundness proof
(`CircuitSoundness.lean::lightclient_unfoolable`) and the whole-history fold
(`lightclient::verify_history`) do not cover this: they attest ONE turn / ONE
folded chain, but say nothing about whether a Byzantine committee member can
split finality, wedge liveness, or serve a state a light client would accept.

Scope read: `blocklace/src/{finality,ordering,evidence}.rs`,
`node/src/{finalization_votes,finality_gate,prove_pool,blocklace_sync,state}.rs`,
`persist/src/federation.rs`, `lightclient/src/lib.rs`.

Verdict key: **CLOSED-by-X** (a deployed gate closes it) · **LIVE-GAP** (a real
hole with a forge) · **RESIDUAL** (a named honest floor, not a bug).

---

## Attack 1 — EQUIVOCATION (double-sign two conflicting heads) — CLOSED

**Question.** Can a Byzantine committee member sign two conflicting blocks/turns
at the same height/slot and split finality into two committee-ratified heads —
two valid quorum certs for conflicting states?

**Verdict: CLOSED**, at two independent layers.

1. **Ordering excludes the equivocating leader.**
   `blocklace/src/ordering.rs::find_all_final_leaders` (line 386) finalizes a
   wave leader ONLY when `leader_blocks.len() == 1` — a leader that produced two
   blocks at the wave-start round is *skipped entirely* (no finalization that
   wave). A non-leader equivocator is excluded from every leader's coverage by
   `has_equivocation_in_past` (`ordering.rs:160`, consumed at `tau` line 547).
   So a double-signer's blocks are never ordered.

2. **Quorum intersection forbids two super-ratifications.** Super-ratification
   (`is_super_ratified`, `ordering.rs:305`) needs `supermajority_threshold(n) =
   ⌊2n/3⌋+1` distinct participants ratifying at the wave-end round. Two such
   quorums intersect in strictly more than the Byzantine budget `f=⌊(n-1)/3⌋`
   for **every** n (proven: `ordering.rs::test_supermajority_quorum_intersection_unconditional`,
   line 1048). The `2f+1` honest participants cannot form two disjoint
   supermajorities, so at most one of two conflicting blocks can be
   super-ratified. No two ratified heads.

3. **Detection + eviction is deployed.** `Blocklace::detect_equivocation`
   (`finality.rs:835`) implements the paper's content-independent Def 4.2
   (incomparable same-creator pair — catches forks at *different* seq too), runs
   on BOTH the live `receive_block` (line 647) and `merge` (line 720) paths and
   on the untrusted-checkpoint recovery path (`from_checkpoint`, line 1193). The
   equivocator's tip is withdrawn and the creator marked; evidence is retained
   as a lace-free-certifiable wire value (`evidence.rs::EvidenceOfEquivocation`,
   two Ed25519 checks + three equalities).

**Existing teeth.** `blocklace/tests/consensus_fault_sim.rs::
byzantine_equivocation_excluded_safety_and_liveness_held` delivers the two forks
in OPPOSITE orders to different honest nodes (the split-brain attempt) and
asserts order-independent detection + identical finalization + exclusion.

**New tooth (this audit).** `blocklace/tests/byzantine_finality_split.rs::
equivocating_leader_cannot_super_ratify_two_heads` builds the concrete
two-conflicting-leader-blocks DAG and asserts `tau` finalizes NEITHER head — the
direct refutation of "two quorum certs for conflicting states."

**Residual (named).** The FINALITY-VOTE layer (`finalization_votes.rs`) keys
votes by `block_id`, so a Byzantine member CAN emit a valid vote for each of two
conflicting block-ids. This does not split finality because (a) honest nodes
only vote for a block their local `tau` finalized (gated at
`blocklace_sync.rs:3674` on `has_voted`), and by (1)+(2) at most one conflicting
block is ever `Ordered` in an honest view; and (b) the vote is a distinct-signer
count toward *order* agreement, never a state cert (see Attack 5). The equivocator
gains nothing but its own eviction.

---

## Attack 2 — WITHHOLDING / CENSORSHIP — CLOSED (graceful) + liveness RESIDUAL

**Question.** Can a Byzantine node withhold a turn/block worse than fail-stop —
a withholding pattern that wedges finality where a crash would not?

**Verdict: CLOSED for safety; liveness degrades gracefully.**

- Finalization needs a supermajority of *cordial* wave-end blocks
  (`ordering.rs::is_cordial`, line 569, `> 2n/3` predecessors from the prior
  round). A withholder contributes ≤ f; the `2f+1` honest supermajority still
  super-ratifies. Withholding to a subset only *delays* (the block reaches the
  supermajority via CRDT union-merge gossip; `tau` is monotone —
  `ordering.rs::test_monotonicity`), it never forks (the same quorum-intersection
  as Attack 1).
- A withholding LEADER is *strictly weaker* than a crashed one: if it reveals its
  leader block to nobody, the wave is skipped exactly as for a dead leader; if it
  reveals to some, either the block reaches a supermajority (all converge and
  finalize it) or it does not (no one super-ratifies). There is no "reveal to
  exactly a sub-quorum" pattern that finalizes for one honest node but not
  another — super-ratification is evaluated against each observer's own causal
  past and requires a supermajority, which is a single set the honest majority
  cannot be split across.

**Existing teeth.** `consensus_fault_sim.rs::{n4_survives_f_kills_and_stalls_at_f_plus_one,
n7_survives_two_kills_and_stalls_at_three}` — f fail-stops tolerated, f+1 STALLS
(safe, never forks). The N3 partition drill confirmed finality freezes correctly
with 1 node down.

**Residual (named, TERMINAL).** Sustained targeted withholding by ≤ f nodes is a
*liveness* degradation (slower finality), never a safety one — the standard BFT
liveness-under-partial-synchrony floor. Not a bug.

---

## Attack 3 — COMMITTEE-RESTART blast radius — CLOSED (Fix B landed), safety intact

**Question.** The N3 run found committee nodes FAIL-CLOSED on restart (persisted
attested root carries 1 sig vs threshold 3). Is the fail-closed genuinely SAFE,
or can an adversary FORCE restarts to wedge the committee permanently (a liveness
DoS)?

**Verdict: CLOSED — was SAFE-but-DoS-able (a live liveness gap); Fix B landed.**

The mechanics as originally found, grounded:

- The recovery anchor `state.rs::verify_signed_anchor_and_rollback`
  calls `StoredAttestedRoot::verify_signatures` (`persist/src/federation.rs`),
  which requires `quorum_signatures.len() >= threshold` valid committee
  signatures over the root's `signing_message()`. A same-epoch root with a
  sub-quorum count **refused to start**.
- The producer under-fed it: the synchronous persist pushes ONLY the local
  node's signature (`1 < threshold` in full mode) — the cross-node quorum
  forms async, after the persist.

**Safety: CORRECT.** The node never serves a finalization it cannot anchor to a
committee quorum. `verify_signatures` also binds the *state root* (three sigs
over a DIFFERENT `merkle_root` are refused — `persist/src/tests.rs:182`), and the
NODE-2 anti-rollback floor (`state.rs:1308`) refuses a recovered head below a
witnessed finalized height (no nullifier resurrection). This is correct hardening.

**✅ Fix B is LANDED at HEAD (2e38c8c49).** All three legs are wired:
(i) the cryptographic binding — `FinalizationVote` v2 signs
`dregg-finalization-vote-v2 || block_id || merkle_root` (`types/src/lib.rs:412`;
`node/src/finalization_votes.rs` carries `merkle_root`, and the `VoteCollector`
RETAINS the signature bytes, handing back the assembled `>= threshold` set via
`assembled_quorum`); (ii) the producer — the commit path captures an
already-assembled quorum at first persist (`blocklace_sync.rs`, the
`finalization_quorum` capture just before `store_attested_root`) and
`backfill_finalization_quorums` (`blocklace_sync.rs:3886`) re-stores recent roots
once the trailing votes converge (the deliberate liveness cost: the quorum trails
the head by a gossip round or two); (iii) the restart anchor —
`verify_signed_anchor_and_rollback` accepts `verify_signatures(c) ||
verify_finalization_quorum(c)` (`state.rs:1300,1391`), with a TRAILING-HEAD branch
that anchors to the highest lower quorum-carrying root (never trusting an
unverified head — the head's self-signature still tamper-checks its own
`merkle_root`). Pinned green: `persist::tests::
committee_node_restarts_cleanly_with_finalization_quorum`,
`persist/tests/byzantine_state_attestation.rs::
finalization_quorum_rejects_forged_and_noncommittee_signatures`, and
`full_mode_single_sig_root_is_refused_genuine_quorum_accepted`. A full-mode
committee node now restarts cleanly once its quorum back-fills; the residual is
only the trailing-head replay window (bounded, liveness-neutral).

**Liveness: RESTORED.** The pre-fix failure mode — any full-mode committee node
that finalized ≥1 height could never rejoin after a restart, so an adversary who
could *induce* restarts (a crash bug, resource pressure; F-DOS-1's inline-prover
wedge, fixed by `prove_pool.rs`, was exactly such a lever) could knock the
committee below quorum **permanently** — no longer exists: a restarting node
re-anchors on the back-filled `finalization_quorum` and rejoins. What remains is
the bounded trailing-head window (a head persisted before its votes converged is
replayed, not trusted), which is a delay, not an exit.

**Also named — a fail-OPEN sibling.** If `committee` is empty at boot
(`state.rs:1232`) the signed anchor is SKIPPED (best-effort HWM only). A boot
path that loses its committee keys (config corruption) downgrades to the
tamperable-redb backstop. Trusted-boot assumption; named residual.

**Fix taken (Fix B).** The second of the two diagnosed routes: `FinalizationVote`
extended to v2 to bind the finalized `merkle_root`, its signatures retained by the
collector, aggregated to ≥threshold and back-filled into the persisted root. This
also supplies the cryptographic material for Attack 5b's state cert (the SERVING
of it is 5b's remaining work). Pinned by `persist/src/tests.rs::
full_mode_single_sig_root_is_refused_genuine_quorum_accepted`.

---

## Attack 4 — PARTITION EDGES beyond the drill — CLOSED for order; state = Attack 5

**Question.** Asymmetric partitions, a heal with divergent committed prefixes, a
minority that thinks it finalized. Can a healed partition produce two histories
that BOTH verify (a partition analog of the closed prefix-hiding)?

**Verdict: CLOSED at the ordering + light-client-cert layer.**

- A minority partition below `supermajority_threshold` finalizes NOTHING new
  (`consensus_fault_sim.rs::partition_heals_without_conflicting_finalization`): it
  cannot super-ratify, so it never "thinks it finalized." The majority finalizes
  a longer prefix; on heal, CRDT union-merge converges all nodes to the identical
  `tau` order, and the pre-heal majority prefix survives (monotonicity). No two
  finalized histories.
- For a light client that never saw the lace, the FORK analog is closed by the
  **committee-anchored** finality cert: `lightclient::FinalityCert::
  has_committee_quorum` (lib.rs:427) counts a ratifying signature ONLY if the
  signer is in the client's TRUSTED committee AND the Ed25519 signature verifies
  over `(finalized_root, participant_count)`. An equivocating prover that folds a
  valid aggregate over a fork and mints fresh keypairs cannot raise the count
  (its keys aren't in the committee — `NoQuorum`, lib.rs:471). The genesis anchor
  closes the dual prefix-hiding (`GenesisMismatch`, lib.rs:461).

**Residual → Attack 5.** The committee-anchored cert is SOUND and verified, but
**no deployed node SERVES it** (only the demo binary
`lightclient/src/bin/whole_history_demo.rs` produces one). The deployed
cross-node quorum (`FinalizationVote` v2) now binds `(block_id, merkle_root)` and
is persisted (Fix B), but is not exposed on the wire. So Attack 4 is closed for
ORDER (re-executing validators converge deterministically) and for a light client
*if it is handed a state-root cert* — but the deployed path does not hand it one.
See Attack 5.

---

## Attack 5 — EXECUTOR as the soundness boundary + the async prove window — RESIDUAL (the headline find)

**Question.** `execute_via_producer` commits state BEFORE the async prove pool
attests. Can a Byzantine node commit an INVALID turn (that the async prove would
reject) and serve it before the proof catches up — a window where committed state
and provable state diverge on a Byzantine node, visible to a light client?

**Two distinct sub-questions; two distinct verdicts.**

### 5a — the async-prove window, for a re-executing validator: CLOSED

`prove_pool.rs` (module docs, lines 18-25) makes the design explicit: the
executor is the soundness boundary; the STARK proof is *additive attestation*,
generated off the commit path. In `execute_finalized_turn` the state overlay is
installed ONLY from the pre→post `Cell` diff of a `TurnResult::Committed`
execution (`blocklace_sync.rs:4034` diff, gated by the `Committed` match arm at
line 4080). A `TurnResult::Rejected` execution mutates nothing on the cloned
`exec_ledger`, so `touched_ids` is empty and no state change is installed — an
invalid turn simply does not commit. Every honest node re-executes the
BFT-ordered turn deterministically (via the same `execute_via_producer` / verified
Lean producer) and reaches the identical `Committed`/`Rejected` verdict and the
identical `canonical_ledger_root`. A Byzantine node that force-commits a divergent
state cannot make honest nodes agree with it — they re-execute and diverge. So
for the re-executing validator population, the async-prove window is a *liveness*
property of the attestation layer (a dropped proof self-heals; `prove_pool.rs:48`),
never a safety hole.

### 5b — the LIGHT-CLIENT state binding: RESIDUAL (the real gap; Fix B in flight)

A light client does NOT re-execute — that is the whole point. It must rely on a
certificate. Here the deployed path leaves a genuine (now narrowed) hole:

- **Order AND state are now BFT-certified in the store.** The cross-node
  committee artifact the live node assembles is the `FinalizationVote` quorum,
  upgraded to **v2** to bind the state root:
  `finalization_vote_signing_message = dregg-finalization-vote-v2 || block_id ||
  merkle_root` (`types/src/lib.rs:412`, `node/src/finalization_votes.rs`), and
  Fix B (landed — see Attack 3) aggregates ≥threshold of those signatures into
  the persisted root's `finalization_quorum`
  (`blocklace_sync.rs::backfill_finalization_quorums`).
- **The certificate a light client needs exists but is unfed.**
  `lightclient::FinalityCert` (signatures over `finalized_root`, lib.rs:278/427)
  is the sound, committee-anchored state cert — but it is produced ONLY in the
  DEMO binary. No deployed node emits one.
- **The served surface is STILL count-only.** `GET /api/federation/roots`
  (`api.rs::get_federation_roots`) returns `merkle_root` + `signatures:
  quorum_signatures.len()` with NO committee verification and does NOT expose the
  now-persisted `finalization_quorum`. A light client trusting this sees a
  `merkle_root` backed by a bare count — a single Byzantine node can present any
  forged root with `signatures: 1` (or a self-threshold-1 federation with a
  self-`verify`-valid root), and the served artifact carries no committee cert to
  arbitrate two conflicting equal-height roots.

**Consequence (narrowed by Fix B).** The committee state cert now EXISTS in the
store (`finalization_quorum`, ≥threshold v2 votes over `(block_id, merkle_root)`),
but the node does not SERVE it: a Byzantine node can still hand a light client a
`merkle_root` whose served artifact the committee never collectively certified.
This is NOT a consensus-*order* break (Attacks 1/4 hold) and NOT a break against
re-executing validators (5a). It is a **missing state-finality certificate on the
deployed light-client wire** — the single-turn and whole-history proofs assume
they are HANDED a committee-finalized `final_root`. The remainder is serving-side
only: expose the persisted `finalization_quorum` (or an assembled
`FinalityCert`) on the API and have the light client verify it against its
trusted committee.

**New tooth (this audit).** `persist/tests/byzantine_state_attestation.rs::
byzantine_conflicting_state_roots_both_pass_count_only_gate` forges two
`StoredAttestedRoot`s with the SAME `blocklace_block_id` + height but CONFLICTING
`merkle_root`, each self-signed, and asserts (a) BOTH satisfy the count-only
`is_structurally_complete()` gate the API surfaces, and (b) NEITHER satisfies a
genuine ≥threshold committee `verify_signatures`/`verify_finalization_quorum` —
proving the SERVED state-attestation has no BFT binding a light client can use,
and that the closing gate is exactly the committee quorum Fix B now persists
(its sibling test `finalization_quorum_rejects_forged_and_noncommittee_signatures`
pins that the discriminator is crypto-bound, not a count).

**Fix direction (remaining).** Serving-side: expose the persisted
`finalization_quorum` on the API (or assemble it into a served
`FinalityCert`) and feed it to the already-sound
`FinalityCert::has_committee_quorum` in the light client. The store-side half
(Attack 3's Fix B) is done.

---

## Summary

| # | Attack | Verdict | Closing gate / gap |
|---|--------|---------|--------------------|
| 1 | Equivocation | **CLOSED** | single-leader-per-wave + unconditional quorum intersection (`ordering.rs:386,236`) + detect/evict (`finality.rs:835`) |
| 2 | Withholding | **CLOSED** (+liveness residual) | supermajority cordiality; withholding ≤ fail-stop (`ordering.rs:569`) |
| 3 | Committee restart | **CLOSED** (Fix B landed, 2e38c8c49) | v2 vote quorum back-filled into `finalization_quorum` (`blocklace_sync.rs:3886`); restart anchor accepts `verify_finalization_quorum` (`state.rs:1300`) |
| 4 | Partition edges | **CLOSED** (order + LC cert) | minority can't super-ratify; committee-anchored cert (`lightclient:427`) |
| 5 | Executor / async prove | **5a CLOSED / 5b RESIDUAL (narrowed)** | re-exec deterministic (`prove_pool.rs:18`); committee state cert now PERSISTED (v2 votes bind `merkle_root`) but not SERVED (`/api/federation/roots` count-only; `FinalityCert` unfed) |

**Highest-value find:** Attacks 3 and 5b were the SAME missing weld — the deployed
committee certified ORDER (`block_id`) but never STATE (`merkle_root`). Fix B
landed that weld store-side: `FinalizationVote` v2 binds the state root and the
≥threshold quorum is persisted (`finalization_quorum`), which closed Attack 3
outright. The remaining honest gap (5b) is serving-side only: expose the persisted
committee state cert to the non-re-executing light client and verify it there.
No consensus-ORDER Byzantine break was found.
