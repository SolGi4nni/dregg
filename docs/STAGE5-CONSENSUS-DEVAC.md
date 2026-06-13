# STAGE 5 — De-vacuifying the consensus front (Klein Stage 5 / HIGH-6)

**Status:** investigation report + precise burn-down map (2026-06-13, consensus-devac lane).
Present-tense description of what exists with file:line; sections titled **PLAN** are the proposed
slices. Companion: `docs/CONSENSUS-FLEX.md` (finality-on-demand design), the in-process witness
`blocklace/tests/multi_node_convergence.rs`, the running-node witness `node/tests/three_node_ordering_rule.rs`
+ `scripts/devnet-n3-ordering.sh`, and the Lean model `metatheory/Dregg2/Distributed/BlocklaceFinality.lean`.

## The claim under test

> "Deployed consensus is n=1 and skips the ordering rule, so the Byzantine-safety theorems are
> vacuous on the running node."

This is THREE distinct claims wearing one sentence. After reading the code and standing up real
3-node clusters, here is the precise verdict on each.

---

## Verdict 1 — the Lean BFT model is NOT vacuous (the framing was partly stale)

The task framing said the Lean side is "empty-adversary `BFTModel` inhabitant + assumed
`gst_liveness` oracle = vacuous." Reading the current code, that is **not** the situation:

* **`BFTModel` safety is adversary-parametrized and genuine.** `metatheory/Dregg2/Proof/BFT.lean:69-88`
  defines `BFTModel` with a real adversary field `Byzantine : Nat → Prop` plus the constraints
  `fault_bound` (≤ f Byzantine in any two blocks' voter union), `bft_threshold` (n > 3f),
  `population_bound`, and `honest_vote_once`. The safety theorem `bft_safety` (`:161-168`) is
  quantified over an **arbitrary** such `M`: it does real quorum-intersection counting
  (inclusion–exclusion, `:132`) to extract an honest witness in `Q₁ ∩ Q₂` and then uses
  `honest_vote_once` for the contradiction. The adversary CAN equivocate within budget; the
  theorem still holds (revealing the n > 3f bound). The empty-adversary inhabitant
  (`Inhabited.model`, `:195-220`, `Byzantine := fun _ => False`) is ONLY a joint-satisfiability
  witness — it shows the fields are not contradictory; it is NOT the model the theorem operates on.
  That is exactly how a well-formed Lean proof is structured, NOT a vacuity.

* **Liveness is reduced, not assumed-as-an-oracle.** `World.gst_liveness` (`metatheory/Dregg2/World.lean:104-115`)
  is a typeclass FIELD (never an `axiom`). `Proof/BFTLiveness.lean` REDUCES its conclusion from a
  DLS88/HotStuff `Pacemaker` whose quorum is DERIVED by transitivity (`honest_quorum` ≤ delivered
  voters), and exhibits a concrete inhabitant. The terminal assumption is the pacemaker's
  `synchronizes` (eventual honest leader after GST) — the **FLP-respecting** boundary, named in the
  assurance case as `PostGSTProgress` (`AssuranceCase.lean:40-41`). That is a legitimate, irreducible
  assumption, not laundered vacuity.

* **The Lean tau model faithfully refines the Rust rule.** `Distributed/BlocklaceFinality.lean` models
  `blocklace/src/ordering.rs::tau` line-for-line as executable Lean (`computeRounds` / `findAllFinalLeaders`
  / `isSuperRatified` / `tauOrder`), proves `finalLeaders_one_per_wave` + `tauOrder_deterministic`
  (`#assert_axioms`-clean), and ships a Rust↔Lean DIFFERENTIAL on a concrete multi-node trace. The
  honest-laggard non-monotonicity is named (`Consensus/TauPrefixMonotone.lean`, conditional under
  `FinalizedRegionStable`, refuted unconditionally).

**Net:** the Lean consensus is a genuine, non-vacuous, faithfully-refined model. There is NO de-vac
work to do on the Lean safety/liveness theorems themselves. The one named residual is the FLP-terminal
`synchronizes` pacemaker field — correctly an assumption.

## Verdict 2 — the ordering RULE is real and runs at n>1 (the deployed-default is the vacuity)

The running node has exactly ONE consensus engine, `--consensus blocklace` (Cordial-Miners), and it
is real:

* `supermajority_threshold(n) = ⌊2n/3⌋ + 1` (`blocklace/src/ordering.rs:196`), the ONE quorum formula
  (federation `quorum_threshold` delegates here; unit-tested intersection > f for all n,
  `:988-999`). At n=3 this is **3** (`:978`) — all three must ratify.
* `is_super_ratified` (`:263-301`) requires a supermajority of DISTINCT participants with wave-end
  blocks ratifying the round-robin leader; `tau` (`:439`) walks final leaders and `xsort`s coverage.
* The node's `poll_finalized_blocks` (`node/src/blocklace_sync.rs:515`) branches on
  `participants.len()`: `<= 1` → the n=1 path (order by sequence, never runs tau, `:551-564`);
  `> 1` → the **verified multi-party path** (`:565-645`), where the authoritative order is the Lean
  `dregg_tau_order` export (Rust `tau` is the differential sibling), gated by the verified
  `dregg_blocklace_finalize` (`:667-672`). All three FFI symbols are linked into the binary
  (`nm` confirms `_dregg_tau_order`, `_dregg_blocklace_finalize`, `_dregg_strand_admit`).

**The deployed vacuity is operational, not theoretical:** the devnet boot script defaults
`FEDERATION_MODE=solo` (`demo/multi-node-devnet/start_devnet.sh`: "keep each federation in solo mode
so a single-node sub-quorum can produce blocks during the demo"), so the running devnet takes the
`participants.len() <= 1` branch and never exercises tau. The fix is to run with a multi-validator
genesis (which populates `known_federation_keys` from `genesis.json` validators at
`node/src/main.rs:528-542`, regardless of the solo/full flag) so `participants = N` and the
multi-party tau branch is the live finality path. **This slice landed** — see Verdict-2 artifacts.

### What landed (the running-node witness at n>1)

* `scripts/devnet-n3-ordering.sh` — boots 3 real `dregg-node` processes in `--federation-mode full`
  with a 3-validator genesis (threshold=3), submits a real faucet Transfer turn, and asserts:
  **[A]** all nodes `federation_mode=full` with 3 distinct identities (anti-vacuity: supermajority(3)=3,
  so no single node self-finalizes), and **[B]** cross-node block exchange over the real `dregg_net`
  QUIC gossip wire (the shared DAG grows beyond genesis; ≥2 distinct creators reach a node). It then
  PROBES **[C]** full cross-node turn finalization and reports it precisely (see Verdict 3).
* `node/tests/three_node_ordering_rule.rs` — the same as a CI-runnable integration test (spawns the
  real binary via `CARGO_BIN_EXE_dregg-node`; no mock). [A]+[B] are hard assertions; [C] is reported,
  gated hard only under `DREGG_TEST_REQUIRE_FINALITY=1`.

Measured: [A] and [B] PASS reliably. Full mode is engaged; the multi-party tau branch with
supermajority=3 is the live finality path; blocks created on one node reach the others over the wire.
**The consensus path provably runs at n>1, not n=1.**

## Verdict 3 — the OPEN: the running node does not yet COMMIT a turn through the rule at n>1

This is the real, measured Stage-5 frontier, and it is NOT the ordering rule or the Lean model.

**Observed (reproducibly, via the script/test above):** with 3 nodes in full mode, a submitted turn
does NOT reach a cross-node attested root — `latest_height` stays 0 on all three, `/federation/roots`
stays `[]`, and the finality executor (`spawn_finality_executor`, `node/src/blocklace_sync.rs:1856`)
never fires (no "executing finalized blocklace blocks"). The DAG grows, but turns never finalize.
The same was observed at **n=2** (supermajority=2), so it is not a 3-specific edge.

**Root cause — gossip DISSEMINATION, file-cited:**

* A node builds each block linking ALL the tips it has *received so far* (`Blocklace::add_block`,
  `blocklace/src/finality.rs:586` — `predecessors = self.tips.values()`). For tau to super-ratify a
  leader, the DAG must approach the **round-synchronous** shape where every participant's round-r
  block links all three participants' round-(r−1) blocks (exactly what `ordering.rs`'s
  `build_full_blocklace` test fixture and `blocklace/tests/multi_node_convergence.rs` construct
  BY HAND).
* The running gossip layer (`net/src/gossip.rs`) is an eager/lazy Plumtree + Dandelion++ stem design
  over **unidirectional QUIC streams** (`:3`), with the eager set seeded from the addresses a node
  DIALS (`join_topic(TOPIC_BLOCKLACE, &peer_addrs)`, `node/src/blocklace_sync.rs:1140`) and a stem
  policy that "never fluffs directly to the mesh while an anchor relay is available" (`:128-145`).
  Empirically at small N on loopback this delivers blocks **asymmetrically**: in an n=2 run the
  submitting node saw only its OWN blocks (`proposers=1`) the entire run while its peer saw both; in
  n=3 runs nodes saw 1, 2, or 3 distinct creators unevenly and `buffered_orphans` grew (blocks arrive
  before their predecessors). No node assembles a causally-closed round with a supermajority of
  creators' wave-end blocks → `is_super_ratified` (`ordering.rs:263`) never returns true → no
  `FinalizedBlock::Turn` → no commit.
* This IS the honest-laggard dynamic the Lean model already names (`TauPrefixMonotone`), surfacing at
  the running-node gossip layer rather than the rule.

**This does not contradict the assurance case.** The assurance case's consensus claims are about the
PROVEN properties of the rule (safety via quorum intersection; liveness modulo `PostGSTProgress`) and
"revocation takes effect at finality (consensus-bound)" — it does not claim the running node achieves
n>1 finalization under the current gossip layer. So this is a **deployment-fidelity gap** (the rule is
verified; the dissemination that feeds it is incomplete), the same shape as the codec translation-
validation gap (HORIZONLOG §Stage-1). It must still be closed — a verified rule that never finalizes on
the running node is the operational tooth missing from HIGH-6.

---

## PLAN — the precise Stage-5 burn-down (ranked)

**S5-1 (THE blocker, HIGH) — full block dissemination at n≥2 so tau finalizes on the running node.**
The eager/lazy mesh must guarantee that every honest creator's blocks reach every honest node (the
liveness precondition tau needs), even at small N. Concretely: (a) make the eager set BIDIRECTIONAL
(a dialed peer adds the dialer to ITS eager set on first contact), or (b) drive cordial dissemination
+ frontier-pull (`send_frontier`/`catchup_tick`, `blocklace_sync.rs:407,426` already exist) hard
enough that the orphan buffer always drains to a causally-closed round before the next wave, or (c)
for the small-committee federation case, eager-push to ALL committee peers (the privacy stem is for
public tx-origin hiding, not intra-committee block sync — these are different topics). The acceptance
test ALREADY EXISTS: flip `node/tests/three_node_ordering_rule.rs` [C] to a hard assertion
(`DREGG_TEST_REQUIRE_FINALITY=1`) — it must go green, i.e. all 3 nodes reach an AGREED attested root
(`latest_height ≥ 1`, identical `latest_root`). Owner surface: `net/src/gossip.rs`,
`blocklace/src/dissemination.rs`, `node/src/blocklace_sync.rs`. This is the keystone — everything below
is comparatively cheap once turns finalize cross-node.

**S5-2 (MED) — Lean↔Rust commit refinement on the LIVE finalized turn.** Today the multi-party path
asserts the Lean `dregg_tau_order` == Rust `ordering::tau` differential on the `(creator, seq)`
multiset per poll (`blocklace_sync.rs:599-628`), and the Lean model proves the rule's safety. The
missing leg is a refinement that the SEQUENCE OF FINALIZED TURNS the node commits equals the Lean
`tauOrder`-driven `Exec.ConsensusExec.executeFinalized` run — i.e. lift `tau_drives_verified_run`
(`BlocklaceFinality.lean`) to the actual node commit cursor (`execution_cursor.rs`). Gated on S5-1
(needs a real finalized turn to refine against). Capture the live finalized order via the trace-export
hook (HORIZONLOG §live-capture) and `#guard` it against the Lean `tauGolden`.

**S5-3 (MED) — quorum-formula unification consumer migration (#170).** The Lean twin
`supermajorityThreshold` LANDED (`QuorumThreshold.lean`) and the Rust has ONE formula
(`ordering.rs:196`), but `BlsQuorumCert.lean` / `EpochReconfig.lean` still transcribe the historical
`n − ⌊n/3⌋` and carry `StrictBft`; `MembershipSafety.lean` keeps the `n=0↦0` guard. Migrate the
consumers (`bls_quorum_diff.rs` / `epoch_diff.rs` / `membership_safety_differential.rs` pin the
relations until then) so there is provably ONE quorum formula end to end. Independent of S5-1.

**S5-4 (MED) — make consensus a leg of the composed apex.** `AssuranceCase.lean`'s
`deployed_system_secure` conjoins A∧B∧C∧D∧E with liveness resting on the `Pacemaker`. Add a
consensus-commit leg whose SUBJECT is the running node's actual finalized-turn product (the
`executeFinalized` output under `tauOrder`), so the composed theorem's Freshness-D
"revocation takes effect at finality (consensus-bound)" is witnessed by the SAME object the node
commits — closing the loop from `bft_safety` through `tauOrder` to the live attested root. Gated on
S5-2.

**S5-5 (LOW) — reconcile the equivocator predicate Lean↔Rust (already aligned; pin it).** The Lean
`hasEquivInPast` (`BlocklaceFinality.lean:148`) is observer-local (over an observer's causal past),
matching the Rust `EquivocationProof` (`blocklace/src/lib.rs:244`, detected observer-locally on
insert). They already agree; add a differential test pinning the Lean observer-local verdict against
the Rust `auto_evict`/exclusion path on a forked trace (the in-process `multi_node_convergence.rs`
Phase 4 already exercises the Rust side — mirror its verdict in Lean) so the alignment is a regression
gate, not an observation.

**S5-6 (LOW, design) — finality-on-demand.** Per `docs/CONSENSUS-FLEX.md`: the running node runs ONE
tier (tau) for n>1; most single-cell turns are I-confluent and could finalize at causal-ack depth
(the fast path), reserving tau for contended ops. This is a separate, larger design lane — noted here
because once S5-1 makes tau-finality real, the tier dial (`Finality.lean` `Selector.groupTier`,
proved) is the natural next reduction of consensus cost. Not required for HIGH-6.

---

## One-line summary

The Lean BFT/liveness model is genuine and non-vacuous; the ordering rule is real and provably runs at
n>1 in full mode (landed: `scripts/devnet-n3-ordering.sh` + `node/tests/three_node_ordering_rule.rs`);
the remaining HIGH-6 tooth is **S5-1** — the running node's gossip does not yet fully disseminate the
DAG, so tau never super-ratifies and turns don't commit cross-node. Close S5-1 and flip the test's [C]
gate green, and "deployed consensus skips the ordering rule" is dead.
