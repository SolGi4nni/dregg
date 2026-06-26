# The verified surface — a constellation of apexes

dregg's formal assurance is not a single theorem. It is a **constellation** of Lean apexes,
each ruling out a distinct class of failure. This document maps what IS a verified apex today
(grounded to the theorem that proves it), then ranks the next apexes to build by leverage ×
tractability. It is a what-is + where-next map; verify each citation against the module at HEAD.

The convention throughout: **carriers are hypotheses, never axioms.** The standard cryptographic
floor (FRI/STARK soundness, Poseidon2 collision-resistance) and the standard distributed floor
(honest majority `n > 3f`, post-GST delivery) are named structure fields or theorem premises, so
every keystone stays `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).

## What IS a verified apex today

### Per-turn validity — the light client cannot be fooled
- **`lightclient_unfoolable`** (`Dregg2/Circuit/CircuitSoundness.lean`) — an accepted batch
  witnesses a genuine kernel transition: accept ⟹ ∃ a real kernel step the proof attests.
- **`deployed_system_secure`** (`Dregg2/AssuranceCase.lean`) — the composed apex
  A ∧ B ∧ C ∧ D ∧ E over one deployed turn: authority (non-amplification), conservation (Σδ = 0),
  integrity (the receipt binds the whole post-state), freshness (anti-replay), unfoolability.
  Each conjunct is its own re-pinned keystone (`authority_guarantee`, `conservation_guarantee`,
  `integrity_guarantee_whole_turn_covered`, `freshness_guarantee`, `unfoolability_guarantee`).

### Settlement — authority is live where it is exercised
- **`settlement_soundness`** (`Dregg2/Circuit/SettlementSoundness.lean`) — authority is live at
  the settlement point; revocation is non-monotone at settlement (the distributed-time-travel
  result, wired into the production `stitch_pair`).

### Consensus safety — finality does not equivocate
- **`bft_safety` / `bft_agreement`** (`Dregg2/Proof/BFT.lean`) — over one vote pool: two
  conflicting blocks cannot both reach a BFT quorum (quorum-intersection at an honest process,
  Li–Lesani / Malkhi–Reiter). The `BFTModel` carries the adversary budget as structure fields.
- **`cordial_agreement` / `cordial_agreement_from_lace`** (`Dregg2/Proof/CordialMiners.lean`) —
  over one `CordialState`: a wave anchors a single super-ratified leader, faithful to
  `blocklace/src/ordering.rs`; the lace-derived form reads the quorum off the real blocklace.
- **`finalLeaders_one_per_wave` / `finalLeaderAt_unique` / `tauOrder_deterministic`**
  (`Dregg2/Distributed/BlocklaceFinality.lean`) — over one `Lace`: a wave has ≤ 1 final leader;
  the finalized total order is a deterministic function of (lace, participants). This models the
  node's REAL `tau` rule (`computeRounds` / `findAllFinalLeaders` / `tauOrder`) executably, and
  ships a differential golden vector the Rust must reproduce.
- **`no_conflicting_finalized_history`** (`Dregg2/Consensus/Safety.lean` — **NEW**) — the
  CHAIN-LEVEL apex: two honest nodes holding DIFFERENT laces cannot finalize conflicting
  histories. See the next section.

### Chain consistency under growth — finalization is append-only (conditionally)
- **`tau_finalized_prefix_monotone`** (`Dregg2/Consensus/TauPrefixMonotone.lean`) — the finalized
  prefix is append-only UNDER `FinalizedRegionStable` (closed finalized region), with the
  unconditional claim REFUTED by an explicit honest-laggard counterexample. A soundness FINDING,
  not a clean win: the node's `executed_up_to` slicing is missing the stability check this names.

### Whole-history light client — the aggregate attests a FINALIZED history
- **`light_client_verifies_whole_history`** + the three-leg headline
  (`Dregg2/Distributed/FinalizedLightClient.lean`) — verifying aggregate + cert + binding attests
  a whole history that executed correctly AND was finalized by a supermajority.
- **`strand_single_tip` / fork-freedom invariants** (`Dregg2/Distributed/StrandIntegrity.lean`) —
  a fork-free strand has a unique tip; the verified write path preserves fork-freedom.

### Privacy — integrity under confidentiality
- **`Dregg2/PrivacyKernel.lean`, `Dregg2/Privacy.lean`, `Dregg2/InfoFlow/`** — the
  noninterference / sealed-value integrity surface. Integrity is proven; end-to-end
  *confidentiality* of the live PIR / sealed / private-voting paths is NOT yet an apex (below).

## The new chain-safety apex (`Dregg2/Consensus/Safety.lean`)

**The gap it closes.** Every consensus-safety theorem above this module fixes ONE lace or ONE
state. None states the property a light client's CHAIN-CHOICE rests on: that two honest nodes,
holding DIFFERENT partial laces, cannot finalize conflicting histories. `lightclient_unfoolable`
covers per-turn validity — it does NOT say which chain is canonical. This module lifts
"can't be fooled" from the TURN to the CHAIN.

**The honest observation that makes it tractable.** The proof of `cordial_agreement` never uses
that its two super-ratifications come from the SAME state — it consumes only the two ratifier
vote pools, the BFT model over their union, the honesty law, and id-determinism. So the
cross-node lift is a genuine generalization, not a re-proof.

- **§1 `quorum_pair_agreement`** — `bft_safety` generalized from one vote pool to two independent
  pools. Each node's `≥ n − f` quorum is monotone-lifted onto the union pool; the classical
  intersection then yields an honest participant in both, who ratified both blocks, so the
  honesty law collapses the ids.
- **§2 `cross_node_leader_agreement` / `_via_bft`** — two `CordialState`s, one wave, one leader.
- **§3 `cross_node_agreement_from_lace`** — the quorum is READ OFF each node's lace
  (`Committed`, via the existing `SuperRatification.ofLace`), not assumed.
- **§4 `no_conflicting_finalized_history`** — THE APEX: the two nodes' finalized histories are
  `Consistent` (never disagree on a common wave's leader) given the per-wave `CrossNodeWitness`.

Carriers (hypotheses, never axioms): honest majority / `n > 3f` (the `BFTModel` over the union
pool), the shared participant universe (one `Finality.Config`), id-determinism. Non-vacuity: the
§1 kernel fires on the minimal `n = 4, f = 1` config, and `Consistent` is two-sided (holds on
agreeing histories, FAILS on conflicting ones). `#assert_axioms`-clean.

**Named residual (a closure lane, not a faked step): `OPEN-CM-SUPERRATIFY-BRIDGE`.** Two parallel
finalization models exist — `Proof.CordialMiners` (the BFT algebra, where this apex lives) and
`Distributed.BlocklaceFinality` (the executable `tau` rule the node runs). They share the `n − f`
ratifier-count shape. Landing `no_conflicting_finalized_history` directly on the executable
`isSuperRatified` Bool is the next rung. Also inherited from the consensus floor: deriving that
the union pool actually meets the BFT threshold is the post-GST dissemination argument (the same
residual `BFT.lean`'s O2 names) — off the safety-critical path.

## Ranked next apexes (leverage × tractability)

1. **Close `OPEN-CM-SUPERRATIFY-BRIDGE`** — bridge the chain-safety apex onto the executable
   `BlocklaceFinality.tauOrder` / `isSuperRatified` the node actually computes. *Leverage:* high —
   turns the algebra-level apex into a statement about the running rule. *Tractability:* high —
   both models already carry the `n − f` ratifier-count shape; the bridge is a faithfulness
   lemma, not a new proof. **The immediate next step.**

2. **LIVENESS / progress** — currently NO unconditional consensus-liveness theorem exists.
   `BFT.gst_liveness_from_round_model` reduces the assumed oracle to Δ-delivery; the
   pacemaker/view-synchronization argument that a `GSTRound` eventually obtains is the open core
   (`Proof/BFTLiveness.lean`, `Proof/CordialMinersLiveness.lean`, `Proof/Synchronizer.lean` are
   the scaffolds). Statement: after GST, an honest turn submitted by an honest client is
   eventually finalized. *Leverage:* high — safety without liveness permits a silent halt.
   *Tractability:* medium — FLP-respecting, rests on a modeled pacemaker; genuinely large.

3. **executor = spec (`execute = recKExec`)** — `docs/RUST-LEAN-EXECUTOR-PARITY.md` is a
   DIFFERENTIAL (a tested trace agreement), not a theorem. The apex: the deployed Rust executor
   refines the Lean `recKExec` kernel on all inputs. *Leverage:* high — every other apex is about
   the kernel the node RUNS only as far as this holds. *Tractability:* low-medium — large surface;
   the realistic path is per-effect refinement rungs (the `RotatedKernelRefinement*` family is the
   circuit-side analogue) rather than one theorem.

4. **NODE correctness** — the `blocklace_sync` poll loop, `finality_gate` admission, and
   `executed_up_to` slicing as a refinement of the verified rule. `gate_admits_iff_verified_finalizes`
   (`Distributed/FinalityGate.lean`) already proves the gate admits exactly the verified set;
   the open piece is the slicing invariant the `TauPrefixMonotone` counterexample exposed.
   *Leverage:* medium-high. *Tractability:* medium — bounded, concrete, and partly a bug-fix.

5. **Distributed-protocol soundness beyond settlement** — branch-and-stitch / membrane
   conflict-resolution as event-structure refinements (`SettlementSoundness` is the proven anchor;
   `Distributed/` carries the surrounding lemmas). *Leverage:* medium. *Tractability:* medium.

6. **PRIVACY / confidentiality** — integrity under sealing is proven; end-to-end confidentiality
   of the live PIR / sealed / private-voting paths (an adversary learns nothing beyond the
   intended disclosure) is not yet an apex. *Leverage:* medium — distinct failure class (leakage,
   not forgery). *Tractability:* low — needs an indistinguishability / simulation framing the
   current integrity-flavored `InfoFlow` surface does not yet state.

The through-line: safety apexes (this constellation) rule out the adversary FORGING or
EQUIVOCATING; the open frontier is LIVENESS (the adversary STALLING) and the EXECUTOR=SPEC /
NODE refinements that tie every kernel theorem to the binary that runs.
