# Guide: The Distributed / SSB-Federation Model

*A newcomer's orientation to dregg's federation — the blocklace, strands (SSB feeds), finality, the
CRDT lace-merge, cell migration, and how the verified Lean models pin the live Rust consensus engine.*

See also: [`../NAVIGATION.md`](../NAVIGATION.md) ·
[`../rebuild/_FEDERATION-SSB-DESIGN.md`](../rebuild/_FEDERATION-SSB-DESIGN.md) (the blueprint) ·
[`../rebuild/_CAPTP-ORIENTATION.md`](../rebuild/_CAPTP-ORIENTATION.md).

---

## The one-sentence model

dregg's federation is **Secure-Scuttlebutt-on-crack**: a **blocklace** (a block-DAG-*lace*) where
each author's blocks form a **strand** (= that author's append-only SSB feed), blocks reference their
predecessors (the DAG = the causal history), and a Cordial-Miners-style wave protocol + Stingray
budget layer turn that DAG into BFT finality. dregg sits on the n>1 target — a single machine is the
degenerate scale-to-zero case, not a defer-excuse.

## dregg vs dreggrs here

The **live consensus engine is Rust** (`blocklace/`, `coord/`, `federation/`, `net/`). It is
**dreggrs** — heritage Rust kept as a fast executable shadow — and it is now **pinned by an
executable Lean model + golden differential** (`tau`). The **Lean is the truth**; the Rust is checked
against it. Almost every theorem below cites the Rust `file:line` it models. See
[`../rebuild/_DREGG-DREGGRS-MANIFEST.md`](../rebuild/_DREGG-DREGGRS-MANIFEST.md).

## The core objects (and where they're modeled)

| Object | Lean | What it is |
|---|---|---|
| **Lace** | `Dregg2/Distributed/*` (`Lace`, `Block`, `BlockId`) | the block-DAG; content-addressed (`Blocklace.blocks` HashMap keys). |
| **Strand** | `Distributed/StrandIntegrity.lean` (`Strand B p:61`) | the per-author feed projection — `p`'s sub-lace, the SSB feed. |
| **Constitution** | `Distributed/MembershipSafety.lean` (`Constitution:105`) | the amendable participant set + supermajority threshold. |

## 1. Finality — `BlocklaceFinality.lean`

The DAG-depth → wave → round-robin-leader pipeline (mirrors `ordering.rs`):

- `computeRounds B:87` / `roundOf:92` — the DAG-depth recurrence (`compute_rounds`).
- `supermajority_threshold` = `⌊2n/3⌋ + 1`.
- `finalLeaders_one_per_wave:332` — **at most one** final leader per wave (the safety core).
- `findAllFinalLeaders_deterministic:320` / `finalLeaderAt_unique:275` — determinism + uniqueness.

The **finality gate** (`Distributed/FinalityGate.lean`) connects this to admission:
`gate_admits_iff_verified_finalizes:187` — a turn is admitted iff it's genuinely finalized. The Rust
node's gate is `node/src/finality_gate.rs`.

## 2. Strand integrity (fork-freedom) — `StrandIntegrity.lean`

A strand is a *feed*: it must be fork-free (no two blocks at the same sequence number).

- `mem_strand_iff:65`, `strand_creator:70`, `strand_subset:74` — the projection laws.
- **`forkFree_iff_seqMonotone:138`** — fork-freedom ⟺ the sequence numbers are strictly monotone.
  This is the SSB "no feed forks" invariant, made a theorem.

Equivocation (a signed fork) is *detectable* — see `Exec/CapTPConsentLace.consent_equivocation_detectable:320`
and `signed_equivocator_consent_not_counted:415` (an equivocator's consent is not counted).

## 3. CRDT lace-merge (the join) — `LaceMerge.lean`

Merging two laces is a **semilattice join** (HashMap insert = key-union, skip-if-present):

- `mergeLace B Δ:103` = `B ++ newBlocks B Δ` (`finality.rs::merge`).
- **`laceIds_mergeLace:111`** — the keyset of a merge is exactly the set union (THE JOIN LAW).
- `merge_comm:138`, `merge_assoc:143`, `merge_idem:151`, `merge_absorb:157`, `merge_monotone:167` —
  the full commutative/associative/idempotent/monotone semilattice. This is why catch-up converges
  (`Distributed/CatchupConverges.lean`) regardless of delivery order.

## 4. Membership safety — `MembershipSafety.lean`

The constitution is amendable, and finality is *reparameterized* by membership changes:

- `computeThreshold n:99` = `⌊2n/3⌋ + 1` (with `n=0 ↦ 0`).
- `Constitution.new:115`, `isParticipant:121`, `Constitution.n:124`.
- `membership_change_reparameterizes_finality:486` — adding/removing a participant correctly shifts
  the threshold, so a stale quorum can't be replayed against the new constitution.

## 5. Cell migration across federations — `CellMigration.lean`

A cell can move between federations (n>1) carrying its transferable authority. The PREPARE/ACCEPT
two-phase artifacts (`Voucher:106`, modeling `cell/src/migration.rs::MigrationVoucher`) must
**conserve**:

- `handoff_conserves_balance:384` — balance preserved across the move.
- `handoff_conserves_caps:395` — the c-list (capabilities) preserved.
- `handoff_aggBalance_conserved:435` — aggregate balance over N cells conserved.

## 6. Joint / entangled turns (N-cell atomic) — `EntangledJoint.lean`

A turn can span multiple cells atomically (the cross-cell ⊗, a wide pullback over a shared `TurnId`):

- `jointApplyAll_atomic:162` — all-or-nothing across the leg set.
- `jointApplyAll_conserves:244` — N-ary conservation.
- `joint_sound_of_binding:490` — soundness from the shared-id binding.
- `entangleWith_monotone:329` — the entanglement graph grows monotonically.

This is the distributed face of the `Hyperedge` spec (`Dregg2/Hyperedge.lean`,
`hyperedge_sound` — the turn *is* the wide pullback; bilateral/ring/forest are incidences of one
object). Differential: `coord/src/entangled_diff.rs`.

## 7. Coordination & Stingray budget — `Dregg2/Coord/*`

The cross-epoch budget/spending-certificate layer (models `coord/`'s `budget.rs`):

- `Coord/StingrayCertReconcile.lean` — cross-epoch `rebalance` cert-reconciliation:
  `rebalance_version_strictly_increases` + `stale_cert_rejected` (epoch monotonicity / no-replay),
  quorum reconstruction with a Byzantine bound (`byzantine_undetected_overspend_le_f_ceiling`,
  ≤ f·ceiling undetected), under the named `CertUnforgeable` (Ed25519 EUF-CMA) portal. Differential
  `coord/src/coord_diff.rs::stingray_cert_reconcile_diff` drives a GENUINE `StingrayCounter` with
  REAL Ed25519 certificates.
- `Coord/{CausalOrder,TwoPhaseCommit,SharedBudgetDynamics}.lean` — the supporting laws.

## 8. The consensus theory — `Distributed/Consensus.lean` + `Proof/*`

dregg's resilience is modeled as a **PAIR, never a scalar** (Sridhar): a `ResiliencePair` over a
`Finality.Config`, with `dreggDeployment` = sleepy validators + sleepy clients (the four-coordinate
client/network model). `dreggResilience` (`cfg = ⟨n=4, f=1, q=3⟩`) is the concrete non-vacuity
witness. The deeper proofs:

- `Proof/CordialMiners.lean` + `CordialMinersLiveness.lean` — the DAG protocol dregg actually runs.
- `Proof/Stingray.lean` — the budget/settlement layer.
- `Proof/BFT.lean` + `BFTLiveness.lean`, `Proof/{GST,Synchronizer}.lean` — quorum intersection,
  post-GST liveness (under the honest `World.gst_liveness` oracle law).

Grounding papers: [`../rebuild/CONSENSUS-GROUNDING.md`](../rebuild/CONSENSUS-GROUNDING.md) (Sridhar
resilience pair + Wong taxonomy).

## 9. Crash / checkpoint / catch-up / epoch

- `Distributed/CrashRecovery.lean` — replay = checkpoint ⊕ overlay (`persist/`).
- `Distributed/CheckpointPrune.lean` — a checkpoint below a finalized height is discardable.
- `Distributed/CatchupConverges.lean` — sync convergence (the lace-merge semilattice makes order
  irrelevant); `node/src/catchup.rs`, `blocklace_sync.rs`.
- `Distributed/EpochReconfig.lean` — epoch reconfiguration.

## 10. Threshold decryption / BLS QC

`Distributed/ThresholdDecrypt.lean` (differential `federation/src/threshold_decrypt_diff.rs`) +
`Distributed/BlsQuorumCert.lean`. The BLS12-381 / KZG *curve math* (`hints/`) is a justified
imported crypto-primitive residual — not dregg protocol semantics (same class as the Ed25519 /
Poseidon floors).

## The node (devnet) — `node/src/`

The runnable federation node: `main.rs`, `genesis.rs`, `config.rs`, `executor_setup.rs` (executes
through the Lean shadow), `finality_gate.rs`, `blocklace_sync{,_checkpoint}.rs`, `catchup.rs`,
`gossip.rs`, `api.rs`. The `net/` crate provides QUIC + Plumtree gossip *delivery* (infra); the
causal-ORDER invariant (the lace = the causal DAG) is the dregg-covered part.

## Where to start reading

1. [`../rebuild/_FEDERATION-SSB-DESIGN.md`](../rebuild/_FEDERATION-SSB-DESIGN.md) — the blueprint.
2. `Dregg2/Distributed/StrandIntegrity.lean` — the SSB-feed core (small, readable).
3. `Dregg2/Distributed/LaceMerge.lean` — the CRDT join (why catch-up converges).
4. `Dregg2/Distributed/BlocklaceFinality.lean` — finality.
