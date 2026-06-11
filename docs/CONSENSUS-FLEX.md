# CONSENSUS-FLEX — consensus on demand

**Status:** investigation report + design proposal (2026-06-11, consensus-flexibilization
lane). Sections titled **DESIGN** are proposals; everything else is present-tense
description of what exists, with file:line. Companion Lean feasibility note:
`metatheory/Dregg2/Consensus/OnDemandFeasibility.lean` (the afternoon-sized theorem,
proved; the wave/epoch obligations stated as named interfaces).

**The thesis.** Total order (tau) is a special case the system overpays for. The
blocklace gives causal order free; the I-confluence classifier prices which operations
actually conflict. Most turns are single-cell and commute — they could finalize at
causal acknowledgment depth (the fast path); only contended operations (same-well
debits, council certifications, same-cell writes, revocation-vs-exercise) need tau.
*The lace is the truth; tau is one linearization you call when you contend.*

The striking finding of this read: **the system already states this thesis to itself,
in three places, and then doesn't act on it.** The four-tier finality ladder exists and
is proved (`Dregg2/Finality.lean`); the I-confluence classifier exists and is proved
non-vacuous (`Dregg2/Confluence.lean`); the contended/commuting dichotomy is proved at
both poles (`Dregg2/Proof/ContendedCrossCell.lean`); and DREGG3 §8 closes with "a
confluence-stable guard runs coordination-free; one that isn't forces ordering
(consensus)" (`docs/DREGG3.md:379-383`). But the running node implements exactly ONE
tier for n>1 — everything waits for tau — and no Rust code consults the classifier
(grep over `node/`, `coord/`, `turn/` for Tier1/IConfluent: zero hits). The work is
not to invent consensus-on-demand; it is to weld the already-proved judgement into the
finality path.

---

## 1. What exists — the finality machinery

### 1.1 The tier ladder (Lean, abstract, proved)

`Dregg2/Finality.lean` defines the pluggable per-cell finality tier:

* `Tier` = `causal | ackThreshold | bft | constitutional` (`Finality.lean:29-46`),
  a `LinearOrder` by `rank` (`:76-88`).
* `Tier.causal` is documented "Eligible ONLY for I-confluent state
  (`Confluence.Tier1Eligible`)" (`:32`); `Tier.ackThreshold` is "k-of-m
  acknowledgements, leaderless; under partition it degrades to tier 1" (`:34-37`);
  `Tier.bft` is Cordial-Miners tau-BFT (`:38-41`).
* `Selector.groupTier : Group → Tier` (`:155-164`) — the per-reference-group finality
  dial already exists as a model object; `tau_unified` resolves a group to its rule
  (`:164`).
* `tier1_requires_iconfluent` (`:181-191`) — the static gate: a cell may run the
  causal rule only if the classifier certifies its invariant I-confluent.
* `crossTierJoin = max` (`:196`) and `commit_at_join_of_tiers` (`:214-237`) — a turn
  touching cells of several tiers commits at the **join (max)** of their tiers; no
  effect released until the join-tier rule commits. This is exactly the
  cross-tier rule a per-cell dial needs, already proved.
* `no_downgrade` (`:254-262`) — finality strength is monotone along any run.
* `conservation_tier_independent` (`:305-309`) — re-tiering a cell cannot change the
  conservation verdict (the two judgements are orthogonal, proved by `rfl`).

Stale-header note (rise-to-meet-the-claim): `Finality.lean:13-14` still says "genuine
distributed-agreement obligations are honest `Prop`s with `sorry` bodies" — the body
contains **no** sorry (the obligations were since discharged or restructured). The
header should be corrected.

### 1.2 The classifier (Lean, proved, runtime-absent)

`Dregg2/Confluence.lean` is the I-confluence judgement (BEC Thm 3.1):

* `IConfluent I := ∀ x y, I x → I y → I (x ⊔ y)` over a `MergeState`
  join-semilattice (`Confluence.lean:33-34`).
* `Tier1Eligible I := IConfluent I` (`:40-41`) — tier-1 eligibility IS I-confluence.
* `nonpairwise_escalation` (`:54-64`) — non-I-confluence yields a concrete clashing
  pair; escalation to consensus is forced by counterexample, not declared.
* Non-vacuity both ways: grow-only is I-confluent (`top_iconfluent`, `:76`);
  "at most one element" / the `balance ≥ 0` shape is not
  (`cardLeOne_not_iconfluent`, `:83-87`).

`Dregg2/Coordination.lean` lifts it to choreography steps: `StepEffect` (`:391-394`)
and `iconfluent_fragment_crossgroup_free` (`:415-423`) — an I-confluent step runs
cross-group, partition-tolerant, no atomic commit; a coupled (Σ=0 settlement) step
must block.

**The dichotomy is proved at both poles** in
`Dregg2/Proof/ContendedCrossCell.lean`: `contended_commits_confluent` (two contending
cross-cell turns that debit *disjoint* source cells commit in either schedule order to
the SAME final ledgers — schedule-agnostic confluence) and
`coupled_no_schedule_agnostic_commit` (two turns contending for the same balance that
funds only one: two adversary schedules whose committed states DISAGREE; no
deterministic local rule picks the winner without consensus). The classifier for the
dichotomy is literally `Confluence.IConfluent` over the contended invariant (header,
`ContendedCrossCell.lean:1-40`).

**Where the classifier lives at runtime: nowhere.** No Rust in `node/`, `coord/`,
or `turn/` mentions tier-1/I-confluence. The judgement is a static Lean fact with no
descriptor field, no executor consultation, no finality-path branch.

### 1.3 The blocklace finalization rule (tau) and what the node waits for

`Dregg2/Distributed/BlocklaceFinality.lean` is the faithful executable model of
`blocklace/src/ordering.rs::tau`:

* `computeRounds` (`:87-89`), wave arithmetic + round-robin `waveLeader` (`:100-113`),
  `causalPastIncl` (`:135`), `hasEquivInPast` (`:143-151`), `approves`/`ratifies`/
  `isSuperRatified` (`:155-182`), `finalLeaderAt`/`findAllFinalLeaders` (`:209-221`),
  `tauOrder` (`:249-259`).
* Safety: `finalLeaderAt_unique` (`:275`), `finalLeaderAt_needs_unique_candidate`
  (the anti-equivocation tooth, `:286`), `tauOrder_deterministic` (`:311`),
  `finalLeaders_one_per_wave` (`:332`).
* The executor wire: `executeTau` folds the verified `executeFinalized`
  (= `recCexec`) over the tau order (`:364-366`); `tau_drives_verified_run` (`:374`)
  and `tau_execution_agreement` (`:387`) — same lace ⇒ same executed state.

`Dregg2/Distributed/FinalityGate.lean` exports the verified rule to the node:
`@[export] dregg_blocklace_finalize` (`:166-167`, the `(creator, seq)` projection)
and `@[export] dregg_tau_order` (`:290-291`, the full ordered `BlockId` list), with
`gate_admits_iff_verified_finalizes` (`:187-191`) and `tau_order_export_eq`
(`:309-313`) proving the exports ARE the verified rule.

**What the node actually waits for** (`node/src/blocklace_sync.rs::poll_finalized_blocks`,
`:510`):

* **n = 1 (solo):** every actionable block is immediately finalized in seq order
  (`:546-559`) — tau is bypassed; scales-to-zero.
* **n > 1:** the authoritative order is the verified Lean `dregg_tau_order`
  (`:561-639`; Rust `tau` is the differential sibling, divergence logged loudly,
  Lean wins). A secondary projection gate re-checks each actionable block against
  `dregg_blocklace_finalize` and STOPS the committed prefix at the first refusal
  (`:642-712`). Then `ordered[executed_up_to..]` is sliced to the executor.
* Wavelength is pinned to 3 (`node/src/finality_gate.rs:43`). So a turn at n>1 is
  final only when its block lies in the **coverage of a super-ratified wave leader**:
  the leader's slot block must exist uniquely at the wave-start round and a
  supermajority of distinct participants must have wave-end blocks ratifying it
  (`BlocklaceFinality.lean:175-221`). Finality latency ≈ a full wave (3 rounds) plus
  ratification — **every turn pays this, including a single-cell grow-only write that
  commutes with everything.** That is the overpayment the thesis names.

**Equivocation handling on the live path:** feed integrity (sig + seq monotonicity +
equivocation detection) is enforced at `insert` on the source lace (the A1 fix,
modeled in `Dregg2/Distributed/StrandIntegrity.lean:1-50`); the ordering projection
rebuilds unsigned skeletons via `insert_unverified` because integrity was already
discharged (`blocklace_sync.rs:855-864`). Detected equivocators are auto-evicted from
the constitution without a vote and the relaying peer is penalized at the gossip layer
(`blocklace_sync.rs:1341-1368`; `constitution.rs::auto_evict`, modeled in
`Dregg2/Distributed/MembershipSafety.lean`).

### 1.4 The causal substrate (free order)

* `Dregg2/Coord/CausalOrder.lean` — the coordination-layer happened-before DAG
  (`types/src/causal.rs::CausalDag`): `happenedBefore` is the transitive closure of
  dependency edges (`:249-253`), proved a strict partial order on well-formed DAGs
  (`hb_irrefl :347`, `hb_trans :364`, `hb_asymm :373`), with insertion order a linear
  extension (`hb_imp_index_lt :387`).
* `Dregg2/Distributed/LaceMerge.lean` — the replication merge is a pure join on the
  content-addressed keyset: `laceIds_mergeLace` (`:111`), commutativity/associativity/
  idempotence/monotonicity (`:138-173`), least-upper-bound (`:179`), and the
  end-to-end **convergence theorem** `merge_convergence_to_state` (`:297-315`): two
  replicas that merged the same causally-closed blocks execute to the same
  `RecChainedState` (modulo the named `hOrder` permutation-invariance residual,
  `:249-261`).

So causal order + CRDT convergence are already verified property of the substrate.
The fast path does not need new dissemination machinery — only a new *finality
predicate* over the structure the lace already carries.

### 1.5 A named gap found during this read (report-and-close lane)

`BlocklaceFinality.lean:52-53` claims the module proves `finalized_prefix_monotone`
("finalization is append-only"). **The theorem does not exist** — not in that file,
not anywhere in the tree (grep: the only hit is the header sentence). Meanwhile the
node RELIES on exactly this property: `executed_up_to` slicing assumes the finalized
order only appends (`blocklace_sync.rs:660-661` says "tau's finalized prefix is
monotone" in prose). This is simultaneously (a) an honesty gap to close in the header
or by proving the theorem, and (b) the **no-rollback keystone of the fast path** (§4,
T5). It is the highest-leverage single theorem in this whole design.

---

## 2. DESIGN — the conflict relation, precisely

### 2.1 The definition

Let `step : S → Turn → S` be the (fail-closed, deterministic) executor application
(concretely `recKExecAsset`-into-`Option`, totalized by refusal-as-identity on the
committed state). Define:

```
Commute t₁ t₂  :=  ∀ s, step (step s t₁) t₂ = step (step s t₂) t₁
t₁ ⊥ t₂        :=  ¬ Commute t₁ t₂            -- the semantic conflict relation
```

This is the trace-monoid (Mazurkiewicz) independence relation, instantiated at the
verified executor. The semantic relation is undecidable in general; the classifier is
a **syntactic over-approximation** computed from footprints:

```
footprint(t) = writes(t)   ⊆ (CellId × Slot)            -- write
             ∪ wells(t)    ⊆ (CellId × AssetId × sign)   -- move (debit/credit)
             ∪ caps(t)     ⊆ (CellId × epoch-register)    -- grant/revoke
             ∪ nulls(t)    ⊆ Nullifier                    -- unshield
             ∪ life(t)     ⊆ CellId                       -- lifecycle bit
reads(t)     = the admission read-set: every slot/epoch/balance/lifecycle register
               the turn's Pred/caveat evaluation or precondition inspects
```

**Classifier rule (sound side):** `t₁`, `t₂` are declared independent (fast-eligible
as a pair) iff their footprints∪reads intersect ONLY on monotone (∪-shaped,
I-confluent) registers. Any overlap on a non-monotone register — a bounded well, an
epoch register read by admission, a non-CRDT slot, a lifecycle bit, a shared
nullifier — is a conflict. The read-set matters: E2 of the Fpu probe proved the
camera is blind to guards (`docs/DREGG3.md:80-83`), so the guard's reads are a
separate, mandatory footprint contribution.

### 2.2 Enumeration against the 8 verbs

The verb surface is reified in `Dregg2/Substrate/VerbRegistry.lean` (`Verb`,
`:94-108`; the live 27-tag `EffectTag` and its total `classify`, `:214-270`). Per
ordered pair (symmetric; same-cell unless said otherwise):

| pair | verdict | why |
|---|---|---|
| `create × create` | commute | fresh content-addressed identities; no shared register (factory nonce is per-sender prologue, see strand note below) |
| `create × *` | commute | a fresh cell shares no register with any pre-existing footprint |
| `write × write`, same `(cell, slot)` | **conflict** | last-writer-wins is order; unless the slot is declared CRDT/monotone (grow-only set, max-register) — then commute |
| `write × write`, disjoint slots | commute | the frame rule (DREGG3 §2.1: disjoint frames commute) |
| `write × read-of-that-slot` (any verb whose Pred reads it) | **conflict** | admission verdict flips with order |
| `move × move`, same well, both debits | **conflict** | `balance ≥ 0` is THE canonical non-I-confluent invariant (`Confluence.lean:6`); two concurrent debits merge to overdraft; the proved impossibility pole (`coupled_no_schedule_agnostic_commit`) |
| `move × move`, same well, both credits | commute | addition commutes; credit is monotone |
| `move × move`, debit × credit same well | **conflict** (conservatively) | the debit's funding check reads the balance the credit raises; order changes refusal. (A declared-overdraft-impossible well could relax this; not free.) |
| `move × move`, disjoint wells | commute | the proved confluent pole (`contended_commits_confluent`) |
| `grant × grant`, same grantor | commute | production appends to the clist (sorted-Merkle set insert = ∪-shaped); non-amp checks read the grantor's HELD set, which neither grant shrinks |
| `grant × revoke`, same lineage/epoch register | **conflict** | grant-then-revoke ≠ revoke-then-grant: the granted child's `stored_epoch` vs the bumped epoch (R7, `docs/DREGG3.md:290`) |
| `revoke × revoke` | commute | epoch bumps compose (two increments in either order reach the same epoch; staleness verdicts depend only on the final value at retrieval) |
| `revoke × ANY exercise under the revoked authority` | **conflict** | the central one. Exercise-then-revoke succeeds; revoke-then-exercise refuses (the `stored_cap_only_fresh_if_epoch_unrevoked` tooth, `Dregg2/Apps/CapSlotFactory.lean`). A concrete two-line non-commuting witness is the NEG pole of the feasibility note (§4). |
| `shield × shield` (NoteCreate) | commute | commitment-set insert; grow-only — `top_iconfluent` shape |
| `unshield × unshield`, same nullifier | **conflict** | "spent ≤ once" is a `card ≤ 1`-shaped invariant (`cardLeOne_not_iconfluent`, `Confluence.lean:83`): each spend valid alone, the merge is a double-spend |
| `unshield × unshield`, distinct nullifiers | commute | disjoint inserts into the nullifier set (`Exec/RecordKernel.lean:316-317`) — note the value-credit side must also land in disjoint wells |
| `lifecycle × ANY`, same cell | **conflict** | seal/destroy/make-sovereign flips the admissibility of every other verb on the cell; order is semantics |
| `lifecycle × *`, different cells | commute | frame |

**The strand discount (free serialization).** Turns by the SAME sender are already
totally ordered by the strand discipline — per-creator seq is strictly monotone and
fork-free at the insert gate (`StrandIntegrity.lean`, the A1 fix). So the conflict
relation only ever needs adjudication between turns of *different* senders; a sender
never contends with itself, and the nonce prologue (`IncrementNonce`, a
turn-structure tag, `VerbRegistry.lean:265`) is not a conflict source.

**Always slow (structurally contended):**

* **Council certifications / constitution proposals** — vote tallying reads a global
  count against a threshold (`MembershipSafety.lean` `hasPassed`; `constitution.rs:336-346`);
  whether the k-th vote passes the proposal depends on every prior vote: maximally
  order-sensitive.
* **Cross-cell atomic turns** (`Distributed/EntangledJoint.lean` N-cell 2PC;
  the live gate `node/src/coord_gate.rs` makes the verified
  `dregg_coord_2pc_decide` authoritative) — all-or-none over several cells is a
  canonicity demand by construction; the impossibility pole applies whenever the legs
  contend.
* **Epoch/validator reconfiguration** — see §5.

---

## 3. DESIGN — the fast path and the slow path

### 3.1 The fast path: finality at causal acknowledgment depth

For a block `b` in lace `B`, define (pure function of the existing structure — no new
wire messages):

```
ackers B b   := { p ∈ participants | ∃ block o of creator p, b ∈ causalPastIncl B o.id
                                      ∧ ¬ hasEquivInPast B o.id b.creator }
ackDepth B b := |ackers B b|
```

This is exactly the `approves`-shape `BlocklaceFinality.lean:155-156` already
computes for leaders, applied to an arbitrary block. **The acks are free**: every
gossiped block acknowledges its whole causal past; tier-2 finality is a threshold
*read* of structure the lace already carries.

* **Fast rule (tier ≤ ackThreshold):** a turn classified all-commuting (its footprint
  conflicts with no concurrent un-finalized turn, per §2) is FINAL when
  `ackDepth B b ≥ k` with `k = superMajority n` (`= 2n/3 + 1`,
  `BlocklaceFinality.lean:98`). Expected latency: one gossip round-trip (everyone's
  next block acks it), vs a full wave + ratification for tau.
* **Slow rule (tier ≥ bft):** unchanged — the verified `dregg_tau_order` path.
* **Contention escalation:** if the classifier detects a conflicting concurrent turn
  (footprint intersection on a non-monotone register with another un-finalized
  block), BOTH turns are demoted to the slow path; tau adjudicates the order. This is
  `nonpairwise_escalation` (`Confluence.lean:54`) operationalized.
* **Per-cell dial:** the cell's declared tier (§6) caps how fast its turns may
  finalize; the cross-tier join rule (`commit_at_join_of_tiers`) governs multi-cell
  turns.

### 3.2 Executor change (the honest size of it)

Today the executor consumes ONE cursor (`executed_up_to`) over ONE total order. The
fast path needs two frontiers: the causally-applied fast set and the tau-committed
prefix, with the invariant that the final state equals the tau-order fold. That
invariant is exactly the convergence theorem (§4, T3): it is what *licenses* the
executor to apply fast turns before tau places them. This is the epoch-sized part of
the engineering (state management, receipts annotated with the finality mode in Q,
re-execution-free reconciliation when the tau slice arrives).

### 3.3 Why `k = superMajority` and not less

Quorum intersection (the same arithmetic as `EpochReconfig.quorums_intersect`,
`EpochReconfig.lean:110-115`): two conflicting blocks cannot BOTH gather
supermajority ack-sets without a common honest acker, and an honest acker's blocks
ack at most one of a conflicting pair (its causal past is downward-closed and the
equivocation guard `hasEquivInPast` refuses forks). This is what makes fast-finality
a finality and not an optimism: a fast-final turn can never be contradicted by a
competing fast-final turn. Its compatibility with *tau* is T5/T6 below.

---

## 4. The soundness theorems

**T1 — linearization agnosticism on commuting sets (PROVED, afternoon).**

> For `step : S → T → S`, a list `l` of turns pairwise commuting under `step`, and
> any permutation `l' ~ l`: `l.foldl step s = l'.foldl step s`.

Lean: `Dregg2.Consensus.OnDemandFeasibility.fastpath_linearization_agnostic`
(rides `List.Perm.foldl_eq'`). Corollary `tau_agrees_with_any_causal_order`: ANY two
linearizations of a commuting block set — the tau one and any causal-ack one — fold
to the same state. This is the precise form of "any tau linearization agrees with the
fast path on commutative prefixes," at the all-commuting pole. The NEG pole
(`revoke_exercise_noncommuting`) witnesses that the hypothesis is load-bearing.

**T2 — frame ⇒ commute for the real executor (wave).**

> For turns `t₁ t₂` with `(footprint ∪ reads)(t₁) ∩ (footprint ∪ reads)(t₂)`
> containing only monotone registers: `Commute recKExecAsset t₁ t₂`.

Stated as the `FrameCommutes` interface in the feasibility note. The reference
instance at the JointCell kernel is already proved
(`ContendedCrossCell.contended_commits_confluent`); lifting it to the full
`RecordKernelState` (19 fields, side-tables) is a real but mechanical wave: a frame
lemma per verb. The chained corollary (T2 + T1 ⇒ pairwise-disjoint turn lists are
linearization-agnostic) is proved generically in the note
(`frame_fastpath_sound`).

**T3 — trace convergence (the crown; epoch).**

> Let `≼` be happened-before on lace `B`, `⊥` the conflict relation. For any two
> linear extensions `ℓ₁, ℓ₂` of `≼` that agree on the relative order of every
> `⊥`-pair: `ℓ₁.foldl step s = ℓ₂.foldl step s`.

The Mazurkiewicz-trace generalization of T1 (T1 is the empty-`⊥` case). Wired to the
real objects: instantiate `ℓ₁ := tauOrder B P w` (a linear extension of `≼` —
`xsortBy` respects rounds, `BlocklaceFinality.lean:241-246`) and `ℓ₂ :=` the fast
path's causal application order. The theorem then says: the fast path commutes with
tau on everything except `⊥`-pairs, which both paths order identically (because
`⊥`-pairs are demoted to tau by the escalation rule). Composes with
`LaceMerge.merge_convergence_to_state` (`LaceMerge.lean:297`) to give cross-replica
agreement: same blocks ⇒ same keyset ⇒ same view ⇒ same fast verdicts (ackDepth is a
function of the causal past) ⇒ same state.

**T4 — fast-verdict determinism (afternoon, rides existing proofs).**

> `ackDepth` is a deterministic function of `(B, participants)`; two replicas with
> `SameView B₁ B₂` (`LaceMerge.lean:198`) compute equal `ackDepth` for every block.

Same shape as `tauOrder_deterministic`; trivial-as-Lean, load-bearing as statement.

**T5 — finalized-prefix monotonicity (wave; ALSO closes the §1.5 gap).**

> If `laceIds B ⊆ laceIds B'` (both canonical, content-agreeing), then
> `tauOrder B P w` is a prefix of `tauOrder B' P w` at the super-ratified-wave
> granularity (a finalized wave's segment never changes as the lace grows).

Currently *claimed* in the `BlocklaceFinality.lean:52` header and *relied on* by
`executed_up_to` slicing (`blocklace_sync.rs:660-661`), but proved nowhere. Without
it neither the existing node nor the fast path has no-rollback. The proof shape: a
super-ratified leader stays super-ratified under lace growth (ratification counts
are monotone in the block set), and `leaderCoverage` of earlier waves is closed
(causal pasts don't grow for fixed blocks). Estimated: one focused wave.

**T6 — fast-final ⊆ eventually-tau-final (wave, after T5).**

> If `ackDepth B b ≥ superMajority |P|` and `b`'s creator never equivocates in any
> extension `B' ⊇ B` visible to a correct replica, then `b ∈ tauOrder B' P w` for
> every sufficiently grown `B'` (every future super-ratified leader's coverage
> includes `b`).

The bridge from the ack quorum to tau membership: a supermajority of strands carry
`b` in their causal past, so any future wave-end ratifying set (itself a
supermajority) intersects them; the final leader's coverage (union of ratifiers'
causal pasts, `leaderCoverage`, `BlocklaceFinality.lean:232-239`) therefore contains
`b`. The honest caveat is the equivocation hypothesis: tau EXCLUDES blocks of
later-discovered equivocators (`tauOrder`'s `hasEquivInPast` filter, `:254-257`),
so a fast-final turn by a creator who *later* reveals a fork could be dropped by tau.
Resolution options, in honesty order: (a) restrict the fast path to turns whose
value effects are recoverable-by-slash (the evidence object, §7, pays for the
rollback), (b) make fast-finality of `b` ALSO require `ackers` saw no fork
(already in the `ackers` definition above — then a fork revealed later means the
equivocator fooled a supermajority, which the quorum-intersection argument bounds to
"cannot produce a CONFLICTING fast-final block", leaving only an excluded-but-final
orphan whose effects the slash covers), or (c) keep equivocator-funds rollback as
the one named non-monotonicity, surfaced in Q. Option (b)+(a) together is the
designed answer.

---

## 5. DESIGN — consensus governed by the polis

### What exists

Two DISJOINT membership mechanisms, each verified, neither owning the other (stated
explicitly in `EpochReconfig.lean:8-16`):

1. **Blocklace constitution** (`blocklace/src/constitution.rs`, modeled in
   `Dregg2/Distributed/MembershipSafety.lean`): continuous governance — Join/Leave/
   expel proposals, the H-rule `max(T, T')` for threshold amendments, distinct-
   current-member quorums counted over the causal past, equivocator auto-eviction
   without a vote. This is the participant set tau actually round-robins over
   (`poll_finalized_blocks` reads `constitution.current.participants`,
   `blocklace_sync.rs:512-513`, filtered by the verified strand-admission gate,
   `:516-531`).
2. **Federation epoch reconfiguration** (`federation/src/epoch.rs`, modeled in
   `Dregg2/Distributed/EpochReconfig.lean`): batched, attested handoff —
   `verifyTransition` (`:259-270`) demands an old-epoch quorum of valid signatures,
   sequential epoch numbers, well-formed delta, correctly recomputed threshold;
   `epoch_handoff_no_gap` (`:372-388`) is the crown (authority continuously
   attested across the boundary); `quorums_intersect` (`:110`) forbids forked
   reconfiguration.

The amendment machinery on the CELL side exists as patterns: `councilBound`
(`Dregg2/Exec/Program.lean:842` — `anyOf [immutable f, senderIs k]`, the per-slot
council approval binding, with `#guard` teeth `:845-854`); `TemporalGate` (a
time-window `StateConstraint`, `turn/src/executor/mod.rs:252-257`, modeled at
`CatalogInstances.lean:140`) — the cooling-period primitive; and the
committee-amendment refusal teeth in `Apps/GovernedNamespaceGated.lean:142,245`
(amending the committee root without the committee's own quorum ⇒ `none`).

### The mapping: membership AS a constitution cell

Reconfig = amendment means: the federation's participant set, threshold, and epoch
live as slots of a distinguished **constitution cell**; a membership change is an
ordinary `write` turn whose admission Pred encodes the existing verified rules:

* H-rule + distinct-member quorum → a relational Pred over the vote-tally slots
  (needs DREGG3 §8 axis-1: record-level relational guards — the same closure the
  queue probe demanded);
* cooling → `TemporalGate` over receipt-chain height / wave number;
* equivocator eviction → the evidence-verified Pred atom of §7 (eviction = a write
  to the participant slot, admissible on presented `EquivocationProof`);
* epoch handoff attestation → `witnessed(vk)` whose verifier is
  `verifyTransition`'s signature/quorum check (already an executable Lean predicate).

### The seams (named honestly)

1. **The feedback edge does not exist.** Today information flows
   consensus → executor only (tau slices turns in). Membership-as-a-cell requires
   the finalized STATE of one cell to flow BACK into tau's `participants` argument
   for subsequent waves. That is a new, carefully-staged wire: "the participant set
   for wave w+Δ is the constitution cell's slot value as of the last finalized
   checkpoint ≤ w" — Δ is the cooling period, and the staging is what prevents a
   self-amending order-dependency loop (the amendment takes effect only at a wave
   boundary strictly after its own finalization — exactly the epoch.rs batching,
   re-derived as a TemporalGate).
2. **Two sources of truth.** constitution.rs and epoch.rs must collapse to one
   (the cell), or one must become a verified projection of the other. Today
   neither subsumes the other by their own headers' admission.
3. **Identity binding.** Blocklace creators are strand keys (`[u8;32]`); cells have
   operators. Membership-as-a-cell needs the strand-key ↔ cell-operator binding to be
   a kernel-legible fact (today it lives in node-side config).
4. **Self-reference floor.** The constitution cell's own writes are finalized by the
   committee the cell defines — fine with the wave-boundary stagger (1), but the
   genesis/bootstrap and the "committee expels a majority of itself" corner need the
   H-rule's max() discipline lifted to the cell program verbatim
   (`MembershipSafety.requiredVotes_amend_ge_both` is the theorem to preserve).

Verdict: the *theorems* mostly exist (EpochReconfig + MembershipSafety are the
amendment safety, already proved); the work is plumbing (the feedback edge) and the
relational-guard closure it presupposes. Epoch-sized, and it should ride AFTER the
guard-algebra uplift (DREGG3 §8), not before.

---

## 6. DESIGN — per-cell finality dials

**Where Hosted/Sovereign lives:** `cell/src/cell.rs:13-15` (`CellMode::Hosted |
Sovereign`); `MakeSovereign` is a lifecycle verb (`VerbRegistry.lean:262`);
cross-federation custody handoff is `Dregg2/Distributed/CellMigration.lean`
(prepare/accept/commit with no-double-existence). The mode is a custody dial; the
finality dial is its natural sibling.

**The field.** Add `finalityTier : Tier` to the cell record (Lean `Tier` already
exists, `Finality.lean:29`; Rust mirror next to `mode`). Semantics:

* **Executor:** a turn's commit tier = `foldr crossTierJoin` over the tiers of every
  cell in its footprint (`commit_at_join_of_tiers` is the already-proved rule,
  `Finality.lean:214`); effects (receipt release, Q emission as "final") are held
  until the join-tier rule reports committed.
* **Classifier coupling:** declaring `Tier.causal` (or `ackThreshold`) at
  `create`/factory time is admissible only if the cell's program/invariant passes
  the static I-confluence check — `tier1_requires_iconfluent` (`Finality.lean:181`)
  becomes a factory-descriptor obligation, checked where descriptors are already
  checked. A `balance ≥ 0` well cannot declare causal; a grow-only registry can.
* **No-downgrade:** re-tiering a cell upward is a `lifecycle`-class write; downward
  re-tiering of already-finalized history is forbidden by `no_downgrade`
  (`Finality.lean:254`) — operationally, a tier change applies only to turns after
  its own finalization (same stagger as §5).

**The n=1 collapse (ember's single-machine principle).** Already exhibited by the
node: at n=1 `poll_finalized_blocks` finalizes everything immediately in seq order
(`blocklace_sync.rs:546-559`) — all four tiers degenerate to the same behavior, the
dial is free, and nothing about the design depends on n>1 to be *correct* (only to
be *useful*). The dial's honest reading: tiers are DISTRIBUTED bounds that collapse
to strong local properties at n=1 — consistent with the dregg4 single-machine note.

---

## 7. DESIGN — evidence-carrying turns (equivocation → slashing via ordinary verbs)

**What exists.**

* Detection: `Blocklace::detect_equivocation` returns
  `EquivocationProof { creator, block_a, block_b }`
  (`blocklace/src/finality.rs:181-186, :813-840`). The Lean fact:
  `Equivocation B p a b` (incomparable distinct same-creator pair,
  `Authority/Blocklace.lean:137-153`) with `equivocation_detectable` (`:171-180`)
  — the proof object is IN the lace, checkable by anyone.
* Consequence today: constitution auto-evict (no vote) + gossip-layer relay penalty
  (`blocklace_sync.rs:1341-1368`); the comment at `:1366-1368` says the block "is
  still retained as slashable evidence" — but **no slashing path exists**; the
  evidence dead-ends at the membership layer.

**What's missing for evidence as a first-class kernel object** (in dependency
order):

1. **A canonical evidence value.** Wire-codec'd
   `EvidenceOfEquivocation = (header_a, header_b, sig_a, sig_b)` where the headers
   carry `(creator, seq/round, id, preds-root)` — small, self-contained, verifiable
   without the lace (two sig checks + same-creator + same-slot + distinct-id). The
   `EquivocationProof` struct is this minus signatures-as-carried and minus a codec.
2. **The verification Pred atom.** A `witnessed(vk)`-style atom (or one curated
   kernel atom) `validEquivocation(ev, strandKey)` — cheap to check (verify/find
   asymmetry: verification is two Ed25519 checks and three equalities). This is the
   ONLY new kernel-adjacent piece.
3. **The bond cell.** A factory-born escrow (the R3 escrow factory, landed per
   `DREGG3.md` R3) holding the participant's stake, whose program releases
   `move`(bond-well → reporter/pot) on a turn presenting valid evidence against the
   bonded strand key. Slashing is then literally an ordinary `move` under an
   ordinary Pred — no new verb.
4. **The identity binding** (shared with §5 seam 3): strand key ↔ bond-cell, so the
   evidence names a slashable owner.
5. (For the fast path, §4 T6 option (a)): the slash amount must dominate the maximum
   fast-finalizable value per wave — an economics parameter, not a kernel fact;
   `Distributed/Economics.lean` is the natural home for the bound.

This also upgrades equivocation handling from "membership penalty" to "priced
deterrent", which is what makes T6's residual honest.

---

## 8. Honest costs — where consensus-on-demand breaks

* **Cross-cell atomic turns** (EntangledJoint, the 2PC coordinator): slow path,
  always. The impossibility is machine-checked
  (`coupled_no_schedule_agnostic_commit`); no design wriggle.
* **Anything reading contended state.** The read-set is part of the footprint; a
  fast turn whose admission Pred inspects a register a concurrent slow turn writes is
  demoted. Apps with chatty global counters will see no fast path until they
  restructure into monotone shapes — the classifier is also a *pricing signal to app
  authors*, which DREGG3 §8 already frames as an asset ("the system telling the
  author the true cost of the braid they asked for").
* **Revocation vs fast exercise** — the sharpest semantic decision. Either every cap
  exercise whose grantor could concurrently revoke is contended (revocation is
  globally binding, fast path shrinks a lot), or fast exercise tolerates a bounded
  staleness window of one ack-round (revocation binds at fast-finality of the
  *revoke*, and an exercise racing it may win). R7's epoch-at-retrieval is
  order-dependent by design; this needs an ember-grade decision, and the doc's
  recommendation is the bounded-staleness reading WITH the window surfaced in Q
  (the receipt says which epoch it read) — the same shape as sturdyref
  `max_staleness`.
* **History-dependent guards** (the causal braid, DREGG3 §8 axis-2): a guard reading
  the causal past may break I-confluence; the classifier must treat the trace slice
  it reads as read-footprint. Confluence-stable guards run free; the rest force
  ordering — the two-sides-of-one-coin already stated at `DREGG3.md:375-383`.
* **Wire/protocol changes** — smaller than feared: tier-2 acks are free (causal
  pasts already carry them, §3.1); the genuine changes are (a) a classification bit
  per turn (descriptor-derived, not user-asserted), (b) the per-cell tier field,
  (c) receipts in Q annotated with finality mode + epoch-read, (d) the executor's
  dual frontier, (e) for §5 only: the consensus←cell feedback edge.
* **n=1 devnet trivializes the fast path.** At n=1 everything is already immediate
  (`blocklace_sync.rs:546`); nothing about this design is observable below n=2, and
  the latency payoff (1 RTT vs a 3-round wave + ratification) is measurable only at
  n≥3. The design must therefore land with its n=3 differential harness, or it
  lands as decoration. Staging below is built around that.
* **Equivocator-funded rollback residual** (T6): a fast-final turn whose creator is
  later exposed can be tau-excluded; the slash (§7) prices it, the ack-side fork
  check bounds it, and Q must surface it. This is the one place the fast path is
  weaker than tau, and the doc refuses to hide it.

---

## 9. Staging and verdict ladder

**Rides now (independent of everything):**
* T5 prefix monotonicity — also discharges an existing header overclaim the live
  node leans on. *(wave)*
* T1/T4 + the NEG witness — landed in the feasibility note. *(afternoon, done)*
* The conflict table (§2.2) → a `Conflict` column in the descriptor/verb registry
  (VerbRegistry is the anchor file for exactly this kind of reconciliation).
  *(afternoon-to-day)*
* Evidence value + codec + Pred atom design (§7 items 1–2). *(afternoon design,
  wave to land)*

**Rides the n=3 devnet (needs nothing else first):**
* `ackDepth` as a pure Lean function + export (same pattern as
  `dregg_tau_order`: model → theorem → `@[export]` → node gate), with the T4
  determinism theorem and a node-side *shadow mode*: compute fast-finality verdicts,
  log latency-vs-tau, finalize nothing by it. Shadow mode is the honest first ship —
  it measures the payoff claim before any semantics change. *(wave)*
* T6 (after T5). *(wave)*

**Needs the rotation (VK/commitment bump, shared with the cap-crown/S2 rotation):**
* The per-cell `finalityTier` field (changes the cell record/commitment). *(wave,
  but sequenced behind the rotation)*
* Q finality-mode annotation (receipt format). *(same rotation)*

**Epoch-sized (sequenced last, each gated on the previous):**
* T2 frame⇒commute over the full `RecordKernelState` (per-verb frame lemmas).
* T3 trace convergence + the executor dual-frontier rework (fast turns actually
  finalize by ackDepth; tau becomes contention-only).
* §5 polis-owned membership (constitution cell + the feedback edge), after the
  DREGG3 §8 relational-guard closure.

**The single highest-leverage next implementation step:** prove
**T5 — `tauOrder` finalized-prefix monotonicity** in
`Dregg2/Distributed/BlocklaceFinality.lean`. It is the one theorem that (a) the
running node already silently assumes at `blocklace_sync.rs:660-661`, (b) the
module header already claims at `BlocklaceFinality.lean:52` without a proof in the
tree, and (c) every fast-path no-rollback statement (T6, hence the whole thesis)
stands on. One wave, no wire changes, closes an honesty gap and opens the lane.
