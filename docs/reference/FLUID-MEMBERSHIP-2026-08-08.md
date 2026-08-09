# Fluid membership: which dregg operations need consensus, and which we are needlessly ordering

**2026-08-08.** Companion to `CONSENSUS-FROM-SOURCE-2026-08-08.md` (what Cordial Miners
specifies), `FEDERATION-DESIGN-GAPS-2026-08-08.md` (how to make *our* committee change safely)
and `DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md` (the reconfiguration corpus). Those three ask
**how to reconfigure a BFT committee**. This one asks the orthogonal question: **how much of
dregg needs a BFT committee at all.**

Read only: no protocol code was changed producing this.

---

## 0. The verdict, before the evidence

**Three findings, and two of them go against the framing that motivated this lane.**

**A. "Fully fluid membership, still safe" is refuted as stated — by a theorem, not by
engineering difficulty.** Lewis-Pye & Roughgarden, *Permissionless Consensus* (LPR), gives the
exact hierarchy the question needs. The **dynamically available** setting is precisely "known
identifiers, but participants may be any subset — they come and go on demand": LPR §1.2. The
**quasi-permissionless** setting is "all listed identifiers are active" — leaving requires
first removing yourself from the list, i.e. a *ceremony*.

> **LPR Thm. 7.2.** *For every ε < 1/3, there is no 0-resilient protocol solving probabilistic
> BA with security parameter ε in the dynamically available, authenticated, and partially
> synchronous setting.*

`0-resilient` means **with no Byzantine players at all**. And:

> **LPR Thm. 9.1.** *Consider the quasi-permissionless, authenticated, and partially synchronous
> setting. For every ρ < 1/3, there exists a deterministic and ρ-resilient PoS blockchain
> protocol.*

LPR §7.3 states the separation explicitly: 7.2 and 9.1 "provide a formal separation between the
dynamically available and quasi-permissionless settings, with the former setting strictly more
difficult than the latter." Our Cordial Miners deployment is the **Eventual Synchrony** instance
(`CONSENSUS-FROM-SOURCE` §5.3) — i.e. partial synchrony. So *for the consensus core*, "join and
leave on demand with no ceremony" is not a hard engineering problem; it is on the wrong side of
Theorem 7.2. Departure must be announced. That is what a ceremony **is**.

Add LPR Thm. 7.3 (Neu, Tas & Tse): accountability is impossible in the dynamically available
setting even under **synchrony**. Since our whole equivocation-exclusion story is an
accountability story, fluidity would cost us the property we have most invested in.

**B. The corpus's actual answer is decomposition, and its author already drew the layering.**
Shapiro, *Grassroots Currencies* §5 (p. 14) sets out a three-tier computational hierarchy:

> "(i) Grassroots Dissemination with leader-based equivocation exclusion is sufficient for
> implementing grassroots currencies, as their longevity need not exceed that of the issuer.
> (ii) Reliable Broadcast, which includes all-to-all dissemination and supermajority-based
> equivocation exclusion, is the standard computational foundations for a payment system of a
> global cryptocurrency. (iii) Ordering consensus, realised by blockchain consensus,
> State-Machine Replication, or Byzantine Atomic Broadcast, is used for mainstream
> cryptocurrencies. **Importantly, these protocols are not grassroots.**"

And the brief's thesis is confirmed at source, in *Grassroots Systems* §2.1 p. 7, immediately
after Theorem 13 — with ref. [16] resolving to Cordial Miners itself:

> "permissioned consensus protocols with a predetermined set of participants such as Byzantine
> Atomic Broadcast [30, 16] are all **interfering**, as additional participants cannot be
> ignored."

GS §2.1 continues: "Devising grassroots consensus protocols is a subject of future work."
`CONSENSUS-FROM-SOURCE` §4a/4b already established this; nothing here weakens it. The point for
*this* document is what follows from it: since tier (iii) is where grassroots dies, the way to
get fluidity is to **move operations down to tiers (i) and (ii)**, not to make tier (iii) fluid.

**C. ⚠ The two operations the brief hoped were CRDT-shaped are the two the literature prices
highest — and it prices them exactly.**

- *"Our capability system is monotone (grant/attenuate) which is CRDT-shaped; revocation may
  not be."* Correct, and there is a paper that gives the number. Frey, Gestin & Raynal, *The
  Synchronization Power (Consensus Number) of Access-Control Objects: the Case of AllowList and
  DenyList*, DISC 2023 — **Cor. 5: CN(AllowList) = 1. §1 contribution 2 + Cor. 7 + Thm. 8:
  CN(DenyList) = k**, where *k* is the number of processes that can conduct **prove**
  (set-non-membership) operations. §3: the consensus number comes not from the insert but from
  the **anti-flickering** property — a principal denied a resource must not transiently regain
  it. Every dregg validator verifies non-revocation, so our *k* is *n*.
- *"Our shielded pool has a global accumulator and nullifier set — that smells like it needs
  order, but check whether a CRDT formulation exists."* It smells right. Same paper,
  **Cor. 14: the k-anon-AT object has consensus number exactly k**, where *k* is the size of the
  anonymity set (App. B.1: the maximal-anonymity setup is µ(i) = {1}^|Π|, every process able to
  transfer on behalf of every wallet). **Anonymity has a consensus price and the price is the
  anonymity-set size.** A pool whose anonymity set is everyone needs *n*-consensus. There is an
  escape, and it is a redesign, not a reformulation — §1.6 below.

**D. And the sharpest census fact, which cuts across all of the above.** `CellId::derive_raw(pk,
token_id)` (`cell/src/cell.rs:997`) means dregg cells are **owner-derived, not
namespace-allocated** — creation cannot contend. But `Effect::GrantCapability` +
`Effect::ExerciseViaCapability` (`turn/src/executor/apply.rs:2874`) let a cap holder apply
effects to the **granter's** cell under a facet mask. So:

> **Every capability grant carrying a state-writing facet converts its target from a
> single-owner account into a k-shared one, and thereby raises that account's consensus number
> from 1 to k** (Guerraoui, Kuznetsov, Monti, Pavlović & Seredinschi, *The Consensus Number of a
> Cryptocurrency*, PODC 2019, as restated in CryptoConcurrency §1 and §Abstract: "implementing
> asset transfer with shared accounts is impossible without consensus").

Grants are individually free (CN 1, AllowList). Their **effect on the graph** is not. This is
the single most important structural fact in the census and it does not appear in any of the
sibling documents.

---

## 1. The operation census

Grounded on the 38-variant `Effect` enum at `turn/src/action.rs:1081` (the live enum; ⚠
`docs/reference/effect-vocabulary.md` is stale — it lists 33 variants at line 1061 and omits
`Custom`, `CreateHybridCell`, `RotatePqIdentity`, `Shield`, `Deshield`, i.e. **both shielded
on/off-ramps**, which are exactly the operations this question is about). The Lean roster
`metatheory/Dregg2/Substrate/VerbRegistry.lean:224` is current at 38.

The column that matters is **"what does the verifier have to know to accept this in isolation?"**
If the answer is "the sender's own prior state and one signature", the operation is
reliable-broadcast-implementable. If the answer requires ruling out a *concurrent* operation by
someone else, it is not.

### 1.1 Group I — single-owner writes. **17 effects. Consensus number 1.**

`SetField` · `EmitEvent` · `IncrementNonce` · `SetPermissions` · `SetVerificationKey` ·
`SetProgram` · `RefreshDelegation` · `RevokeDelegation` · `MakeSovereign` · `Refusal` ·
`CellSeal` · `CellUnseal` · `CellDestroy` · `AttenuateCapability` · `ReceiptArchive` · `Custom` ·
`RotatePqIdentity`

Each reads and writes exactly one cell, whose write authority is the cell's own key. Two
concurrent such effects on *different* cells commute unconditionally. Two on the *same* cell are
by definition self-inflicted, and the standard construction handles them: a **per-account
sequence number**. We already have it — `Effect::IncrementNonce` and the cell nonce are
structurally the `sn_i` of Albouy et al.'s Agreement Proof scheme (*Asynchronous BFT Asset
Transfer: Quasi-Anonymous, Light, and Consensus-Free*, §6.1: AP-Agreement — "there are no two
different valid APs σ_i and σ_i' for two different values v and v' at the same sequence number
sn_i and from the same prover p_i").

⚠ **Conditional on the cap graph.** `AttenuateCapability` is narrow-only in place
(`apply.rs:4340`, `capabilities.attenuate_in_place` at `:4384`); as a *specification* it is a
meet-semilattice operation and hence a CRDT. As *implemented* it is a read-modify-write, so two
concurrent attenuations of one slot would be last-writer-wins, not a meet. Under a
consensus-free regime that becomes a correctness requirement, not a nicety. Everything else in
Group I is genuinely single-writer only when the cell has no outstanding cap carrying the
matching facet — see §1.5.

### 1.2 Group II — creation. **4 effects. Consensus number 1, by identifier construction.**

`CreateCell` · `SpawnWithDelegation` · `CreateCellFromFactory` · `CreateHybridCell`

Name allocation is the textbook consensus-requiring operation: two claimants, one name. **We do
not have it.** `CellId::derive_raw(public_key, token_id)` (`cell/src/cell.rs:531`, invariant
checked at `:997`) makes the identifier a *function of the creator's key*. Two distinct creators
cannot collide; one creator colliding with itself is its own equivocation and is caught by the
same per-account sequencing as Group I. This is a real architectural asset and it was not
designed for this purpose.

⚠ The exception is `governed-namespace`, which reintroduces a shared namespace on purpose —
§1.7.

### 1.3 Group III — monotone / AllowList writes. **5 effects. Consensus number 1 (Cor. 5).**

`GrantCapability` · `Introduce` · `NoteCreate` · `Promise` · `Notify`

Each is an **insert into a grow-only set**. `note_commitments` is grow-only with duplicate
rejection (`cell/src/commitment_set.rs:96`); the reactive registry grows
(`turn/src/executor/mod.rs:994`); a c-list slot install is an add. Concurrent inserts commute;
duplicate inserts are idempotent. This is a grow-only set CRDT and it is exactly Frey/Gestin/
Raynal's AllowList, whose **`append` operation carries no synchronisation requirement**
(DISC 2023 §5, Thm. 4: "Algorithm 1 wait-free implements an AllowList object", Cor. 5: CN = 1).

The blocklace supplies the substrate for free: Almeida & Shapiro, *The Blocklace: A
Byzantine-repelling and Universal Conflict-free Replicated Data Type* — "the blocklace datatype,
with the sole operation of adding a single block, is a CRDT … it is both a pure operation-based
CRDT, with self-tagging, and a delta-state CRDT". Prop. 5.4 (Eventual Visibility) and Prop. 5.5
(Finite Harm) are the guarantees these five operations actually need. **We already run the
structure; we are running consensus on top of it for operations that only need the structure.**

### 1.4 Group IV — transfer-shaped. **8 effects. CN 1 if single-owner; CN k if k-shared.**

`Transfer` · `NoteSpend` · `Mint` · `Burn` · `React` · `BridgeMint` · `ExerciseViaCapability` ·
`PipelinedSend`

This is the classical result (Guerraoui et al. PODC'19; Albouy et al. §1: "consensus was thought
necessary to avoid double spending, but … a reliable broadcast primitive whose deliveries
respect process sending order is sufficient **when each account is owned by a single
process**"). Three refinements matter for us:

1. **Credits are always free.** Only the *debit* side needs ordering; a receiving account can
   apply incoming credits in any order. So `Burn`'s write to the issuer well and `Mint`'s credit
   to the target are consensus-free; only `Mint`'s draw *from* the well and `Burn`'s debit *of*
   the target are transfer-shaped.
2. **Shared accounts are not automatically consensus.** CryptoConcurrency (Tonkikh, Ponomarev,
   Kuznetsov & Pignolet) **Thm. 1**: a deterministic asynchronous protocol exists with
   *Transfer Concurrency* — consensus objects are invoked **only when there is an actual
   overspending attempt** — at k-overspending-free latency of **k+4 RTTs**. Its Abstract and §4
   add the part that reframes our whole federation: "we avoid relying on a central,
   universally-trusted, consensus mechanism and allow **each account to use its own consensus
   implementation, which only the owners of this account trust**."
3. **`React` is a one-shot hole discharge** against `reactive_nullifiers`
   (`turn/src/executor/mod.rs:1000`). If only the hole's holder may discharge it, k = 1 and
   `React` belongs in Group I. If a `Notify`-deposited hole is dischargeable by several parties,
   k is that number. Worth pinning deliberately; it is currently an emergent property of who
   holds what.

### 1.5 ⚠ The cap graph is the k

`ExerciseViaCapability` (`apply.rs:2874`) resolves `cap.target` — **another cell** — and applies
`inner_effects` there under the cap's permission level and `allowed_effects` facet mask. A cell
with *m* live outstanding caps carrying a state-writing facet is an (m+1)-shared account in
exactly CryptoConcurrency's sense.

So the census's tidy "Group I is single-owner" is **conditional on the capability graph**, and
the capability graph is data, not schema. The useful consequence is also the actionable one:

> **k is computable.** For any cell, k = 1 + |live caps on it carrying a writing facet|. A
> consensus-free fast path can *check* k = 1 and take the broadcast route; anything else routes
> to the account's own (small) consensus. That is precisely CryptoConcurrency's dynamic
> detection, and it works because our caps are explicit objects rather than an ambient ACL.

### 1.6 Group V and VI — the two that are genuinely priced above 1

**`RevokeCapability` — a DenyList. CN = k = the number of non-membership verifiers = n.**

`apply.rs:908` does two things: a per-cell tombstone (`capabilities.revoke(slot)` at `:945`,
single-owner, Group I-shaped) and an insert of `cred_nul(provenance)` into the global grow-only
`note_revoked` accumulator (`:955`, `insert_revocation` at `:963`, idempotent). The *insert* is a
CRDT. **The read is not.** Every capability exercise proves "no ancestor of mine is revoked" —
a set-**non**-membership proof — and Frey/Gestin/Raynal §3 identify exactly this as the
difference:

> "resource after being denied it poses serious security problems. Hence, the DenyList object is
> defined with an additional **anti-flickering** property prohibiting such transient periods.
> This property is the main difference between an AllowList and a DenyList object and is the
> reason for their distinct consensus numbers."

Contribution 2: "the DenyList requires the synchronization of all the **k verifiers of its
set-non-membership proofs**, i.e. CN(DenyList) = k." In dregg every validator is a verifier, so
k = n and revocation is full-federation consensus. ⚠ The paper also says what would *reduce* it:
k is the verifier count, not the participant count. A revocation whose non-membership is
verified only by the parties in the derivation subtree has k = that subtree.

⚠ Second-order: `apply_revocation_channel_trip` (`apply.rs:1002`) is `#[allow(dead_code)]` with
no production caller, and `RevocationChannel::trip` (`cell/src/revocation_channel.rs:128`)
compares `CellId`s in memory **with no signature check**. Any consensus-free redesign of
revocation must not inherit that; an unauthenticated trip in a broadcast regime is a remote
denial primitive.

**`Shield` / `Deshield` / `ShieldedTransfer` — CN = anonymity-set size (Cor. 14).**

`apply_shielded_transfer` (`apply.rs:1843`) reads `note_shielded.root8()` at `:1884` — a single
global accumulator root — and judges every input's spend proof against it, then writes
`note_nullifiers` (`:1897`) and `note_shielded` (`:1957`). `apply_shield` at `:2006`,
`apply_deshield` at `:2135` (which reads the live `note_shielded.root8()` as `piCommitted`).
**None of them names a cell**: `participant_cells` is empty for `Shield` (`action.rs:1662`).

That is the definition of an operation with no single owner, and the price is stated:

> **Frey/Gestin/Raynal Cor. 14.** *The consensus number upper bound of a k-anon-AT object is k.
> Using this corollary and Thm. 12, we further deduct that k-anon-AT object has consensus
> number k.*

with k the anonymity-set size (App. B.1). Albouy et al. §2 restate the same result from the
other side: "it was recently shown [22] that fully anonymous asset transfer requires consensus
or equivalently total order to be implemented, if asset transfers from a correct process must
never fail."

**Is there a CRDT formulation?** No — but there is a *different object* with a
consensus-free implementation, and the shape of the trade is fully specified. Albouy et al.'s
QAAT (§6.2, Alg. 1–3) achieves **quasi-anonymity**: receiver and amount hidden, **sender not**
(§1 fn. 1: "when the anonymity of only the sender or the recipient is hidden, we talk about
quasi-anonymity"). Structurally it replaces our two global objects with per-account ones:

| dregg today | QAAT |
|---|---|
| one global `note_shielded` accumulator | `A_i` — a universal accumulator **per process**, of that process's own debits and credits (Alg. 1) |
| one global `note_nullifiers` set | **per-sender sequence number `sn_i`** + AP-Agreement: at most one valid proof per (prover, sn) |
| double-redeem prevented by the global nullifier set | non-membership proof in the **receiver's own** accumulator (§6.2) |

The double-spend argument becomes local: at most one transfer per sequence number per sender.
There is no global nullifier set at all. `t < n/3` is needed **only** for the Agreement Proof
scheme (§6 fn. 5). Zef takes the same escape (Albouy §2: "similar to what is done by Zef").

⚠ **This is a full redesign of the pool, not a reformulation of it, and it costs sender
anonymity.** Say that plainly before pricing it. It is also the only route the corpus offers,
because the impossibility is a theorem.

### 1.7 The non-`Effect` operations

**Committee Join / Leave.** `blocklace_sync.rs:3575` `propose_membership` →
`apply_passed_proposal` (`:20002`) mutates `constitution.current.participants`;
`apply_committee_change` (`:3492`) advances the PQ roster, the finalization-vote committee and
the threshold. This is the one operation whose *purpose* is to change the quorum that authorises
future operations. §2 and §3 below.

**Automatafl game turns — the pleasant surprise: k = 2, and commit-reveal already commutes.**
`MatchState` (`dregg-automatafl/src/game.rs:438`) is one shared `WorldCell` written in full each
turn, and `surface.rs:26` says the moves are simultaneous: "Automatafl's turn is not alternating:
both players seal simultaneously." But the per-seat slots (`commit: [u64;2]`, `frm`, `to`) mean
each seat's commit is a **single-owner write keyed by (seat, turn_no)**, and the resolution
`apply_turn = automaton_step ∘ resolve_mid` is a deterministic pure function of both commits.
Two seats' commits therefore commute; the *turn* is a deterministic join. Consensus number 2 at
worst, and plausibly 1 per seat.

⚠ **What genuinely needs more is the timeout.** Deciding that a player *did not* reveal is a
decision about the **absence** of a message, and absence is not detectable asynchronously. Every
forfeit, expiry and dispute window in the system is of this shape. This is the real ordering
requirement in games, and it is nowhere near where anyone would look for it.

**The daily crate ritual — the purest consensus-free operation we own, currently guarded by a
process mutex.** `metatheory/Dregg2/Games/PathOfAngels/SalvageCrate.lean:216` — `OpenKey` carries
`{federationId, contentSession, contentEpoch, period, player}`, and `State.consumed` (`:244`) is
a `Finset OpenKey`. **Keyed by player.** So `consumed` is a grow-only set partitioned by player:
one writer per partition, concurrent opens by different players commute, a duplicate open by one
player is idempotent. CN 1, textbook G-Set CRDT.

What we actually run is a single-node `tokio::sync::Mutex` over a read-open-append against one
federation-scoped blob (`node/src/poa_crate_api.rs:123`, gate at `:179`, critical section at
`:325`), because — as the code itself says at `:176-181` — `PersistentStore::get_config/
set_config` are not a compare-and-set. **The contention is in the storage representation, not in
the semantics.** The Lean states the resulting dependency as
`the_replay_guard_is_exactly_as_strong_as_the_node_log`. A per-player key would remove both the
lock and the dependency.

**`governed-namespace` route table.** `governance_committee_root` and `threshold` are
`Immutable` for the cell's life (README `:45-55`), so its membership is *frozen*, not governed;
its route updates are an M-of-N vote on a shared namespace — the one place we deliberately
reintroduce name contention. CN = the committee size.

**`polis` council.** M-of-N with **forward-certified amendments** (README `:19-26`): the new
membership is committed *before* it takes effect. That is the right shape and is worth noting —
it is a small-k, locally-trusted consensus object of exactly the kind CryptoConcurrency §4
describes, already built, already scoped to its own members.

### 1.8 The census in one table

| Group | Count | Requirement | Cited |
|---|---|---|---|
| I single-owner writes | 17 | reliable broadcast + per-account `sn` | Albouy §6.1 (AP-Agreement) |
| II creation | 4 | RB; no name contention by construction | `cell.rs:997` |
| III monotone / AllowList | 5 | grow-only set CRDT | Frey/Gestin/Raynal Cor. 5; Almeida & Shapiro |
| IV transfer-shaped | 8 | CN 1 single-owner; CN k shared, consensus only on overspend | Guerraoui PODC'19; CryptoConcurrency Thm. 1 |
| V revocation | 1 | **CN = k = non-membership verifiers = n** | Frey/Gestin/Raynal Cor. 7 / Thm. 8 |
| VI shielded | 3 | **CN = anonymity-set size** | Frey/Gestin/Raynal Cor. 14 |

**34 of 38 effects (89%) are reliable-broadcast-implementable** under an explicit hypothesis —
that the target cell's capability graph has k = 1 — plus the automatafl turn (k = 2) and the
crate open (k = 1). **4 of 38 are priced above 1 by a theorem**, and all four are the ones a
casual read would have guessed were fine.

⚠ **A count of effect variants is not a count of traffic**, and the difference is measured
elsewhere: Sui Lutris (Blackshear et al., §1) reports that over its history **64% of transactions
used the consensus-free fast path, with peaks at 98%** — but "on some rare days where traffic is
dominated by more traditional DeFi and Oracle applications, the rate of transactions using the
fast path drops to **1%-2%**." That is *Sui's* number on *Sui's* workload; we have no equivalent
measurement of dregg and I am not extrapolating one. What it establishes is that the
consensus-free fraction is a property of the **workload**, not of the protocol, and it can
collapse.

---

## 2. The boundary: the smallest set that genuinely needs consensus

Six members. Each is here because concurrent operations do **not** commute and no local witness
can rule the conflict out.

1. **Committee membership change itself.** Not because reconfiguration inherently needs
   consensus — DBRB and Pastro both do it *without* (§3) — but because ours changes the quorum
   threshold `⌊(n+f)/2⌋+1` of a protocol whose specification assumes a fixed Π (CM §2), and
   because the resulting object must be totally ordered with respect to the votes counted
   against it. `FEDERATION-DESIGN-GAPS` §2.3 already names the enabling absence (no
   configuration number on any consensus message).

2. **Revocation's non-membership check**, at k = n (§1.6). Reducible in principle by shrinking
   the verifier set; not reducible by reformulation.

3. **The shielded pool**, at k = anonymity-set size (§1.6). Reducible only by weakening to
   quasi-anonymity, which is a redesign.

4. **Overspend resolution on a k-shared cell** — and *only* the overspend, per CryptoConcurrency
   Thm. 1's Transfer Concurrency property. Not every access to a shared cell. The consensus
   object required is **per-account and trusted only by that account's owners**, not the
   federation's.

5. **Every decision about an absence**: turn timeouts, capability expiry against block height
   (`apply.rs`: `self.block_height > expires_at`), dispute windows, forfeit. Asynchrony cannot
   distinguish "did not send" from "not yet delivered". These need either consensus or an
   explicit synchrony assumption, and today they are silently getting the former.

6. **Shared-namespace allocation** where we choose to have one — `governed-namespace`'s route
   table. Avoidable per-namespace; we avoided it for cells.

### ⚠ 2.1 What is actually forcing the total order today, and it is none of the above

`turn/src/executor/mod.rs:2114-2122` — `consensus_state_commitment` folds **three global
accumulator roots** (`note_nullifiers.root8()`, `note_commitments.root8()`,
`note_revoked.root8()`) into the single value that the executor signature, the federation
receipt QC and the attestation quorum all certify (context builder at
`turn/src/state_commit.rs:197-204`).

**A single global root is a total order whether or not any operation needed one.** Two turns
that touch disjoint cells and commute perfectly still produce different signed commitments
depending on which was folded first. This — not the operations — is the mechanism by which
dregg totally-orders a system that is 89% commutative.

Whatever else is decided, this is where the decomposition starts, and it is the smallest
possible first move: **shard the committed root** so that a turn's commitment is over the
accumulators it touched, not over all of them. Sui Lutris §1 solves the same problem the same
way and calls the leftover an "after-the-fact checkpointing protocol that eventually generates a
canonical sequence of transactions in blocks, **without delaying execution and finality**."

⚠ Related, and it cuts the other way: `note_shielded` is **deliberately absent** from
`consensus_ctx` (`mod.rs:980-984`). So today the *most* consensus-bound object in the census
(§1.6) is the one global accumulator whose root the committed commitment does **not** cover. That
is a defect under the current architecture and it does not become less of one under any
decomposition.

---

## 3. What fluid membership would look like for the consensus-free majority

Two constructions in the corpus do this, and they answer the four questions in the brief
directly.

### 3.1 Who may participate

**DBRB** (Guerraoui, Komatović, Kuznetsov, Pignolet, Seredinschi, *Dynamic Byzantine Reliable
Broadcast*) — the primitive is exactly "reliable broadcast where processes join and leave, with
no consensus underneath." Its central move is that **processes never agree on the membership**
(§1: "which makes it impossible for processes to agree on the exact membership"). Instead:

- A **view** `v` is an append-only set of `changes ⊆ {+,−} × U` (§3.1). Membership is
  `v.members = {p : ⟨+,p⟩ ∈ v.changes ∧ ⟨−,p⟩ ∉ v.changes}` — a *derived predicate over a
  monotone set*, not a registry. (Compare `CONSENSUS-FROM-SOURCE` §4c: GSN's `member(q, B)` is
  the same shape. And compare ours: `constitution.current.participants`, a registry that both
  grows and shrinks — `blocklace_sync.rs:2341` notes the two halves have *different*
  monotonicity.)
- Views are made **comparable**, so the set of views is a chain and reconciliation is a
  join — not a decision.
- Quorums are `v.q = |v| − ⌊(|v|−1)/3⌋`, per view (Assumption 3), with the resilience
  "more than 2/3 of processes inside the broadcast system are correct **at all times**, which
  is tight" (§1).

**Pastro** (Kuznetsov, Pignolet, Ponomarev, Tonkikh, *Permissionless and Asynchronous Asset
Transfer*) goes further: the participant set is not a set at all but a **stake-weighted
configuration**, "a partially ordered set of transactions that unambiguously determines the
active system participants and the distribution of stake among them", and — the load-bearing
sentence — "configurations form a lattice order and a **lattice agreement** protocol can be
employed to make sure that participants properly reconcile their diverging opinions on which
configurations they are in" (§1). **Lattice agreement is strictly weaker than consensus and is
solvable in asynchrony.** That is the mechanism by which membership can be fluid without
consensus, and it is the answer the brief was looking for.

### 3.2 What a newcomer must obtain before acting

Not a chain. Three things, and this is where the honest cost starts:

1. **A view / configuration certificate.** In DBRB, the join is a protocol: the joiner
   disseminates its request, gathers confirmations, and is installed by a view change in which
   correct processes "exchange their current state with respect to in-flight broadcast messages
   and membership changes" before transitioning (§1). In Pastro, the certificate is a
   configuration signed by holders of > 2/3 of stake.
2. **State transfer for whatever it must witness.** DBRB's install carries state-update
   messages; a joining validator that must answer non-membership queries needs the accumulator,
   not just the head.
3. **Nothing else.** In particular *not* the total history — this is the whole point of
   the "lightness" line (Albouy §1: "each participant only needs to store her own transfer
   history"). ⚠ Contrast Ouroboros Genesis, whose contribution is that a newcomer can
   bootstrap **from the genesis block alone**, without checkpoint advice — but that is a
   *different guarantee in a different setting*: **dynamic availability** means honest parties
   may sleep and wake while the protocol still produces one total order, and it requires
   synchrony, a clock, and an honest majority of *online* stake (OG §1, §2.1, "Dynamically
   available party sets"). Dynamic availability is about **who is awake**; fluid membership over
   RB is about **who is a member**. They are not substitutes and neither implies the other.

### 3.3 What a departure costs — ⚠ and the thing you cannot promise a leaver

**DBRB Thm. 81 (Strong Validity Impossibility)** and **Thm. 82 (Strong Totality Impossibility)**:
no algorithm can guarantee that a process which has asked to leave delivers everything
broadcast/delivered before it left. Both proofs turn on indistinguishability between "the sender
crashed" and "the sender's messages are delayed", and Thm. 82 holds *even if the only failure is
a single crash*. What DBRB **does** achieve is stated as maximal: validity and totality hold for
every correct process that has **not** expressed its will to leave (Def. 1).

So the departure contract is: *you may leave at any time; the system will not tell you what you
missed on the way out.* For a validator that is fine. For anything that must produce a final
receipt to its own user, it is a design constraint.

Two more departure costs, both from the same source:

- **DBRB Assumption 1 (Finite number of reconfiguration requests):** "In every execution, the
  number of processes that want to join or leave the system is finite … captures the assumption
  that no new reconfiguration requests will be made for *sufficiently long*, thus ensuring that
  started operations do complete." ⚠ **This is the fine print on "fully fluid".** Even the
  construction designed for join-and-leave-without-consensus needs churn to *pause* for
  liveness. Unbounded fluidity is not on offer anywhere in this corpus.
- **Key destruction.** Pastro §1: "before installing a new configuration, one should ask holders
  of > 2/3 of stake of the old one to **upgrade their private keys and destroy the old ones**",
  via a forward-secure signature scheme. A departure that leaves old keys alive leaves a
  superseded configuration able to deceive slow participants.

### 3.4 What an adversary gains

- **Superseded-configuration attack on slow readers**, unless forward-secure keys are used
  (Pastro §1). This is a *new* attack surface that a static committee does not have.
- **The stake/weight assumption must hold in every active candidate configuration
  simultaneously** (Pastro §1: "the adversary is restricted to corrupt participants that
  together own less than one third of stake in **any active candidate configuration**"), not
  just in the current one. Fluidity multiplies the number of things that must be true at once.
- **Account lockout**, the characteristic consensus-free failure. Sui Lutris §1 is blunt:
  "consensusless protocols are sensitive to client bugs as equivocations lock the assets
  forever." Their fix is not a proof but an **epoch**: "client bugs only affect the liveness of
  equivocated owned objects for a single epoch … the current epoch length for our production
  system is 24h." CryptoConcurrency's fix is the per-account consensus fallback. Either way,
  **something periodic or something consensual has to exist to un-wedge an equivocated account**
  — and note that a 24h epoch boundary is itself a ceremony.
- **Loss of accountability**, if fluidity slides into the dynamically available setting:
  LPR Thm. 7.3 (Neu, Tas & Tse), impossible even under synchrony.
- **Colluders**, which the blocklace handles but does not eliminate: Almeida & Shapiro §5.2 —
  "a colluder p can remain undetected indefinitely, allowing it to create any number of blocks,
  preceded by any number of blocks from the Byzantine node q". Prop. 5.5 bounds the harm to a
  finite prefix; it does not prevent it.

---

## 4. The honest cost — what a shift would break, re-open, and make unclaimable

**What breaks immediately.**

- `consensus_state_commitment` (§2.1) and everything downstream of it: the executor signature,
  the federation receipt QC, the attestation quorum, the light client's notion of "the state
  root at height h". A sharded commitment is a different object; a flag day, a VK epoch, a
  re-genesis. Cheap by this repo's doctrine — but it is not a small diff.
- **`RevokeCapability` stops working as specified.** Anti-flickering is what makes revocation
  mean anything, and it is *exactly* what the consensus number buys. A revocation in a
  broadcast-only regime is a revocation that can transiently un-revoke.
- **The shielded pool stops working entirely** unless it is rebuilt per-account (§1.6), and the
  rebuilt version is quasi-anonymous. Every VK, every PI count, every circuit in the shielded
  family is re-emitted.

**What re-opens.**

- **Every soundness statement that quantifies over "the committed order."** The apex campaign,
  the fold pins, the light-client statements — they are statements about a totally ordered
  commit log. Under a partial order they need re-stating, and some of them may not have a
  partial-order analogue. This is by far the largest hidden cost and it is not a protocol cost;
  it is a **metatheory** cost, in the place where our work is deepest.
- **Equivocation exclusion** would have to become what `DECISION-BRIEF` §work already says it
  should be — "a predicate over committed structure (`node(b) ∉ byz(⌊b⌋)`), not a live roster
  mutation" — except that under fluid membership there is no single committed structure to
  evaluate it over, only comparable views. Almeida & Shapiro's Byzantine-repelling protocol is
  the right primitive; it has never been run in our tree.
- **The lockout question we have never had to answer**, because consensus answered it for us.

**What becomes unclaimable.**

- *"Every turn is totally ordered and every node agrees on the state root at every height."*
  This is currently true, it is load-bearing for how we explain the system, and it would become
  false by construction.
- *"Finality."* In the consensus-free line finality is per-operation and relative to a view.
  Grassroots Flash's own table (GF §6.1, via `CONSENSUS-FROM-SOURCE` §4b) reads
  `Consensus-based: No`, `Finality by/Trust in: Sovereign (= leader)`. That is a genuinely
  weaker sentence than the one we can say today.
- *"A leaver receives everything up to its departure"* — DBRB Thms. 81/82. Not a cost of our
  design; a cost of the universe.

**And what we would gain, stated at the same resolution.** Deterministic progress under
asynchrony for 89% of the effect vocabulary; no leader; no wave latency for a `SetField`; per-
account failure domains instead of one global one; and the ability to say something true about
grassroots deployment, which today we cannot (GS §2.1 names our exact protocol class as the
counterexample).

---

## 5. Rewrite or decomposition?

**Decomposition. It is incremental, the increments are independently valuable, and there is a
production existence proof.**

Sui Lutris is that proof, and it is not a paper system: §1 reports launch May 2023, "operating
continuously … with no downtime for a year", 107 validators, 3.1M certificates/day across 383
epoch changes, combining "a consistent broadcast protocol between validators to ensure the
safety of all operations" with consensus "only … for the correct execution of complex smart
contracts operating on shared-ownership objects, as well as to support network maintenance
operations such as defining checkpoints and reconfiguration." Owned objects take the fast path;
shared objects take consensus; **both live in one system**. That is our Group I/II/III versus our
§2 boundary, with the same dividing line drawn for the same reason.

The increments, in dependency order, each shippable alone:

1. **Shard `consensus_state_commitment`** (§2.1). Pure win regardless of the destination: it
   removes a false dependency between operations that already commute, and it is the
   precondition for everything else. Also closes the `note_shielded` gap by forcing the question
   of which root covers what.
2. **Make `k` explicit and computable per cell** (§1.5) — a cell's shared-ness is currently an
   emergent property of the cap graph. Naming it turns "is this operation consensus-free?" into
   a check rather than an argument. Valuable as an *audit* even if nothing else happens.
3. **Route the k = 1 fast path.** Group I/II/III over reliable broadcast with the cell nonce as
   the sequence number. The blocklace already is the CRDT; this is wiring, not invention.
4. **Per-account consensus objects for k > 1** (CryptoConcurrency §4) — and note we have already
   built one: `polis`'s M-of-N council with forward-certified amendments is exactly the shape.
5. **Then, and only then**, the two theorem-priced items: revocation's verifier set, and the
   shielded pool's anonymity model. Both are genuine design forks (§6).

**What is *not* incremental, and would be the fork:** making the *consensus core itself* fluid.
LPR Thm. 7.2 says that is not available in our setting, so the only version of "fully fluid" that
exists is one where the fluid part is the consensus-free part and the consensus part keeps its
ceremony. That is not a compromise position; it is the position the literature actually holds.

⚠ **Read this section against `CLAUDE.md`'s own warning.** The pattern it forbids is pricing the
real fix and shipping a containment while filing the fix as "Phase 3, later". Steps 1–4 above are
not a containment of step 5 — they are independently correct under the *current* architecture,
and each is a defect fix (a false dependency; an unnamed invariant; a needless total order; a
consensus object trusted by more parties than need trust it). Step 5's two items are priced by
*theorems*, not by cost estimates, and a theorem is the one kind of constraint this document is
allowed to treat as one.

---

## 6. The two genuine forks for ember

Everything above is either analysis or work. These two are taste, and both are §"key material /
weakens a check"-adjacent:

**Fork 1 — the shielded pool's anonymity model.** Full anonymity costs n-consensus (Cor. 14) and
is what we have. Quasi-anonymity (hide receiver + amount, expose sender) buys asynchronous,
consensus-free, per-account operation (Albouy §6) and a much smaller global state, and costs
sender anonymity permanently. There is no third option in this corpus, because the boundary is
an impossibility result.

**Fork 2 — revocation's verifier set.** k = n today because every validator verifies
non-membership. Narrowing k to the derivation subtree makes revocation nearly free and makes
"revoked" a *local* fact — which is a real weakening of a check, and therefore yours.

---

## 7. What I searched, and what the literature does not settle

**Searched:** the 43 PDFs in `pdfs/` (read in depth: DBRB; CryptoConcurrency; Pastro; Albouy et
al. QAAT; Frey/Gestin/Raynal DISC 2023; Lewis-Pye & Roughgarden *Permissionless Consensus*;
Almeida & Shapiro *Blocklace CRDT*; Shapiro *Grassroots Systems* and *Grassroots Currencies*;
Sui Lutris; Ouroboros Genesis; skimmed: *Foundations of Dynamic BFT*, *Reconfigurable
Heterogeneous Quorum Systems*, the static-BRB trio). Plus `scripts/lit-search.py` for
capability-revocation-without-consensus, which is how the DISC 2023 paper was found — **it was
not in the corpus** and it is the paper that settles the two questions the brief flagged as
open. Added as `pdfs/zot-consensus-number-access-control-allowlist-denylist-disc2023.pdf`
(DROPS full version, not the 2-page arXiv stub; ⚠ not yet in `pdfs/MANIFEST.json`).

**Not settled by anything I read:**

- **The consensus number of a *capability graph*.** Frey/Gestin/Raynal give AllowList and
  DenyList separately. Our object is an AllowList whose entries *point at other principals'
  state*, so each append raises another object's k (§1.5). I found no treatment of that
  composition. It may be a small result; it is not in the corpus.
- **Whether a partially-ordered commit log can carry our soundness statements.** Purely a
  question about our own metatheory, and the largest unpriced item in §4.
- **A churn bound for a mixed system.** DBRB has Assumption 1 (finite requests); Pastro
  explicitly does not bound configuration updates (per `DYNAMIC-COMMITTEE-LITERATURE` §4.2c);
  Sui Lutris uses a 24h epoch. Nobody states a rate.
- **Any measurement of dregg's own fast-path fraction.** §1.8's 89% is a count of *effect
  variants*, which is not traffic. The 64%/98%/1–2% figures are Sui's, on Sui's workload. We
  have no instrument that would answer this for us, and building one is cheap and would come
  before any of §5's steps were worth doing at scale.
