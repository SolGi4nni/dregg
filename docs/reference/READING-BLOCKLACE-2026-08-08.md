# Reading the blocklace: what our own data structure is supposed to guarantee

**Date:** 2026-08-08
**Method:** the blocklace's own foundational paper read end to end, plus Cordial Miners and the five
grassroots papers, from `pdfs/`. Every claim about a paper carries paper + section/definition/
proposition. Every claim about our code carries `file:line`, verified at source.
**Scope:** read-and-think. No protocol code changed by this pass.
**Builds on:** `docs/reference/CONSENSUS-FROM-SOURCE-2026-08-08.md` (`66681e080`), which settled the τ
question. This pass does not revisit τ; it reads the layer *underneath* τ — the datatype itself.

Citation shorthand: **BC** = Almeida & Shapiro, *The Blocklace: A Byzantine-repelling and Universal
Conflict-free Replicated Data Type* (arXiv:2402.08068v4, 2025-01-22) — **the blocklace's own paper**.
**CM** = Keidar, Naor, Poupko, Shapiro, *Cordial Miners* (arXiv:2205.09174v6). **GS** = Shapiro,
*Grassroots Systems* (2301.04391). **GSN** = *Grassroots Social Networking* (2306.13941).
**GF** = *Grassroots Flash* (2309.13191). **GA** = *A Grassroots Architecture for Digital Democracy*
(2404.13468). **GC** = *Grassroots Currencies* (2202.05619).

---

## 0. LEAD — the claims this reading falsifies

Five, in descending severity. Each is a statement we currently make, in a docblock or a module
header, that the papers or the code contradict.

### 0.1 `auto_evict_equivocator` reopens F-CO-1 — the exact fork the participant projection was written to close

`node/src/blocklace_sync.rs:2036`–`:2050` states the invariant that governs the τ participant set, at
length and correctly:

> the set … MUST be BYTE-IDENTICAL on every honest node — or two honest nodes compute DIFFERENT leader
> schedules over the SAME lace and finalize DIVERGENT orders with no detection: **a silent fork**.
> … Sourcing the key from committed state makes this projection **a deterministic function of
> committed state alone**.

The projection fix (F-CO-1) closed one input to that set: the node-local `votes.pq_key` map. It left
the other input wide open. `handle_push` (`:5543`), running on **gossip arrival**, calls
`constitution.auto_evict(proof)` (`:5580`), which reaches `Constitution::auto_evict_equivocator`
(`blocklace/src/constitution.rs:174`–`:185`) and does:

```rust
        self.participants.retain(|k| k != &evicted);
        self.threshold = compute_threshold(self.participants.len());
        self.version += 1;
```

and `poll_finalized_blocks` reads exactly that field, live, on every poll —
`blocklace_sync.rs:1996`: `let raw_participants = constitution.current.participants.clone();`.

So the τ participant set **is** a function of local gossip arrival order. It is not a function of
committed state, and nothing records the mutation anywhere a peer can see it. The divergence needs no
attacker beyond the equivocator itself: node A receives both halves of the fork and drops to `n=3`;
node B has received only one half and stays at `n=4`. `wave_leader(wave, participants)` is
`participants[(wave as usize) % participants.len()]` (`blocklace/src/ordering.rs:288`–`:291`), so A and
B elect **different leaders for the same wave**, and `supermajority_threshold` differs too
(`:317`). Divergent anchors, divergent τ, no detection. That is the F-CO-1 fork, verbatim, through a
second door.

Neither paper does this. **CM never changes `Π`** (§2: "a set Π of n ≥ 3 miners"); App. D contemplates
shrinking the *effective* set and files it as future work. **BC never changes `Π`** either — Π is
fixed at §2.1 and repelling operates on blocks, never on the node set. There is no line in either
paper that removes a member from the quorum denominator on detection.

### 0.2 "Equivocation detection built into the data structure" is false as stated — the structural check cannot fire

`node/src/blocklace_sync.rs:9` advertises, as one of four things the blocklace provides:

> - Equivocation detection built into the data structure

The structural check exists and is faithful: `Blocklace::approved_by`
(`blocklace/src/finality.rs:1910`–`:1955`) is CM Alg. 1 line 17 —
`approves(b, b1) := b1 ∈ [b] ∧ ∀b2 ∈ [b] : ¬equivocation(b1, b2)` — implemented over the block's own
causal past, exactly right.

It cannot fire, because our predecessor rule guarantees the equivocating pair is never in a causal
past. `try_add_block` (`finality.rs:1220`) takes

```rust
        let predecessors: Vec<BlockId> = self.tips.values().copied().collect();
```

and `tips` is `HashMap<[u8; 32], BlockId>` (`:1198`) — **at most one tip per creator, by type**. On
detection we go to zero: `insert_checked` does `self.tips.remove(&block.creator)` (`:1543`), `merge`
mirrors it (`:1631`), `remove_equivocator` does the same (`:1968`), and the tip is never restored
("Don't update tips for known equivocators", `:1556`).

So after detection **no block this node ever authors again points at either half of the fork**, and
before detection it can point at only one. The pair enters a causal past only by accident — if two
honest nodes each pointed at a *different* half before either detected, a later block pointing at both
their tips inherits both. That is a race, not a mechanism.

CM's rule is the opposite, and the difference is the entire point of the number two. CM Alg. 1 line 5:

```
 5:    b.pointers ← hash(tips), where tips are the tips of blocklace_prefix(d), at most two tips per miner
    ▷ Def. 19; two-tips limitation to prevent a Byzantine miner from flooding the blocklace before being
    excommunicated
```

**Two** is not a budget, it is a floor dressed as a cap (see §5). One is enough for an honest chain;
two is the minimum that carries an equivocating *pair* forward into the next block's closure, which is
what makes `approves` decidable at the anchor and what makes CM Prop. 39's proof go through. We
implement neither number — we implement one, then zero.

**What we actually do instead:** an out-of-band mutation of live membership state (§0.1). The
structure detects; it does not exclude.

### 0.3 The eviction does not survive a restart, and `committee_replay`'s stated doctrine is violated

`node/src/committee_replay.rs:1`–`:3` opens:

> the constitution as a PURE VIEW of the chain, never a second source of truth

`derive_from_lace` (`:225`) starts from `ConstitutionManager::from_participants(genesis_committee…)`
(`:230`) and folds finalized **membership** blocks. Measured: `rg -n "auto_evict|Evicted|equivoc"
node/src/committee_replay.rs` returns **nothing**. There is no eviction in the fold, because there is
nothing in the lace to fold — the eviction was never a block.

Consequences, all measured:

- **An evicted equivocator is a full committee member again after a restart.** `n` and the threshold
  go back up; the equivocator is back in the leader rotation.
- **Two sources of truth that disagree by construction.** `from_checkpoint_trusted`
  (`blocklace/src/finality.rs:2185`) *does* restore `lace.equivocators` from the checkpoint (`:2200`),
  so the lace remembers and the constitution forgets. Nothing reconciles them: `equivocators()` has
  **zero call sites in `node/src`** (repo-wide it appears only in `redteam/`, `preflight/`,
  `dregg-analyzer/`, and inside `blocklace/`).
- **`LeaveReason::Evicted` (`blocklace/src/constitution.rs:224`) is never constructed anywhere in the
  repo.** The on-chain shape for recording an eviction exists and is dead. This is the
  never-keep-a-no-op case from `CLAUDE.md` — a reader trusts it.

### 0.4 The Byzantine-repelling protocol — the thing that *proves* "finite harm" — is entirely absent

Our design cites the blocklace's harm bound as a property we inherit. We do not implement the protocol
that establishes it. BC §5.3 is short and concrete, and we have none of it:

| BC §5.3 requirement | Ours |
|---|---|
| accept a set `S = ⌊b⌋ ∩ D` only if the resulting `B′` is **Byzantine-repelling** (`brep`, Def. 5.3) | no `brep` check anywhere |
| **buffer `r`-blocks until `r` acknowledges a known Byzantine `q`** (§5.1 principle 3, §5.2) | `OrphanBuffer` buffers on **missing predecessors only** (`node/src/catchup.rs:169`, `:255`, `:404`) |
| `byz(B)` includes creators of non-`brep` blocks (§5.2) | no such predicate |
| `wf(b, B)`: pointers must be **pairwise incomparable** (Def. 4.1) | `insert_checked` (`finality.rs:1527`) checks only closure (`:1529`–`:1537`); the signature/roster pin is the caller's (`receive_block_pinned`, `:1498`–`:1520`); no antichain check on an incoming pointer set |

The buffer discipline is the *entire content* of Prop. 5.5 (Finite Harm). Its proof turns on `R_q(B)`
— the set of nodes that have not yet acknowledged `q` as Byzantine — shrinking by one every time we
admit a `q`-block, and admitting a `q`-block only via an `r`-block that acknowledges `q`. Without
that gate there is no `R_q(B)` and no bound: **a colluder can feed us an unbounded number of
equivocator blocks forever** (BC §5.1: "a colluder `p` can remain undetected indefinitely, allowing it
to create any number of blocks, preceded by any number of blocks from the Byzantine node `q`,
indefinitely, and thus polluting the blocklace of any node accepting `p`-blocks").

Colluders are not exotic. BC Def. 5.2 makes a colluder simply a node that never acknowledges `q`, and
observes that a colluder "can be exposed only at infinity" — the buffer is the *only* answer the paper
has, and it is the one thing we skipped.

### 0.5 We punish the node that delivers the evidence

`handle_push`, on detecting an equivocation, calls
`handle.gossip.penalize_equivocation_relay(from)` (`blocklace_sync.rs:5592`), which
graylists the relaying peer and evicts it **from every topic's eager set**
(`net/src/gossip.rs:1348`–`:1358`).

Under BC, relaying an equivocation is the *correct* behaviour and the mechanism the whole harm bound
runs on: Prop. 5.5's proof is a chain of correct nodes receiving evidence and forwarding it, and
Lemma A.1 (Byzantine Convergence) requires that "`p` will eventually send `⌊b⌋` to `q`, **including
`r`-blocks that constitute evidence for `r` being Byzantine**." The relay we demote is, in the paper's
model, doing its job.

The amplification is cheap and one-sided: **one** fork block, broadcast once, demotes the mesh
position of every honest node that forwards it. The code's own comment distinguishes the network-layer
penalty from the consensus-layer evict and says the block "still propagates" — but propagation is
exactly what the eager/lazy demotion slows, and it slows it for *all* topics, not just this one.

### 0.6 Housekeeping: the citation in `finality.rs` names the wrong authors

`blocklace/src/finality.rs:1724` cites "paper Almog–Lewis–Naor–Shapiro arXiv:2402.08068 Def 4.2". The
paper at that arXiv id is **Paulo Sérgio Almeida and Ehud Shapiro** (title page). The *definition* is
cited correctly and the implementation matches it; only the attribution is wrong. Noted because it is
the sort of thing that only survives in a codebase where nobody has opened the PDF.

---

## 1. What the CRDT paper establishes, and whether we satisfy the hypotheses

### 1.1 The two propositions

BC proves exactly two things about the protocol, both in §5 with proofs in App. A:

> **Proposition 5.4 (Eventual Visibility).** Any block in a blocklace of a correct node is eventually
> in the blocklace of every correct node.

> **Proposition 5.5 (Finite Harm).** If `p` is correct and there is public evidence that `q` is
> Byzantine then `p` will eventually stop including `q`-blocks in its blocklace.

The abstract's headline — *"a Byzantine node may harm only a finite prefix of the computation"* — is
Prop. 5.5 plus the observation (§5, opening) that this leaves "a potentially-infinite suffix of the
computation Byzantine-free." **Note what it is not.** It is not a bound on how much harm; it is not a
safety property; it is not about ordering at all. It says: eventually you stop taking their blocks.
The "finite prefix" is *unbounded* in size — bounded only by the number of nodes that have not yet
acknowledged the equivocation (App. A, proof of 5.5: `R_q(B)` is finite to begin with, so it can be
drained finitely many times).

### 1.2 The hypotheses, and where we stand

| BC hypothesis | Where stated | Do we satisfy it? |
|---|---|---|
| **Correct nodes form a connected graph**, so any message received by a correct node is forwarded along correct nodes | §1, §4 (citing Kleppmann–Howard [10]) | ⚠ **Assumed, and we actively work against it.** `penalize_equivocation_relay` (§0.5) demotes correct relays out of the eager set on the exact message the axiom is about |
| **Node Liveness / Production** — a correct node "produces an initial `p`-block and produces new `p`-blocks **indefinitely**" | Def. 5.1.1 | ✅ **by default, off by a flag.** `--idle-heartbeat-ms` default `120000` (`node/src/lib.rs:300`–`:301`) emits one signed heartbeat block linking current tips every 2 min when idle. `0` disables it (`blocklace_sync.rs:12594`) and **voids the axiom**, hence both propositions |
| **Node Liveness / Dissemination** — eventually send **each block in the closure of every `p`-block** to every correct node | Def. 5.1.2 | ✅ for closure-reachable blocks (`handle_frontier` `to_send`, `blocklace_sync.rs:5886`–`:5920`, iterates the whole lace, not the closure — strictly more than required) |
| **Block well-formedness** `wf(b, B)`: `¬∃a,b ∈ P · B[a] ≺ B[b]` — the pointer set is an **antichain** | Def. 4.1 | ❌ **not checked on ingest.** `insert_checked` (`finality.rs:1527`) checks only closure. Our *own* blocks satisfy it by the tips map; incoming ones are unverified |
| **Validity is a function of the block's own causal past** — `valid(v, ≺b)`, "regardless of concurrent updates that may be present" | §1, §4.1, §4.3 | ✅ where it exists. `validated_consensus_time_frontier_v1` (`finality.rs:1389`) derives from `predecessor_consensus_time_frontier_v1` — the block's own predecessors. Correct shape |
| **The Byzantine-repelling protocol** (`brep` invariant + the acknowledge-before-admit buffer) | §5.2, §5.3 | ❌ **absent entirely** (§0.4) |

**Verdict on Q1: we satisfy the axioms about the network and (by default) about production; we
satisfy none of the protocol.** Prop. 5.5 is therefore not available to us, and the "finite prefix"
framing should not appear in our documentation as a property we have.

### 1.3 What "universal CRDT" buys, and what we are leaving on the table

BC §3 establishes the blocklace as **both** a pure operation-based CRDT with self-tagging (§3.2) and a
delta-state CRDT under a generalisation of the delta framework (§3.3). The universality claim (§3.1,
§7) is: with arbitrary payloads and a per-datatype `valid` predicate, one blocklace is a universal
Byzantine-fault-tolerant host for *any* op-based CRDT.

The mechanism is BC §4.3:

```
polog(B) = ({b ∈ B | wf(b) ∧ valid(b) ∧ node(b) ∉ byz(⌊b⌋)}, ≺)
valid(b) = valid(v, polog(≺b))
```

Read `node(b) ∉ byz(⌊b⌋)` carefully, because it is the single most useful line in the paper for us:
**exclusion is a predicate over the block's own closure.** It is deterministic, it converges without
coordination, it needs no message, no vote, no membership mutation, and no agreement about *when*
anyone learned anything. Every node computes the same `polog` from the same blocklace. That is what a
CRDT is for.

BC §4.1 makes the design choice explicit, and it is the choice we did not make:

> There are two design options regarding the behavior of a node upon the receipt of a correctly-signed
> `p`-block that is not well-formed or not valid:
> 1. Discard the block.
> 2. Accept the block into the blocklace, resulting in all nodes eventually knowing that `p` is
>    Byzantine.
>
> … **We adopt the second option**, as it ensures that in an infinite computation the harm a Byzantine
> node may cause is finite. It requires that the payload of invalid blocks be **ignored from the
> perspective of the data type**.

We do option 2 for *storage* (we retain the fork block as evidence — `finality.rs:1541`–`:1554`,
faithful) and then implement the "ignore from the perspective of the datatype" half as a live-state
mutation instead of as a predicate over the closure.

**Three things we hand-rolled that the structure already provides:**

1. **The finalization-vote channel** (`node/src/finalization_votes.rs`) is a second attestation surface
   with an invented first-write-wins equivocation policy (`:596`) and no connection to
   `Blocklace::equivocators()`. In the papers there is no vote message at all — ratification is
   ordinary blocks (CM Alg. 1:18–19), so "voting twice" *is* blocklace equivocation and is caught by
   machinery that already exists. As a block payload it would be one `valid` predicate.
2. **The join handshake's first leg** is a gossip envelope, not a block — `blocklace_sync.rs:662`–`:664`:
   *"it is not a block, never enters the lace, and registers nothing."* A committee member then authors
   the on-chain `Join` proposal under its own key, so the ratification half *is* in the lace. GSN Alg. 3
   lines 37–40 puts **both** halves in as ordinary blocks (invite and accept) and derives membership as
   a predicate (`member(q, B)`, Alg. 3:58) — no sponsor re-authorship, and the candidate's own consent
   is a block anyone can check rather than an envelope one member vouched for.
3. **The eviction** (§0.1–§0.3). `node(b) ∉ byz(⌊b⌋)` is the whole thing, and it is convergent,
   restart-durable and fork-free for free.

Each of these is a channel where we had to invent an equivocation policy and a convergence story from
scratch, for a system whose datatype's stated selling point is that it supplies both.

**And the cost the paper warns about is the one we are paying.** BC §1 and §4:

> a single Byzantine node can create states denoting a degree of concurrency only achievable by much
> more than `n` correct nodes. The high degree of the underlying DAG needed to achieve convergence
> will prevent optimized structures for processing queries.

The blocklace is meant to be a *secure PO-Log* that "warrants optimizations for querying or compact
long term storage of information which has become stable" (§4). We do not run those optimisations, and
the reason we cannot bound the pollution that would break them is §0.4.

---

## 2. Equivocation exclusion, precisely

The question was: *is `auto_evict_equivocator` what the papers mean by exclusion, or something else
wearing its name?* **Something else.** The papers have three distinct mechanisms and we have collapsed
all three into one live-state mutation that is none of them.

### 2.1 The three mechanisms, kept apart

**(a) Detection** — `eqvc(B)` (BC Def. 4.2): a pair of distinct `p`-blocks incomparable under `≺`.
This is a pure predicate on a blocklace. BC's remark is important and we honour it: *"a node `p` can
belong to `eqvc(B)` even if no block in `B` observes an equivocation by `p`; the existence of a pair
of incomparable `p`-blocks in `B` is enough."* Our `detect_equivocation` (`finality.rs:1743`) is
exactly this, content-independent, and its docblock explains correctly why the old `(creator, seq)`
heuristic was a strict subset. **✅ Faithful.**

**(b) State-layer exclusion** — `node(b) ∉ byz(⌊b⌋)` (BC §4.3), and CM's `approves` / `xsort`
(Alg. 1:17, Alg. 2:39–40). Evaluated over **a fixed causal past**, therefore deterministic and
identical on every node. CM Fig. 4.C is the picture: the green leader includes the red block (it does
not observe the equivocation), the purple leader excludes it (it does). *Different anchors legitimately
disagree; two nodes computing the same anchor never do.* **We implement the predicate
(`approved_by`) and cannot reach it (§0.2).**

**(c) Repelling** — CM Def. 29 and §3, BC §5.2–§5.3. Forward-looking, and again **per-block**:

> CM Def. 29 (Equivocator-Repelling). Let `b ∈ B` be a `p`-block that acknowledges a set of blocks
> `B ⊂ B`. Then `b` is equivocator-repelling if `p` does not equivocate in `[b]` and all blocks in
> `B` are equivocator-repelling.

and the operational reading, CM §6.2:

> once an equivocation by miner `q` is observed by a block `b`, `q` would be repelled: **Any block that
> observes `b` would not acknowledge any `q`-block**, preventing any further `q`-blocks from joining
> the blocklace.

Note what repelling *is*: a rule about which blocks a new block **points at**. It changes the DAG's
future edges. It does not change `Π`, it does not change the threshold, it does not delete anyone from
a roster. CM Prop. 39 (Equivocators-Free Suffix) is the payoff — a depth `d` beyond which the suffix
contains only non-equivocator blocks — and its proof requires the antecedent we destroy: *"Since `B` is
disseminating, there is some `d`-suffix of `B` in which **all blocks observe these equivocating
blocks**."* Our blocks observe neither.

BC's repelling adds the colluder handling on top: buffer `r`-blocks until `r` acknowledges `q`
(§5.1–§5.3). Also purely local, also no membership change.

### 2.2 When does a node become excluded, and what happens to its earlier blocks

**The papers' answer:**

- There is **no instant** at which a node becomes excluded globally. Exclusion is not an event; it is a
  predicate that different blocks evaluate differently depending on what they observe. BC Lemma A.1
  gives only a *Byzantine Convergence Time* — a time after which all new correct blocks agree on
  `byz(⌊b⌋)` — and it is not observable.
- **Blocks authored before exclusion keep their status.** Under BC §4.3 a block `b` is in the PO-Log
  iff `wf(b) ∧ valid(b) ∧ node(b) ∉ byz(⌊b⌋)` — evaluated against **`b`'s own past**. A block created
  before its author equivocated has no equivocation in its past, so it stays. Under CM the same:
  `approves(b, b1)` fails only for an anchor that *observes* the equivocation, so an earlier anchor's
  segment keeps the block (CM Fig. 4.C, the V-marked red block).
- **Blocks authored after** are excluded by the repelling rule — nobody points at them, so they never
  enter any anchor's closure, so they are never ordered.

**Our answer:** the instant a gossip datagram arrives at *this* node. Retroactive, global-in-scope
(the member leaves the quorum denominator, changing the leader schedule for **every** wave including
already-anchored ones), node-local in effect, unrecorded, and reverted by a restart. It is not part (a)
(we already have that), not part (b) (unreachable), and not part (c) (which never touches `Π`).

**The one place we exceed the papers, and it is real:** the slashing path
(`crate::equivocation_court_service::slash_from_proof`, `blocklace_sync.rs:5603`) has no counterpart in
either paper. CM and BC have no economic layer at all. That is ours and it is legitimately more than
the literature offers.

### 2.3 Why the arrival-ordered rule is unsafe here specifically

BC §5.1 states the general reason in one sentence:

> Due to network asynchrony, different nodes may observe two equivocating blocks in a different order,
> so **excluding the second block of an equivocation may violate eventual visibility**. Furthermore, an
> equivocator may create more than two equivocating blocks, so different nodes may initially observe
> different equivocations by the same node.

We do not exclude the second *block* (we retain it — good). But we do take an irreversible action
keyed on the arrival of the second block, and the sentence's logic transfers exactly: arrival order is
the one thing that differs between correct nodes, so it is the one thing a consensus-relevant decision
must not depend on. `auto_evict` makes the leader schedule depend on it.

---

## 3. Cordial dissemination vs cordial ordering — what we may claim

**The prior lane's finding is confirmed at source, and it is if anything stronger than reported.**

### 3.1 The corpus names Cordial Miners as not grassroots

GS §2.1, immediately after Theorem 13 (verified verbatim, GS p. 7):

> We note that blockchain consensus protocols with hardcoded miners, e.g. the seed miners of Bitcoin
> [12] or the bootnodes of Ethereum [13], as well as **permissioned consensus protocols with a
> predetermined set of participants such as Byzantine Atomic Broadcast [30, 16]**, are all
> **interfering**, as additional participants cannot be ignored.

GS reference [16] (verified, GS reference list): *"Idit Keidar, Oded Naor, and Ehud Shapiro. Cordial
miners: A family of simple and efficient consensus protocols for every eventuality. DISC 2023."*
**Confirmed: Cordial Miners is the cited example of a non-grassroots protocol.**

And grassroots consensus is named as open (GS §2.1, the next paragraph, verified verbatim):

> However, Theorem 13 and the examples above do not imply that ordering consensus protocols cannot be
> grassroots. The problem is not with the consensus protocol as such, but **with the choice of its
> participants**. … **Devising grassroots consensus protocols is a subject of future work.**

### 3.2 Cordial Dissemination *is* grassroots, as a protocol

GS Prop. 29: *"The Cordial Dissemination protocol CD is grassroots."* GS §3 gives the two principles
(p. 11):

> 1. **Disclosure**: Tell your friends which blocks you know and which you need
> 2. **Cordiality**: Send to your friends blocks you know and think they need

and the realisation (GS §3.2): *"Disclosure is realized by **a new `p`-block serving as a multichannel
ack/nack message**, informing its recipient whether it follows another agent `q`, and if so also of
the latest `q`-block known to `p`, for every `q ∈ P`."*

### 3.3 Therefore — exactly which of our claims are supportable

| Claim | Supportable? |
|---|---|
| "Our ordering layer is grassroots" | ❌ **No.** GS §2.1 names CM as the counterexample. Never claim this |
| "Our dissemination implements the Cordial Dissemination *mechanism*" | ✅ Yes — with the §4 caveats about the side channels |
| "Our dissemination *is grassroots* (inherits GS Prop. 29)" | ❌ **No.** Prop. 29 is about CD as a protocol over a freely-chosen social graph. Ours runs over a predetermined committee: `handle_peer_addrs` accepts an address only when the key is in our own `known_federation_keys` (`blocklace_sync.rs:5488`ff, and the docblock says so: *"discovery learns ADDRESSES for already-trusted identities; it never admits new identities"*). Additional participants are not merely ignorable — they are unrepresentable |
| "We descend from the grassroots line" | ⚠ **Only as lineage, not as property.** True of the datatype and the dissemination *shape*; false of every theorem |

**One additional finding, and it is GS's own argument turned on us.** GS §2.1 rules Bitcoin
non-grassroots partly because *"two instances of the protocol would interfere on the assigned global
port numbers."* Our gossip topic is a **global constant string**:

```rust
node/src/blocklace_sync.rs:45:  pub const TOPIC_BLOCKLACE: &str = "dregg/blocklace";
```

not namespaced by `federation_id`, and it is the only value passed to `join_topic` (`:4502`). Two
dregg federations on one gossip network share the topic. That is GS's port-number interference,
literally. It is also a straightforwardly good idea to fix regardless of grassroots claims — a topic
name is a cheap thing to derive from the genesis anchor.

For completeness on where consensus sits in the corpus's own layering, GA §1 (p. 2) puts equivocation
exclusion **below** ordering consensus and notes that payment systems and social networking need
exclusion but not consensus; GSN §1 says the same (*"require also equivocation exclusion, but neither
require consensus"*); GF §6.1's table lists Grassroots Flash as `Consensus-based: No`. **Consensus is
the one layer the grassroots line has not delivered.** We are building it. That is fine, and it is
ours to justify — it is simply not descent.

---

## 4. What the blocklace gives us that we are not using

### 4.1 It is a delta-state CRDT, and our merge already is the paper's merge

BC §3.3 defines the generalisation precisely:

> - support lattice: powerset of blocks;
> - state lattice: lattice of sets of blocks closed under `≺`.
>
> The join is simply **set union**. … Given local state `B` and delta group `D`, the condition becomes
> `⌊D⌋ ⊆ B ∪ D`.

`Blocklace::merge` (`finality.rs:1592`–`:1661`) implements exactly that condition:

```rust
                if !self.blocks.contains_key(pred) && !delta_ids.contains_key(pred) {
                    return Err(MergeError::NotCausallyClosed { missing: *pred });
```

**✅ This one we got right, and it is worth saying so.** The paper's stated payoff follows: *"Possibility
of small messages, tolerance of duplicates through the idempotency of join, and tolerance to message
loss by allowing retransmission of the same or newer delta-groups that subsume the lost message."*

Two notes. (i) The live ingest path does *not* go through `merge` — `handle_push` routes to
`catchup::apply_with_buffering` (`node/src/catchup.rs:347`), which uses `receive_block_pinned`
(`:387`) and so applies the hybrid roster pin; `merge` only calls `verify_signature` (`finality.rs:1617`).
That is the safer arrangement, but it means the CRDT join and the production ingest are two code paths
with different admission rules. (ii) `apply_with_buffering`'s orphan buffer is the paper's `D`
(BC §2.4: *"a received block that points to blocks not yet in `B` is buffered"*) — correct, and the
natural place to add the §5.3 acknowledge-before-admit gate, which is the same buffer with one more
condition.

### 4.2 The block is the frontier message — we send a third copy of it

BC §6, the whole of Cordial Dissemination:

> a `p`-block `b` by a correct node `p` acknowledges all the blocks known to `p` at the time of block
> creation (**and, by omission, reports on all the blocks not known to `p`** at the time). Thus, when
> `q` accepts the `p`-block `b` it eventually cordially responds by sending to `p` all the blocks known
> to `q` but not to `p`, **according to `b`**. The response may be arbitrarily lazy or even
> probabilistic.

Our blocks already carry this: `try_add_block` points at every tip (`finality.rs:1220`), so the
pointer set of any block we author **is** `Frontier { tips }`. And yet we ship, on the wire:

```rust
node/src/blocklace_sync.rs:301:  Frontier { tips: HashMap<[u8; 32], BlockId>, nonce: u64, votes: Vec<…> },
node/src/blocklace_sync.rs:297:  Pull { ids: Vec<BlockId>, nonce: u64 },
node/src/blocklace_sync.rs:300:  PullResponse { blocks: Vec<Block>, nonce: u64 },
```

`Frontier.tips` is `blocklace.tips().clone()` (`blocklace/src/dissemination.rs:514`) — the identical map
the block's pointer set already encodes. The `nonce` exists (`:303`–`:312`) because a stalled node
re-emits a byte-identical frontier that gossip hash-dedup drops. **A `p`-block never has that problem:
it carries a fresh signature and a new self-pointer, so it is byte-unique by construction.**

`Pull`/`PullResponse` have no counterpart in CD at all — the response is unilateral and lazy, derived
from the peer's block. CM Alg. 3 line 57 likewise: *"The package sent to miner `q` contains any blocks
up to the previous round that `p` knows that `q` might not know, **based on the last block received
from `q`**."* No request message exists in either protocol.

**Why we needed the side channel, and what the papers say about that.** `handle_frontier`'s own
comment (`blocklace_sync.rs:5822`–`:5837`) explains it exactly:

> At `n>1` the round-synchronous rule needs a SUPERMAJORITY of distinct creators at a round before any
> node may advance (n=3 ⇒ all three), so when the committee advances rounds concurrently every node
> ends a round holding its OWN newest block but missing its peers' newest blocks. … nothing ever
> re-requests it … the cluster wedges one block short of the round cohort FOREVER.

That is a real wedge and the patch works. But the root cause is that **we gated block production on
round completion and then had nothing to say when the round cannot complete.** CM has the same gate
(Alg. 3:52 `completed_round()`) and a different answer: Alg. 4 line 67, `es_advance_round()`, which
advances on the per-round condition **or a timeout**, with CM §6.2 giving the reason and Prop. 38
(leader-liveness w.p. 1) stated only under `timeout > ∆`. `blocklace_wave_timeout_ms` is threaded
through `run_blocklace_sync` (`node/src/lib.rs:2888`, `blocklace_sync.rs:4088`ff) — **whether it
actually gates round advance in the CM sense was flagged as unaudited by the prior pass and is still
unaudited.** It is the next thing to check and it is the difference between a protocol-level answer and
a ping.

### 4.3 What is on the table, ranked

1. **`node(b) ∉ byz(⌊b⌋)` as the exclusion rule** (BC §4.3). Convergent, restart-durable, needs no
   membership mutation, no message, and no agreement about timing. Directly replaces §0.1–§0.3.
2. **Payloads instead of channels** (BC §3.1). Finalization votes, the join handshake, and the eviction
   record are all block payloads with a `valid` predicate over the block's own past. Each one moved
   into the lace deletes an invented equivocation policy.
3. **The acknowledge-before-admit buffer** (BC §5.3). One extra condition on a buffer we already have,
   and it is what makes "finite harm" a property rather than a slogan.
4. **`wf` on ingest** (BC Def. 4.1) — the antichain check on an incoming pointer set. Cheap, local,
   per-block, and it is the CRDT paper's sibling of CM's cordiality check that the prior pass found
   missing (`CONSENSUS-FROM-SOURCE-2026-08-08.md` §5.1). **These are two different checks and we have
   neither.** Cordiality: the pointer set covers a supermajority of the previous round. Well-formedness:
   the pointer set is an antichain. Both are one pass over `b.pointers`.
5. **PO-Log compaction** (BC §4). Only reachable once (3) bounds the pollution.

---

## 5. The two-tips-per-miner cap: what it protects, what is exposed

**CM Alg. 1 line 5, verbatim:**

```
 5:    b.pointers ← hash(tips), where tips are the tips of blocklace_prefix(d), at most two tips per miner
    ▷ Def. 19; two-tips limitation to prevent a Byzantine miner from flooding the blocklace before being
    excommunicated
```

**The flood it prevents.** BC §2.4 says a correct node's block points at `ids(max≺(B))` — *all*
maximals. An equivocator producing `k` mutually-incomparable blocks puts `k` maximals in `max≺(B)`, so
**every honest block's pointer set grows by `k`**, and every honest block is relayed by every miner.
CM §7 prices the blowup: each block is `O(n)` in size, a Byzantine block costs `O(n³)` bits because
every correct miner sends it to every other. Uncapped, the equivocator sets `k` and multiplies that.
The cap makes the pointer set `≤ 2n` regardless of `k`.

**Why the number is two and not one.** One tip per miner is sufficient for an honest chain (BC Def. 2.6,
the virtual chain axiom: any two `p`-blocks by a correct `p` are comparable, so a correct miner has
exactly one maximal block). **Two is the minimum that can carry an equivocating pair into the next
block's closure.** That is what every downstream mechanism needs:

- CM `approves(b, b1) = b1 ∈ [b] ∧ ∀b2 ∈ [b] : ¬equivocation(b1, b2)` (Alg. 1:17) — needs both halves
  in `[b]`.
- CM Lem. 31 (at most one of an equivocating pair can hold supermajority approval) — quantifies over a
  blocklace containing both.
- CM Prop. 39 (Equivocators-Free Suffix) — its proof opens *"there is some `d`-suffix of `B` in which
  **all blocks observe these equivocating blocks**."*
- BC `byz(⌊b⌋)` (§4.3) — needs the pair in `⌊b⌋`.

So "at most two tips per miner" is a cap on the flood **and simultaneously a floor on the evidence**.
Read only as a cap, it looks like a nice-to-have. It is load-bearing in both directions.

**What we have instead.** `tips: HashMap<creator, BlockId>` (`finality.rs:1198`) — structurally one per
creator, dropping to zero on detection (`:1543`, `:1631`, `:1968`, never restored `:1556`).

**So the flood exposure is CLOSED — by a stricter cap than CM's — and the evidence floor is BROKEN.**
That is the honest verdict, and it is not the verdict the question expected. Concretely:

| | CM (≤2/miner) | Ours (≤1/miner, 0 after detection) |
|---|---|---|
| pointer-set blowup from `k` equivocations | bounded at `2n` | bounded at `n` ✅ (stricter) |
| equivocating pair reaches a later block's closure | **guaranteed** by construction | only by the race in §0.2 |
| `approves` / `xsort` can exclude | yes | **structurally cannot** |
| Prop. 39 equivocator-free suffix | provable | antecedent destroyed |
| evidence reaches a peer at all | via causal closure — guaranteed by dissemination | via **anti-entropy only**: `handle_frontier`'s `to_send` iterates the whole lace (`blocklace_sync.rs:5902`) and `Blocklace::checkpoint` serialises `self.blocks.values()` (`finality.rs:2007`), so the orphaned half does travel — but as an unreferenced block, outside the causal structure, and therefore never in any ordered history |

The last row is the practical shape of it: the second fork block exists on every node that gossiped
during the window, is pointed at by nothing, is ordered by nothing, and is invisible to every
anchor-relative rule. **The evidence is real and unreachable.** That is why the eviction had to become
a live-state mutation — there was nowhere in the DAG to put it.

**One more exposure the cap would not have covered and we should not conflate with it.** CM's cap is
on *our own* block creation. Nothing in either paper or in our code caps the pointer set of an
**incoming** block: `insert_checked` (`finality.rs:1527`) accepts any `predecessors` vector whose
members are present. A Byzantine miner can therefore ship a block with an enormous pointer set and
force `causal_past` / `round_of` / `approved_by` walks over it on every node. The paper's answer to
that is `wf(b, B)` (BC Def. 4.1) plus cordiality (CM Alg. 1:15) at admission — the checks from §4.3
item 4. We should not add a two-tips rule to block *creation* and call the incoming side handled.

---

## Summary

| # | Question | Papers say | We do | Verdict |
|---|---|---|---|---|
| **1** | "Harm only a finite prefix" | BC Prop. 5.5, under Node Liveness (Def. 5.1) + connected correct graph + **the §5.3 buffer discipline** | Liveness ✅ (heartbeat, disableable); connectivity ⚠ (we demote evidence relays); **buffer discipline absent** | ❌ **not available to us** |
| **1** | Universal CRDT | Pure-op with self-tagging (§3.2) + delta-state (§3.3); one lace hosts any datatype via `valid(v, polog(≺b))` | delta-merge ✅ faithful (`finality.rs:1592`); three side channels re-invent convergence | ⚠ half used |
| **1** | `wf(b,B)` antichain on ingest | BC Def. 4.1 — admission predicate | not checked | ❌ missing |
| **2** | What exclusion *is* | Detection `eqvc(B)` + state-layer `node(b) ∉ byz(⌊b⌋)` over the **block's own closure** + repelling as a **pointer rule**; `Π` never changes | live mutation of `constitution.current.participants` on gossip arrival, changing `n` and the threshold | ❌ **something else wearing the name** |
| **2** | Blocks authored before exclusion | keep their status — the predicate is per-closure (BC §4.3, CM Fig. 4.C) | retroactive and global: the leader schedule changes for every wave | ❌ |
| **2** | Durability | exclusion is a function of the blocklace, so it survives anything | not on chain, not in `committee_replay`, `LeaveReason::Evicted` never constructed → **reverts on restart** | ❌ |
| **3** | Grassroots ordering | CM is GS §2.1's named **non-grassroots** example (ref [16]); grassroots consensus is future work | — | claim is **unsupportable** |
| **3** | Grassroots dissemination | CD is grassroots (GS Prop. 29) over a **freely chosen** social graph | CD mechanism over a predetermined committee; `TOPIC_BLOCKLACE` a global constant | mechanism ✅, **property ❌** |
| **4** | Frontier / catch-up | the **block is** the disclosure (BC §6, GS §3.2); response is unilateral and lazy; no request message | separate `Frontier` (+nonce) and `Pull`/`PullResponse` on the wire | ⚠ hand-rolled; root cause is an unaudited round-advance rule |
| **5** | Two tips per miner | flood cap **and** evidence floor (CM Alg. 1:5) | one tip, then zero | flood ✅ closed stricter; **evidence floor broken** |

### What follows, in order

1. **Make exclusion a predicate over the block's own closure** — BC §4.3's `node(b) ∉ byz(⌊b⌋)` — and
   delete `auto_evict_equivocator`. This is one change that closes §0.1, §0.2 and §0.3 together, and
   it is the paper's design rather than a patch on ours. It pairs with the τ re-anchoring the prior
   pass called for: once τ orders `[anchor]`, the anchor's closure is exactly the domain this predicate
   wants.
2. **Point at both halves of a detected fork.** CM's two-tips rule, in the direction that matters:
   stop `tips.remove` from deleting the evidence path, and let a block carry a detected equivocating
   pair forward. Without this, (1) has nothing to evaluate.
3. **Add the acknowledge-before-admit condition to `OrphanBuffer`** (BC §5.3). It is the only thing in
   either paper that bounds a colluder, and we already have the buffer.
4. **Add `wf` (BC Def. 4.1) alongside cordiality (CM Alg. 1:15) at admission.** Two different one-pass
   checks over `b.pointers`; we have neither.
5. **Stop graylisting equivocation relays across all topics** (`blocklace_sync.rs:5592`). Under BC the
   relay is behaving correctly and the penalty is a cheap DoS amplifier.
6. **Namespace `TOPIC_BLOCKLACE` by the genesis anchor.** Small, and it removes GS's own
   interference argument from applying to us verbatim.
7. **Audit the round-advance rule against CM Alg. 4:67** (`timeout > ∆`, Prop. 38). Still unaudited
   after two passes; it is the protocol-level answer to the wedge our `Frontier` nonce patches.

### Where the papers do not settle it

- **Committee growth.** BC fixes `Π` at §2.1; CM fixes it at §2 and treats only shrinking, as future
  work (App. D). Neither paper says what happens to in-flight waves across a membership change. Our
  join design remains ours to justify.
- **Whether the §0.2 race is exploitable in a specific direction.** I did not construct a witness in
  which two honest nodes point at different halves and a third inherits both — the structural fact
  (nothing *guarantees* the pair enters a closure) is what the argument rests on, and that is read at
  source, not inferred.
- **Whether `blocklace_wave_timeout_ms` implements CM's `es_advance_round`.** Named, threaded, not
  audited. Do not assume either way.
