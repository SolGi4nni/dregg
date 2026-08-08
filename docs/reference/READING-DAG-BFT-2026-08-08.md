# Reading the DAG-BFT lineage: where Cordial Miners sits, and what came after

> ⚑ **STATUS (2026-08-08, evening): C1 LANDED as `d182d10fc`.** Everything below describing OUR τ
> as coverage-based — `leaderCoverage` (deleted), the fold over `find_all_final_leaders` (now feeds
> only head selection; the chain walks ratified leaders inside the head's closure), and
> `FinalizedRegionStable` (deleted; the surviving hypothesis is `ChainExtends`, with
> `ClosedExtension` structural) — is a correct read of the MORNING tree and is historical now.
> The `finalLeaderAt` retraction defect (§3.3's "the more fundamental of the two") is NOT fixed;
> `ChainExtends` absorbs it. C2 (cordiality at admission) is now DEFINED (`isCordialBlock`,
> BlocklaceFinality §5c) but NOT wired to the receive path.

**Date:** 2026-08-08
**Method:** 10 papers read as text from `pdfs/`. Every claim about a paper carries paper +
section/lemma/algorithm-line. Every claim about our code carries `file:line`, verified at source.
**Scope:** read-and-think. No protocol code changed by this pass.

**Companions.** `docs/reference/CONSENSUS-FROM-SOURCE-2026-08-08.md` (`66681e080`) reads Cordial
Miners against our τ and establishes the τ deviation; this doc does not re-derive it, it *confirms
the rule from the rest of the lineage* and adds the variants that legitimately read live state.
`docs/reference/DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md` (`5baa476a8`) reads the reconfiguration
literature; **§4 below corrects one of its negatives** with two papers from this cluster it did not
search.

Citation shorthand. **DR** = Keidar, Kokoris-Kogias, Naor, Spiegelman, *All You Need is DAG*
(DAG-Rider, 2102.08325). **NT** = Danezis, Kokoris-Kogias, Sonnino, Spiegelman, *Narwhal and Tusk*
(2105.11827). **BS** = Spiegelman, Giridharan, Sonnino, Kokoris-Kogias, *Bullshark* (2201.05677).
**SH** = Spiegelman, Aurn, Gelashvili, Li, *Shoal* (2306.03058). **SH++** = *Shoal++* (2405.20488).
**MY** = Babel, Chursin, Danezis, Kichidis, Kokoris-Kogias, Koshy, Sonnino, Tian, *Mysticeti*
(2310.14821). **SL** = Blackshear et al., *Sui Lutris* (CCS '24, 2310.18042). **BY** = Vonlanthen,
Sliwinski, Albarello, Wattenhofer, *Banyan* (2312.05869). **HH** = Tsimos, Kichidis, Sonnino,
Kokoris-Kogias, *HammerHead*. **CM** = Keidar, Naor, Poupko, Shapiro, *Cordial Miners* (2205.09174v6).

---

## 0. The four things this pass changes

1. **Mysticeti makes the *same* move as Cordial Miners and says so — and it found a safety bug in
   CM's preprint.** MY fn. 10: the CM manuscript available during Mysticeti's development
   *"considered a single certificate pattern to be a sufficient condition to commit a block. **This
   is not safe.**"* The published CM fixed it by requiring super-ratification. **We are on the fixed
   rule** — `is_super_ratified` (`blocklace/src/ordering.rs:436`) demands a supermajority of distinct
   enrolled participants at the wave's last round. Verified, no action. (§2.3)

2. **The uncertified DAG has a *measured* cost CM's latency table does not price, and it is not
   small.** SH++ §8.3 injected 1% egress message drop on 5 of 100 nodes: Mysticeti's latency rose
   **10×** while certified Shoal++ rose 1.3×. MY's own production write-up (§VIII) independently
   names the same cause — *"inefficient synchronization of unevenly broadcasted blocks"* — and notes
   it *"was not noticeable in the current Sui blockchain due to the higher latency of Bullshark."*
   The ~2× CM claims (CM abstract) is a *message-delay* count; the fetch is off that ledger. (§2.4)

3. **⚑ The reconfiguration negative was too broad, and this cluster holds the refutation.**
   `DYNAMIC-COMMITTEE-LITERATURE` §3 defended *"nothing in this corpus treats reconfiguration of a
   DAG/blocklace consensus protocol"* — naming the six papers it searched. **It did not search Sui
   Lutris or Mysticeti.** SL §4.2 is a four-step committee reconfiguration protocol for a system
   running **Bullshark** as its consensus engine, with a safety theorem (SL Thm. 1) and **383
   production epoch changes** (SL §1). MY §IV-D states the rule for a pure-consensus DAG in one
   sentence: *"A deterministic consensus commit C sets the boundary between epochs e and e+1."*
   (§4)

4. **⚑ NEW FINDING — we run CM's Eventual-Synchrony leader election with the *asynchronous*
   round-advance rule, and CM names that exact combination as the thing the design prevents.**
   `CONSENSUS-FROM-SOURCE` §5.3 flagged the round-advance rule as unaudited and *"the next thing to
   check."* Checked. `plan_round_block` (`node/src/blocklace_sync.rs:6054`) advances on cordiality
   alone — a supermajority of distinct creators at my current round — with **no leader condition and
   no timeout**, and nothing in the cadence path (`round_cadence_decision:6200`,
   `cadence_tick_round_driven:6450`) is leader-aware. That is CM Alg. 4 **line 59** (the asynchronous
   rule, `w=5`, retrospective coin leader). We pair it with `w=3` and a publicly predictable
   round-robin `wave_leader` (`blocklace/src/ordering.rs:288`) — CM Alg. 4 **line 67**, whose three
   leader clauses and timeout exist, in CM's own words (§6.2), *"to prevent the adversary from
   ordering the messages after GST, in particular, the leader block and the blocks that super-ratify
   it, **as the leader is known in advance**."* CM Prop. 38 (ES leader-liveness w.p. 1) is stated
   only under `timeout > ∆`. **We took the leader-election half of one instance and the
   round-advance half of the other.** This is a liveness hole, not a safety one — but it is free for
   an adversary who controls delivery order, and it is *deterministically* costly for an honest
   member that is merely slow. (§5.3)

---

## 1. Where Cordial Miners sits

### 1.1 The family tree, by what each paper changed

The lineage is one idea — *build a DAG, then read the order out of its structure with zero extra
messages* — refined along four independent axes: **what a DAG edge costs**, **how many anchors per
round**, **who the anchor is**, and **when you may emit**.

| Paper | Year | Edge cost | Anchors | Anchor choice | The contribution |
|---|---|---|---|---|---|
| **DR** | 2021 | Reliable Broadcast | 1 per 4 rounds | shared coin, retrospective | The template: *"once we agree on a sequence of leaders, all that is left to do is to order the causal histories of the leaders in some deterministic order"* (DR §5). Weak edges for Validity. |
| **NT** | 2021 | RB, certified | (Tusk: coin) | — | Splits **dissemination** from **ordering**. A certificate of availability *"includes 2f+1 signatures, ie. at least f+1 honest validators have checked and stored the block"* (NT §3.2). Makes garbage collection tractable (NT §3.3). |
| **BS** | 2022 | RB, certified | 2 per 4 rounds (ES: 1 per 2) | round-robin + fallback | Partial synchrony with an asynchronous fallback; **f+1** votes suffice to order an anchor in the ES variant. First GC that keeps a fairness statement (BS §7). |
| **CM** | 2022 | **best-effort broadcast** | 1 per wave (ES `w=3`) | round-robin (ES) / coin (async) | **Drops RB.** Pays for it inside the ordering function with equivocation exclusion (`approves`/`xsort`). ~2× latency, `O(n)` good-case messages. |
| **SH** | 2023 | RB, certified | **1 per round** (pipelined) | **reputation**, re-derived per anchor | Pipelining + leader reputation over a DAG, and the proof obligation that makes reputation *safe* rather than merely fast. Eliminates the odd-round timeout. |
| **HH** | 2023 | RB, certified | 1 per round | **reputation**, swap `f` worst for `f` best | Deployed reputation. The determinism argument: score *"up to but **excluding** the committed leader."* |
| **MY** | 2023 | **signed, uncertified** | **up to n per round** | predefined total order over slots | CM's move, implemented and hardened: implicit certificates read from the DAG, per-slot `to-commit`/`to-skip`/`undecided`, 3-message-delay commit. Deployed on Sui mainnet 2024-07-25. |
| **SL** | 2023 | (Bullshark below) | — | — | The **reconfiguration** protocol, and the consensusless fast path it has to protect across the boundary. |
| **BY** | 2023 | — (chained, ICC) | rank-ordered, every replica proposes | **rank**, delay ∝ rank | Not a DAG. Its lesson is the *schedule shape*: a leader schedule as a **priority order** rather than an exclusive assignment. |
| **SH++** | 2024 | RB, certified ×3 DAGs | 1 per round × 3 | reputation, candidate sets | Recovers uncertified-DAG latency **without** dropping certificates, and measures what dropping them costs. |

**CM's position: it is the origin of the uncertified-DAG branch, and the branch it originated is the
one that got deployed.** MY §IX credits it directly (*"Cordial Miners has also proposed a similar
DAG-structure to Mysticeti-C"*); SH++ §9 is blunter — *"Mysticeti improves upon Bullshark's best
case latency by transitioning to an uncertified DAG and **implementing the Cordial Miners consensus
protocol**."* Mysticeti's acknowledgements thank Shapiro and Naor for reviewing the related work,
so the attribution is not contested.

### 1.2 What CM changed and, precisely, what it did not

CM changed **dissemination**. It did not change the ordering rule. CM §1:

> When a miner wishes to disseminate a block, it simply sends it to all other miners, taking a
> single round of communication, instead of at least two when using reliable broadcast.

and the price is paid inside τ, not by loosening the anchor discipline — *"by 'complicating' the
local ordering task to exclude equivocations, we forgo the extra communication rounds."* CM's Def. 6
τ′ quantifies over `[b]`, the anchor's own closure, exactly as DR Alg. 3 line 54 quantifies over
`path(v, v′)`. **This is the single most important structural fact about CM's position in the
lineage: it is a dissemination-layer paper wearing an ordering-layer proof.** Everything in §3 below
follows from it.

---

## 2. Uncertified DAGs: CM vs Mysticeti

This is the comparison the brief asked for, because an uncertified DAG is what we run.

### 2.1 They make the same move, but replace RB with different things

Both drop reliable broadcast. What each puts in its place differs, and the difference is where the
hazards live.

| | **CM** | **MY** |
|---|---|---|
| What a block carries | signature + hash pointers to tips, ≤2 per miner (CM Alg. 1 line 5) | signature + ≥2f+1 hashes of previous-round blocks, **first hash must be the author's own previous block** (MY §II-C) |
| Admission rule | `correct_block(b)`: pointers cover a supermajority of round r−1 **and** `¬equivocator(b.creator, [b])`; *"incorrect blocks are ignored"* (CM Alg. 1:15–16, Alg. 3:49) | block validity: signature valid, author in the validator set, all hashes to **distinct valid blocks**, self-link present, ≥2f+1 from round r−1 (MY §II-C) |
| Certification | none as a message; **super-ratification** is read out of the DAG | none as a message; the **certificate pattern** is read out of the DAG (2f+1 round-r+1 blocks supporting B; any later block containing that pattern is a *certificate*) |
| Equivocation, at the block layer | **abstain**: `approves(b,b1)` is false if `[b]` contains any equivocation of `b1` (CM Alg. 1:17) — Fig. 1.B, *"approves neither"* | **pick**: a block **supports** the first block for slot `(A,r)` reached in a depth-first traversal of its own references (MY §II-C) |
| Equivocation, at the commit layer | exclude both from `xsort`; **repel** the equivocator going forward (CM §3, Def. 29) | *"even if A equivocates and one of its blocks is certified, we process it as being correct – despite the self evident Byzantine behavior"* (MY §II-C) |
| Why at most one survives | Lem. 31: at most one of an equivocating pair can hold supermajority approval | Lem. 4 + Lem. 5: a correct validator never supports two proposals for a slot, hence at most one is ever certified |

**Both are "uncertified" only in the message sense.** Each still has a certificate; it is just
*derived* from DAG structure rather than *collected* as signatures. That is worth saying plainly
because it dissolves a false comfort: dropping RB does not drop the 2f+1 quorum, it relocates it.

**The one genuinely divergent design choice is the equivocation policy**, and it is a real fork in
the road:

- CM's abstain is **conservative and self-healing**: an equivocating leader anchors nothing, and the
  equivocator is repelled. Its cost is liveness — MY §IX's jab is that CM's blocklace *"detects and
  excludes equivocating miners so that it can eventually converge **when there is no misbehavior**."*
- MY's support-first-in-DFS is **live but blunt**: it commits a Byzantine author's block when that
  block wins the support race, and relies on Lem. 5 to guarantee the winner is unique. Its cost is
  that a proven-Byzantine block enters the ledger.

We took CM's side (`hasEquivInPast` in `leaderSegment`; `EquivocationIndex` in `ordering.rs`), which
is the conservative one. No change indicated. But see §2.2 — the *mechanism* MY needs to make
support work is one we should want anyway.

### 2.2 The hazard CM does not discuss #1: support stability needs a self-link

MY Lem. 4 — *"For any slot s ≡ (v,r), a correct validator never supports two distinct block
proposals from validator v in round r **across all of its blocks**"* — is proved like this:

> Since a correct validator **first includes a reference to its own block from the previous round**,
> once a correct validator supports a certain block for s, it continues to support the same block in
> all of its future blocks.

The self-link is a **block-validity rule** (MY §II-C: *"By convention, the first hash must be to the
previous block of A"*), and MY fn. 2 notes it also carries the safety of fast-path transactions
across an epoch change. **CM has no self-link requirement.** CM does not need one for `approves`
(abstention is a function of `[b]` alone), but the general principle transfers: *a verdict a
validator will be held to should be forced monotone by the block format, not by the validator's good
behaviour.*

**Our status.** `plan_round_block` (`node/src/blocklace_sync.rs:6054`) links the *whole* cohort at
`my_max_round`, which necessarily includes our own block at that round — so we self-link **in
practice**. But `insert_checked` (`blocklace/src/finality.rs:1527`) validates only **closure** (every
predecessor known). It does not check cordiality and it does not check the self-link. So a Byzantine
author can produce a block that is admitted and is not linked to its own strand. Cheap to add; the
right time to add it is alongside cordiality (see §6, item C2).

### 2.3 The hazard CM does not discuss #2 — because Mysticeti found it in CM

MY fn. 10, in full:

> The Cordial Miners manuscript publicly available during Mysticeti's development considered a
> single certificate pattern to be a sufficient condition to commit a block. **This is not safe.** As
> we saw in our proofs, there is a need for 2f + 1 blocks certify a block to safely commit it. The
> published version of the work, that appeared concurrently to this work, fixes this issue.

This is a peer finding an actual safety bug in the paper we descend from, and it names the exact
predicate to check. **Checked at source, and we are clean:** `is_super_ratified`
(`blocklace/src/ordering.rs:436`) collects `block.creator` over wave-last-round blocks that
`ratifies_enrolled` the leader into a `HashSet`, and requires
`ratifying_participants.len() >= supermajority_threshold(participants.len())`. That is 2f+1 distinct
certifiers, not one. `find_all_final_leaders` (`:483`) is the only caller.

Two caveats worth recording, neither of which is the fn.10 bug:
- The set of wave-end blocks is drawn from the **live** `rounds` map, which is the τ deviation
  already documented in `CONSENSUS-FROM-SOURCE` §0, not a separate defect.
- MY's bar is 2f+1 *certificate blocks* (round r+2 objects that each contain a 2f+1 support
  pattern), i.e. one level deeper than 2f+1 *votes*. CM's super-ratification is the same two-level
  shape and ours implements CM's. The predicates coincide at the level that matters.

### 2.4 The hazard CM does not discuss #3: data fetching on the critical path

This is the highest-value item in the comparison, because it is **measured** and it applies to us at
full strength.

SH++ §3.3:

> removing certificates makes the DAG brittle: it can introduce a significant amount of unwanted
> synchronization on the critical path and increase susceptibility to timeout violations. **Edges to
> uncertified, yet locally unavailable proposals must be validated by fetching missing data (at least
> 2 additional md per round)** before advancing to avoid losing liveness in the face of Byzantine
> fabrications or unstable networks.

SH++ §9, on Mysticeti specifically: *"A single Byzantine (or slow) replica, for instance, can impose
at least 2 additional message delays per round in Mysticeti by not fully (or timely) disseminating
its node proposals."*

SH++ §8.3, the measurement (100 nodes, 18k tps, 700ms median for both systems before injection):

> We inject network layer message drops for 1% of egress traffic in 5 nodes (out of 100 total)…
> Upon failure injection the latency of Mysticeti rises sharply (**by a factor of 10x**) as replicas
> scramble to perform critical-path synchronization on missing data (resulting, at times, in
> timeouts). … Shoal++, in contrast, remains largely unaffected by message drops (latency rises to at
> most 1.3x). **Because all nodes are certified, the DAG construction process… proceeds smoothly; any
> required synchronization is asynchronous and off the critical path.**

This is not only the competitor's framing. **Mysticeti's own production account says the same
thing** (MY §VIII): the first geo-distributed deployment *"did not meet expectations… noticeably
higher tail latency and jitters. We discovered several contributing factors including **inefficient
synchronization of unevenly broadcasted blocks**"* — and, tellingly, *"The synchronization issue was
not noticeable in the current Sui blockchain due to the higher latency of Bullshark."* The fix was
engineering (better block synchronization, TCP with streaming), not a protocol change.

MY's own liveness proof carries the cost explicitly: Lem. 8 (Round-Synchronization) budgets
*"2·∆ to request any missing parent block"* and Lem. 10 sets the certificate-creation wait at **4·∆**.

**Why this lands on us harder than on Mysticeti.** `insert_checked`
(`blocklace/src/finality.rs:1527`) rejects a block whose predecessors are not all present
(`BlockError::MissingPredecessor`) and `merge` rejects a non-causally-closed delta. That is the
correct rule — CM Alg. 3:49 and DR §5 both require it, and it is what makes "two correct processes
always have the same causal history for any vertex they both have in their DAGs" true. But it means
**every missing predecessor is a hard stall until a fetch completes**, and we have no certificate to
tell us in advance that the missing block is *retrievable*. In a certified DAG, 2f+1 signatures mean
f+1 honest nodes hold the block; in ours, a referenced block may simply never have been sent to
anyone but the referrer.

**This is a real, unpriced operating cost of the design we chose. It is not a reason to abandon the
design** — Mysticeti runs it on 137 validators in production — **but the mitigation is engineering
we have not built:** an off-critical-path block synchronizer with fetch-ahead, and a bound on how
long a producer will wait on a missing parent before it stops treating that peer's tips as usable.
Ranked in §6 as C4.

### 2.5 The hazard CM does not discuss #4: emit-order backpressure

MY §III-B step 3, and the sentence just after Fig. 4:

> the validator iterates over that sequence, committing all slots marked as to-commit and skipping
> all slots marked as to-skip. **This iteration continues until the first `undecided` slot is
> encountered.**
> … unlike prior work that commits everything the moment a decision rule exists, **Mysticeti-C
> applies some backpressure through undecided slots to preserve safety.**

MY §III-A says why the `undecided` state exists at all: it *"forces all subsequent proposer slots to
wait, mitigating the risk of non-deterministic commitments due to network asynchrony without the need
for a buffer round."*

CM has no analogue because CM has one anchor per wave and its τ recursion is anchored on the last
final leader. The moment you have *more than one* candidate anchor whose decisions can land out of
order — which is the direction every post-CM paper went — **you need an explicit rule that says the
output stops at the first thing you have not decided.** Note this well for us: our `tauStep` folds
over `findAllFinalLeaders` and emits every final leader it finds, with **no undecided state and no
truncation point**. A wave whose leader is not (yet) super-ratified is simply skipped and later
waves are emitted past it — and if that leader *becomes* super-ratified when a late block arrives, it
is inserted behind material already emitted. §3.3 puts this in the lineage's own terms.

---

## 3. The ordering rule, confirmed

### 3.1 The rule, four independent statements of it

**DR Alg. 3 line 54** — the per-anchor contribution:

```
verticesToDeliver ← {v′ ∈ ∪_{r>0} DAG_i[r] | path(v, v′) ∧ v′ ∉ deliveredVertices}
```

and DR §5 states the hypothesis it rests on:

> since we never add a vertex `v` to the DAG before we add all the vertices `v` points to with strong
> or weak edges, **two correct processes always have the same causal history for any vertex they both
> have in their DAGs.** Therefore, once we agree on a sequence of leaders, all that is left to do is
> to order the causal histories of the leaders in some deterministic order.

**BS §5.2**, with the three-leader complication:

> `p_i` **traverses back the rounds of its DAG until the last round in which it committed a leader**
> and check whether it is possible that other honest parties committed leaders in these rounds… all
> honest parties order the same leaders and in the same order. All that is left is to apply some
> deterministic rule to order their causal histories one by one.

**MY Thm. 1 (Total Order)**:

> Correct validators deliver blocks by using an identical deterministic algorithm to order the
> **causal history of committed proposer blocks**. Since a correct validator has all the causal
> histories of a block when the block is added to its DAG, and the sequence of committed proposer
> blocks of one validator is a prefix of another's (Lem. 7), all correct validators deliver a
> consistent sequence of blocks.

**CM Def. 6 / Alg. 2:37** — `output xsort(b1, [b1] \ [b2])`, every quantifier over the anchor's own
closure.

**Verdict: confirmed, unanimously, across certified and uncertified DAGs, coin-elected and
round-robin anchors, single-anchor and n-anchors-per-round.** The per-anchor input is *the anchor's
own causal past*, an object fixed by that anchor's signed hash pointers. Nothing in the lineage
reads the live DAG for the *contents* of an anchor's segment.

### 3.2 The append-only floor is a named variable in every implementation

The property is not incidental; each protocol carries a **floor variable** that the recursion may
never descend below.

| Protocol | The floor | Where |
|---|---|---|
| DR | `decidedWave` — the backward loop runs `for w′ from w−1 down to **decidedWave + 1**` | DR Alg. 3:39 |
| BS | `committedRound` — *"traverses back… **until the last round in which it committed a leader**"* | BS Alg. 4, §5.2 |
| MY | the commit sequence truncates at **the first undecided slot**; earlier slots are latched by Lems. 2/3/6 | MY §III-B step 3 |
| CM | `last_final_leader()`, and the recursion walks only **ratified leaders inside `[b̂]`**; finality appears in τ exactly once, at the head | CM Alg. 2:32, 41–46 |

Ours has none. `find_all_final_leaders` (`blocklace/src/ordering.rs:483`) starts at `wave = 0` and
loops to `max_round` on **every** call, re-deciding every wave against the current lace. That is the
same defect as the τ-domain deviation, seen from the control-flow side rather than the data side,
and it is why `FinalizedRegionStable.leaders_extend` has to be *assumed*: nothing in the code makes
the leader list a suffix-extension of the previous one.

### 3.3 Does any variant legitimately read live state? Yes — two, and here is the discipline

This is the part of the question worth the most, because the answer is not "never read live state."

**Variant A — Mysticeti's decision rule.** MY's direct rule *does* read the local live DAG: a slot is
`to-commit` when the validator observes 2f+1 certificate patterns for it **in its own DAG**, and two
validators reach that point at different times with different DAGs. What makes it safe is a
three-part discipline, all of it proved:

1. **Every decision is a one-way latch, proved irrevocable.** Lem. 2: a directly-skipped slot cannot
   have been committed by anyone. Lem. 3: a directly-committed slot cannot be skipped by anyone.
   Lem. 5: at most one block per slot is ever certified. Lem. 6: two validators that both decide a
   slot decide it identically. **A live read may only ever produce a verdict that no subsequent
   arrival can reverse.**
2. **The indirect rule reads a *fixed* object, not the live view.** When the direct rule fails, the
   verdict is a function of the causal history of a single anchor block — MY Lem. 6's induction ends
   *"Since the indirect decision of X and Y for slot k depends entirely on the causal history of the
   same block b, both validators decide the slot k identically."*
3. **The output truncates at the first undecided slot** (§2.5). Undecidedness is *backpressure*, not
   permission to skip ahead.

**Variant B — Shoal / HammerHead leader reputation.** These derive the *anchor schedule itself* from
DAG contents, which is as live-state-dependent as it gets. SH §3.2 is explicit that in a DAG this is
a **safety** problem, not a liveness one:

> One important property [of] Jolteon is that Safety is preserved even if validators disagree on the
> identity of the leader… Unfortunately, this is not the case for Narwhal-based BFT. **If validators
> disagree on the anchor vertices, they will order the DAG differently and thus violate safety.**
> This makes the leader reputation problem strictly harder in Narwhal-based BFT.

The discipline that makes it safe is the same one, in a different dress: SH computes the new mapping
*"based on the causal history of ordered anchor A in round r (which they are guaranteed to agree on
by Property 1)"*, and HH §3 goes one step further —

> when we commit a sub-dag in Bullshark this happens **through a subjective view of the DAG**. This
> means that two validators might see a different subset of votes… In order to resolve the first
> challenge **we introduce a delay at the calculation of the reputation score** … we calculate the
> reputation score **up to but EXCLUDING the committed leader.**

**So the rule the lineage actually follows is not "never read live state." It is:**

> A live read may determine **whether** you are ready to emit. It may never determine **what** you
> emit. Anything that feeds the emitted order — the anchor's segment contents, the anchor list, the
> anchor schedule — must be a function of a committed object's fixed causal past.

Our `leaderCoverage` (`metatheory/Dregg2/Distributed/BlocklaceFinality.lean:409`) violates the second
sentence, and `finalLeaderAt` (`:384`) violates the first (its singleton rule can *retract* a
verdict, which no latch in this lineage can do). Both are already on the fix list in
`CONSENSUS-FROM-SOURCE` §0; this section adds that **the retraction is the more fundamental of the
two.** Every protocol here has monotone per-anchor decisions; not one of them can un-decide.

---

## 4. Reconfiguration in this cluster — the negative was too broad

### 4.1 The correction

`DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md` §3 states, and defends by naming its search:

> **Nothing in this corpus treats reconfiguration of a DAG/blocklace consensus protocol.** … Full-text
> grep … over the extracted text of: `dag-rider`, `bullshark`, `shoal`, `shoal-plus-plus`, `banyan`,
> `cordial-miners`.

For those six, the finding stands and I re-confirmed it (DR: fixed `Π`; BS: two hits, one a *dynamic
adversary*, one Mir-BFT's numbers in related work; SH/SH++: "dynamic" always means *dynamic anchor
re-interpretation*; BY: "epoch synchronization" once, about Jolteon/Ditto; CM §2 fixes `Π`, App. D
treats only shrinking).

**Sui Lutris and Mysticeti were not in that list, and both treat it.** This is the same class of
error the companion doc itself names — *a negative claim inherits the shape of the shelf it was
drawn from* — recurring one document later, on a shelf assembled by paper *title*. SL's title says
"Broadcast and Consensus"; its §4.2 is a reconfiguration protocol.

### 4.2 Sui Lutris §4.2 — a reconfiguration protocol for a system running Bullshark

SL runs **Bullshark as its consensus engine** (SL §5, assumptions: *"Sui Lutris operates in the
partial synchrony model only due to our use of Bullshark as consensus protocol"*). Its four steps:

1. **Register.** Candidates for epoch `e+1` call `Register`; *"This function establishes the static
   stake distribution for the next epoch. The smart contract accepts registrations until the **S**th
   checkpoint of the epoch is created."* — the freeze point is **a position in the committed
   checkpoint sequence**, not a wall clock.
2. **Ready.** *"Before taking over committee operations, future validators run a full node to
   download the required state… Once a validator for the new epoch is ready to start validating, they
   call the `Ready` function to signal they have successfully synchronized the required state… The
   cutoff period for the epoch is when a **quorum of new validators** is ready. At this point, the old
   committee stops signing new transactions or locking objects."* — state transfer **before**
   participation, gated on a quorum of the *incoming* set.
3. **End-of-Epoch.** The old committee *"stop accepting certificates from clients and instead make
   sure that all the certificates they have processed are sequenced by the consensus engine"*, then
   call `End-of-Epoch`. The takeover happens only *"after **2f+1** such End-of-Epoch messages are
   **ordered**"* — i.e. the drain evidence is itself on the committed prefix.
4. **Handover.** After 2f+1 End-of-Epoch calls plus an extra checkpoint, `Handover` terminates the
   epoch. A validator continuing into the new epoch must *"(i) drop the temporary lock stores, and
   (ii) **roll back the execution of any transaction that did not appear in any checkpoint so far.**
   As discussed earlier, this is safe as these transactions were not final."*

SL Thm. 1 (Safety) is the statement that makes this a protocol rather than an operations runbook:
*"At the start of every epoch, all correct validators [have executed the same set of transactions in
the same order]."* And SL §7 measures it: 10 validators, 3 epoch changes at 10-minute epochs, *"the
performance of Sui Lutris (and Bullshark) are largely unaffected by epoch changes."* Production: 383
epoch changes, 107 validators, 24h epochs (SL §1).

Two assumptions to carry forward, both stated by SL and neither free:
- **BFT assumption, second clause:** *"Correct validators of previous epochs **never leak their
  signing keys**."* This is the same obligation Pastro discharges with forward-secure signatures
  keyed by configuration height (see `DYNAMIC-COMMITTEE-LITERATURE` §4.2c). SL assumes it; we
  currently do neither.
- **The epoch boundary is also the *recovery* mechanism.** SL uses reconfiguration to *"unlock
  equivocated objects"* — a client that deadlocks its own account is stuck *"for a single epoch"*
  and no longer. Reconfiguration is not only a governance event; it is where you release
  safety-motivated locks that nothing else can release.

### 4.3 Mysticeti §IV-D — the rule for a pure-consensus DAG, in one sentence

MY §IV-D, on why Mysticeti-**C** (the pure consensus protocol, no fast path — our shape) has *no*
epoch-change protocol:

> The safety of reconfiguration is ensured by including all finalized transactions from the current
> epoch into the causal history of the epoch's final commit, which also acts as the initial state for
> the succeeding epoch. **Guaranteeing reconfiguration safety is straightforward in systems mandating
> consensus for all transactions, such as Mysticeti-C, owing to the total ordering property inherent
> in consensus. A deterministic consensus commit C sets the boundary between epochs e and e+1.** This
> makes sure that all transactions completed in epoch `e` are included in and come before commit `C`.
> … This holds trivially for consensus protocols which is why we **omit the epoch change for
> Mysticeti-C**.

For Mysticeti-FPC (which has a consensusless fast path, as SL does) it needs the **epoch-change
bit**: an honest validator that detects epoch change stops voting for fast-path transactions, sets
the bit in all its blocks, and *"Upon committing blocks from 2f+1 validators with the epoch-change
bit set via the consensus path, the epoch is considered closed."* Same 2f+1-drain shape as SL step 3.

**The bearing on us is direct and simplifying.** We have no consensusless fast path — every turn
goes through τ. So MY §IV-D says our reconfiguration boundary should be *a committed anchor*, and the
epoch's content is *that anchor's causal history*. That is the same answer as
`DYNAMIC-COMMITTEE-LITERATURE` §3.1 arrived at from the PBFT side ("install at a wave boundary,
keyed to the anchor that ordered the Join"), now with a DAG-native paper saying it.

**⚠ One thing MY's "trivially" hides, and we must not inherit the word.** MY-C is trivial here
because in Mysticeti the roster is *not an input to the ordering function's verdicts* in a way that
can change retroactively — the validator set enters block validity and the 2f+1 counts, and MY simply
does not consider a run where those change mid-DAG. Our τ reads `participants` at every level
(`roundOf`, `blocksAtRound`, `ratifiesEnrolled`, `wave_leader`, `supermajority_threshold`), so
re-running τ after a roster change can reorder blocks that already exist. That hazard —
`DYNAMIC-COMMITTEE-LITERATURE` §3 item 2 — is real, is ours, and **no paper in this cluster faces
it**, because none of them changes the roster while a DAG is live. That negative I will defend for
this cluster: SL changes the committee *between* epochs with a drained, quiesced boundary
(step 3 stops new work; step 4 rolls back anything not checkpointed), which is precisely the
arrangement that means the ordering function never has to run over a mixed-roster DAG.

---

## 5. Leader/anchor schedule: hazards of static round-robin

### 5.1 What a static schedule costs, measured

HH §1 opens with the production incident, which is the most concrete statement of the cost anywhere
in the cluster: on a deployed DAG-BFT chain, when *"validators started being less responsive… the p95
latency going up from 3 seconds to 4.6 seconds and even the p50 latency increasing."*

SH §3.2 gives the mechanism: *"In Narwhal-based BFT, if the leader of round r crashes, no validator
will have the anchor of round r in its local view of the DAG. Thus, the anchor will be skipped and no
vertices in the previous round can be ordered until some later point due to an anchor in a future
round."*

SH++ §8.3, crashing 33 of 100 replicas: *"Bullshark and Mysticeti, in contrast, suffer drastically
increased latency since **they do not employ a leader reputation mechanism** to elect suitable anchor
candidates, and thus must 'wait' to commit until a non-faulty replica is elected as anchor."*

The formal property is **Leader-Utilization** (HH Def. 3, from Spiegelman et al.): *"in crash-only
executions, after GST, the number of rounds r for which no honest party commits a vertex formed in r
is bounded."* A static round-robin schedule over `n` participants with `k` persistently slow members
deterministically loses `k/n` of all waves — not probabilistically, not under attack, just as a
standing tax.

MY Lem. 11 states the flip side, which is why round-robin is *sufficient*: *"The round-robin schedule
of proposers in Mysticeti ensures that in any window of 3f+3 rounds, there are three consecutive
rounds with honest primary proposers."* Round-robin buys liveness with a bounded but linear-in-`f`
worst-case wait. Reputation buys back the constant.

### 5.2 The three answers the field gives, and they are not the same answer

| Answer | Paper | Mechanism | What it costs |
|---|---|---|---|
| **Skip and wait** | DR, BS, CM | an unratified anchor is skipped; a later anchor orders its round | one wave (or more) of latency per bad leader; needs a timeout to be *safe against a slow-but-honest* leader (§5.3) |
| **Re-derive the schedule** | SH, HH | recompute the leader mapping from the causal history of a committed anchor, excluding the anchor itself | a **safety** obligation: schedule agreement by strong induction *without skips* (HH Prop. 1); a laggard applies retroactively |
| **Multiple slots / priority order** | MY, BY | MY: up to `n` proposer slots per round in a predefined total order, with instant `to-skip`. BY/ICC: every replica may propose, delay ∝ rank; the rank-0 replica is the leader but no view change is needed if it is absent | MY: more `undecided` slots under asynchrony (MY §III-C). BY: not a DAG; and each rank costs a delay unit |

Mysticeti runs **two** of these at once: `n` slots per round *and* HammerHead reputation to pick the
2f+1 best as candidates (MY §III-C, §VIII). Its related-work section names the constraint that
combining them imposes: *"for liveness, it would need to adopt a proposer slot rotation schedule
where **slots remain static for 3 rounds**"* — a reputation update may not move a slot inside its own
decision window.

**BY is the one genuinely different idea here and it is worth naming even though BY is not a DAG
protocol.** In ICC/Banyan the schedule is a *priority order over proposals*, not an *exclusive
assignment of a slot*: every replica may propose in every round, replica of rank `r` waits a delay
proportional to `r` first, and a replica stops voting for higher-rank proposals once a lower-rank one
notarizes. The consequence (BY §1, §4) is *"rotating leaders **without the necessity for a
view-change protocol**"* — an absent rank-0 leader costs exactly one delay unit and the round still
produces a block. For us that is a design to know about, not to adopt: it presumes a chained
block-tree, not a DAG.

### 5.3 ⚑ Our round-advance rule is the asynchronous one, under a prospective leader

**CM Alg. 4, verbatim** — the two instances differ in *both* leader election and round advance, and
CM §6.2 explains that this pairing is deliberate:

```
    ▷ ASYNCHRONY (w = 5, retrospective coin leader)
59:  procedure advance_round():
        return max r : cordial_round(r)                                  ▷ advance as soon as cordial

    ▷ EVENTUAL SYNCHRONY (w = 3, prospective round-robin leader)
66:  w ← 3
67:  procedure es_advance_round():
68:    return max r : cordial_round(r) ∧
69:      ((r mod w = 0 ⟹ ∃b : leader(r) = b.creator) ∧                    ▷ wave's 1st round: leader block present
71:       (r mod w = 1 ⟹ ∃b : leader(r−1) = b.creator ∧ ratifies(…)) ∧    ▷ 2nd round: leader ratified
73:       (r mod w = 2 ⟹ ∃b : leader(r−2) = b.creator ∧ super-ratifies(…)))
75:      ∨ timeout)                    ▷ timeout measured from when round r is cordial; p's estimate of ∆
```

CM §6.2, on why:

> The reason a wave in asynchrony is longer is to counter the adversary: **If the adversary knows in
> advance the leader block in the first round of the wave, it can manipulate block arrival times s.t.
> a wave with a final leader block will never happen.**
> … In ES, a miner advances to the next round after a round either if timeout passes, or conditions
> for leader block finality occur (Line 67). … **These conditions are to prevent the adversary from
> ordering the messages after GST, in particular, the leader block and the blocks that super-ratify
> it, as the leader is known in advance.**

CM Prop. 38 (ES leader-liveness with probability 1) is stated **only** *"if `timeout > ∆`"*.

**What we implement.** `plan_round_block` (`node/src/blocklace_sync.rs:6054`), the whole rule:

> * No own block yet ⇒ `Genesis`.
> * Otherwise let `r = my_max_round`. If a supermajority of DISTINCT creators have a block at round
>   `r`, return `Advance` linking every round-`r` block; else `Wait`.

That is `cordial_round(r)` and nothing else. There is no leader clause and no timer. The cadence that
calls it (`round_cadence_decision:6200` → `cadence_tick_round_driven:6450`) gates on
*work* — `DrainTurns` / `ReactiveAck` / `AdvanceWave` / `IdleHeartbeat` — never on the leader.
And `blocklace_wave_timeout_ms`, the only thing in the tree named like a wave timer, is **not** a
consensus timeout: it is threaded to `derive_from_lace` as `timeout_waves` and thence to
`ConstitutionManager::from_participants` (`node/src/committee_replay.rs:225–230`), i.e. **governance
proposal expiry**. Repo-wide, `rg 'wave_timeout'` returns seven hits, all in `node/src/lib.rs`
plumbing.

Meanwhile `wave_leader` (`blocklace/src/ordering.rs:288`) is `participants[wave % participants.len()]`
— maximally predictable, published in the genesis roster, and stable forever.

**So: prospective, publicly-known leader (the ES half) + advance-on-cordiality-alone (the async
half).** Two consequences, and only the second needs an adversary:

- **Honest and slow is enough.** We advance the moment 2f+1 distinct creators are at our round. If
  the wave-leader is not among the fastest 2f+1, our block does not link it — and because a
  wave-end block's causal past is fixed at signing, it never will. The wave is skipped. With
  round-robin, participant `i` leads waves `i, i+n, i+2n, …`, so a persistently slow member costs
  `1/n` of all waves, deterministically. This is exactly what SH §5.2 says the even-round timeout is
  for: *"without timeouts in the even rounds, an honest leader that is even slightly slower than the
  fastest 2f+1 validators will struggle to get its anchor linked by other vertices. As a result, the
  anchor is unlikely to be ordered."*
- **An adversary controlling delivery order gets the whole thing for free.** It knows the leader `n`
  waves ahead. It needs only to keep the leader's block out of the fastest 2f+1 arrivals at each
  wave-start round. CM §6.2's sentence is precisely this attack, and CM's answer is the line-67 gate.

**This is a liveness finding, not a safety one, and it should be said that way.** But it is the
cheapest gap on this list to close, it closes an item another lane left explicitly open, and CM hands
us the predicate.

---

## 6. Ranked post-CM lessons: corrections vs optimisations

Ranked by what they change about what we should do. **Corrections** are places the field found CM
wrong, incomplete, or silent on something we are exposed to. **Optimisations** are latency and
throughput we can decline.

### Corrections — act on these

**C1. Emit-order monotonicity is enforced by a floor variable and a truncation point, not by hope.**
*(DR Alg. 3:39 `decidedWave`; BS Alg. 4 `committedRound`; MY §III-B step 3 "until the first undecided
slot".)* — This is the lineage-side confirmation of the τ verdict already reached in
`CONSENSUS-FROM-SOURCE` §0, and it adds two implementation requirements that doc does not state:
`find_all_final_leaders` must carry a **floor** and must not re-decide below it, and the emitted
order must **truncate** at the first wave it has not decided rather than emitting past it. **Act:
yes, as part of the τ re-anchor. Do not land the re-anchor without the floor** — an anchor-past τ
that still re-decides every wave from zero on every call is only half the fix.

**C2. A verdict a validator will be held to must be forced monotone by the block format.**
*(MY §II-C block validity + Lem. 4; CM Alg. 1:15–16 `correct_block` + Alg. 3:49 "incorrect blocks are
ignored".)* — Two admission predicates are missing from `insert_checked`
(`blocklace/src/finality.rs:1527`), which today checks only closure: **cordiality** (pointers cover a
supermajority of the previous round) and the **self-link** (the author's own previous block among the
predecessors). We enforce both when *authoring* (`plan_round_block`) and neither when *receiving*,
which is the wrong way round — the author we do not need to constrain is ourselves. Cordiality is
the hypothesis under CM Prop. 3 → Prop. 9; `CONSENSUS-FROM-SOURCE` §5.1 already ranks it as the cheap
fix. **Act: yes.** This is a per-block predicate over that block's own pointers, evaluated once at
receipt.

**C3. Any DAG-derived quantity that feeds the emitted order must come from a committed anchor's
fixed causal past — and this is a *safety* rule in a DAG, unlike in leader-based BFT.**
*(SH §3.2: "If validators disagree on the anchor vertices, they will order the DAG differently and
thus violate safety. This makes the leader reputation problem strictly harder in Narwhal-based BFT."
HH §3: score "up to but EXCLUDING the committed leader.")* — We have no reputation today, so nothing
is broken *by this*. Its value is as a **standing rule** and it has two immediate applications: (a)
the roster is such a quantity, so an epoch-boundary roster must be `c(committed prefix)` and never
`c(now)` — the hazard `DYNAMIC-COMMITTEE-LITERATURE` §3 names; (b) if reputation is ever proposed,
the safety obligation (HH Prop. 1, strong induction over schedules **without skips**) comes with it
and is not optional. **Act: adopt as a rule now; it costs nothing and it is the general form of the
bug we already have.**

**C4. The uncertified DAG puts data fetching on the critical path, and it is worth 10× under a 1%
drop rate on 5% of nodes.** *(SH++ §3.3, §8.3; MY §VIII production account; MY Lem. 8's explicit
"2·∆ to request any missing parent block".)* — Unpriced in CM. We inherit it fully because
`insert_checked` hard-rejects on a missing predecessor and we have no certificate telling us a
referenced block is retrievable at all. **Act: yes, as engineering, not protocol.** An
off-critical-path synchronizer with fetch-ahead, and a producer-side policy for how long to treat a
peer's tips as usable while its parents are missing. **Do not "fix" it by relaxing the closure
check** — closure is the hypothesis under DR §5's same-causal-history property and CM Prop. 9's
closed-blocklace premise. This is the one place in this document where the cheap-looking move is the
unsound one.

**C5. The ES round-advance gate.** *(CM Alg. 4:67 + §6.2 + Prop. 38; SH §5.2 on the even-round
timeout.)* — §5.3. We run the async advance rule with an ES leader. **Act: yes.** The predicate is
three clauses and a timer, and CM writes it out. Note the ordering with C1/C2: the gate reads
`ratifies`/`super-ratifies`, so it should land after the τ re-anchor, not before.

**C6. Finality must never retract — the equivocating leader is resolved by counting, not by
forfeiting the wave.** *(CM §4.2, Lem. 31; and every protocol in §3.2's table, none of which can
un-decide.)* — `finalLeaderAt`'s `≥2 candidates ⇒ none` rule is already on
`CONSENSUS-FROM-SOURCE`'s list; the lineage evidence adds that **no protocol in the family has a
retractable decision at all**, so this is not a stylistic difference from CM but a departure from the
whole family. Mysticeti's Lems. 2/3/5/6 exist precisely to prove irrevocability for *each* decision.
**Act: yes**, and treat "can a late arrival flip this verdict from true to false?" as a checklist
question on every consensus predicate we write.

**C7. Reconfiguration is a solved, deployed problem in this lineage, and the boundary is a commit.**
*(SL §4.2, Thm. 1, §7; MY §IV-D.)* — §4. Supersedes the "no paper here specifies it" line for the
DAG lineage. The parts list to copy is SL's four steps, of which the two that are load-bearing for
safety are **state transfer before participation** (step 2, gated on a quorum of the *incoming* set)
and **a 2f+1 drain that is itself ordered** (step 3). **Act: as design input for the federation
work** — this is not a defect report, it is the missing reference the join-path design was written
without.

### Optimisations — decline, or defer, with a reason

**O1. Pipelining (an anchor every round rather than every `w`).** *(SH §3.1, SH++ §4.)* Pure latency.
Buying it means taking on Shoal's "re-interpret the DAG from the first ordered anchor" machinery, and
that machinery is what C3 warns about. **Decline until τ is re-anchored.**

**O2. Multiple proposer slots per round.** *(MY §III-A/§III-C.)* Latency. MY itself flags the cost —
more `undecided` slots under asynchrony or attack, delaying the commit sequence — and mitigates with
reputation. At our committee size this buys little. **Decline.**

**O3. Leader reputation.** *(SH §3.2, HH.)* This is the highest-value optimisation on the list
because our static round-robin loses `1/n` of waves to any persistently slow member (§5.1), and
because both SH++ §8.3 and HH §1 measure the effect on real deployments. But it carries C3's safety
obligation in full, and C5 (the timeout gate) recovers most of the same ground for far less. **Defer,
explicitly: fix C5 first, then reconsider.** Do not implement reputation before the τ re-anchor —
a reputation function reading the live lace would be the same bug on a third axis.

**O4. Banyan's fast path / ICC rank-ordered proposal.** *(BY §1, §4.)* A different protocol family
(chained block-tree, not a DAG); BY §2 itself only *"hypothesize[s] that it applies to DAG protocols
too."* **Decline**, but keep the *idea* — leader schedule as priority order rather than exclusive
assignment — in the pocket for whenever the round-robin tax becomes the top complaint.

**O5. Narwhal worker/primary scale-out.** *(NT §1, §4.)* Throughput architecture, orthogonal to
everything here. **Decline.**

**O6. Garbage collection.** *(BS §7; NT §3.3; CM App. D.)* Memory, not correctness — and the lineage
is clear that in asynchrony you must choose between fairness and GC, while under eventual synchrony
(our instance) you can have both after GST. `CONSENSUS-FROM-SOURCE` §5.6 covers this. **Defer**, with
the note that NT §3.3's footnote is a genuine operational warning: *"A bug in our garbage collection
led to exhausting 120GB of RAM in minutes compared to 700MB memory footprint of Narwhal."*

---

## 7. What I did not verify, and what would falsify this

- **I did not construct the slow-leader liveness witness.** §5.3's claim that a persistently slow
  member costs `1/n` of waves follows from `plan_round_block` + `wave_leader` + the fixed causal past
  of a wave-end block. It is a derivation from code I read, not a run I performed. A test that pins
  it — hold one member's blocks back past the supermajority point for `n` consecutive waves and
  assert `find_all_final_leaders` skips exactly that member's waves — is cheap and would settle it.
- **I did not audit the block synchronizer** (`node/src/blocklace_sync.rs` frontier/chunked sync) for
  whether the missing-predecessor fetch is on or off the critical path. C4's severity for *us*
  specifically depends on that, and I am asserting only the paper-side cost plus the fact that
  `insert_checked` hard-rejects.
- **The `is_super_ratified` check is against the published CM's super-ratification, matched by
  shape.** I compared predicates, not proofs; I did not verify that our two-level pattern is
  literally MY's "2f+1 certificate blocks each containing a 2f+1 support pattern" rather than a
  one-level 2f+1 vote count with a second level supplied elsewhere. Reading `ratifies_enrolled` end
  to end would settle it, and is worth doing before anyone cites §0 item 1 as a clean bill.
- **§4.3's negative** — that no paper in *this* cluster treats a roster change while a DAG is live —
  is a claim about ten papers I read, one of which (SL) changes the committee at a drained boundary
  specifically so the question does not arise. If someone finds a DAG paper that re-runs its ordering
  function across a roster change, that negative falls and §4.3's warning gets a reference.

---

## Summary

| # | Question | The lineage says | We do | Verdict |
|---|---|---|---|---|
| 1 | Where does CM sit? | Origin of the uncertified-DAG branch; MY §IX and SH++ §9 both name Mysticeti as its implementation | we are CM ES `w=3` | — |
| 1 | Same move as Mysticeti? | Yes — both drop RB and read certificates out of DAG structure. They differ on equivocation: CM **abstains**, MY **supports first-in-DFS and commits the certified one** | CM's abstain | ✅ ours is the conservative side |
| 2 | Hazards MY found that CM did not | ① single-certificate commit is **unsafe** (MY fn. 10) ② support stability needs a **self-link** (Lem. 4) ③ **data fetch on the critical path**, 10× measured (SH++ §8.3) ④ multi-anchor emission needs an **undecided/truncate** rule | ① fixed rule ✅ ② self-link authored, not validated ❌ ③ fully exposed, no mitigation ❌ ④ no undecided state, no truncation ❌ | C2, C4, C1 |
| 3 | Ordering rule | Anchor's own causal past; **unanimous** across DR:54, BS §5.2, MY Thm. 1, CM Def. 6. Every implementation carries an append-only **floor** | union over live-lace ratifiers; `find_all_final_leaders` re-decides from wave 0 every call | ❌ known deviation + missing floor |
| 3 | Legitimate live reads? | **Yes, two** — MY's decision rule and SH/HH reputation. Safe because every verdict is a proved **one-way latch**, the fallback reads a **fixed** anchor history, and the output **truncates at the first undecided** | `finalLeaderAt` can **retract** — no protocol in the family can | ❌ retraction is the deeper defect |
| 4 | Reconfiguration in this cluster | **Specified.** SL §4.2 four steps, Thm. 1, 383 production epoch changes, on a Bullshark engine. MY §IV-D: *"a deterministic consensus commit C sets the boundary"* | out-of-band join, no epoch boundary, no drain, no state-transfer gate | ⚑ corrects the prior negative |
| 4 | Roster change *while a DAG is live* | **Not treated by anything here** — SL drains and quiesces so the question never arises | our τ reads the live roster at every level | ❌ ours alone; defend the boundary |
| 5 | Static round-robin | Loses `1/n` of waves to any slow member; MY Lem. 11 bounds the honest window at `3f+3` rounds; three field answers: skip+timeout, reputation, multi-slot/priority | round-robin `wave % n`, publicly known | ⚠ tax is real, tolerable |
| 5 | Slow or absent leader | CM Alg. 4:67 — advance only on leader-present / ratified / super-ratified **or timeout**, `timeout > ∆` (Prop. 38), *"as the leader is known in advance"* (§6.2). SH §5.2 says the same about the even-round timeout | **`cordial_round(r)` alone** — the *asynchronous* rule (Alg. 4:59), no leader clause, no timer; `blocklace_wave_timeout_ms` is governance expiry | ⚑ **NEW** — closes the item `CONSENSUS-FROM-SOURCE` §5.3 left open |

### The order to do them in

1. **C1 + C6 together** — re-anchor τ on the committed block's causal past, *with* a floor variable
   and a truncation point, and make every finality verdict a one-way latch. These are one change;
   splitting them ships half a fix.
2. **C2** — cordiality and self-link at admission. Cheap, independent, and it is what turns
   `FinalizedRegionStable` from an assumption into a theorem.
3. **C5** — the ES round-advance gate. Reads `ratifies`/`super-ratifies`, so it lands after 1.
4. **C4** — the synchronizer. Independent of all of the above and the only one that is pure
   engineering.
5. **C7** — feeds the federation/reconfiguration design; not a defect queue item.
6. **C3** — adopt as a standing rule today; it costs nothing and it is the general form of 1.
