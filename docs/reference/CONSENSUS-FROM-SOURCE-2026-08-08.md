# Consensus from source: what the papers actually specify

**Date:** 2026-08-08
**Method:** 11 papers read from `pdfs/`. Every claim about a protocol carries paper + section/algorithm/line.
Every claim about our code carries `file:line`, verified at source.
**Scope:** read-and-think. No protocol code changed by this pass.

**Layout:** §0 leads with the τ verdict, because a decision was waiting on it. §§1–4 answer the
questions in order from the papers; §3b and §4b hold the implementation comparison for §§3–4 (§§1–2
compare inline, since the τ question is the crux). §5 is what the papers settle that we had not
asked about. The summary table at the end is the whole thing on one page.

Citation shorthand: **CM** = Keidar, Naor, Poupko, Shapiro, *Cordial Miners* (arXiv:2205.09174v6).
**GS** = Shapiro, *Grassroots Systems* (2301.04391). **GSN** = *Grassroots Social Networking* (2306.13941).
**GF** = Lewis-Pye, Naor, Shapiro, *Grassroots Flash* (2309.13191). **DR** = *DAG-Rider* (2102.08325).
**BS** = *Bullshark* (2201.05677). **SH** = *Shoal* (2306.03058).

---

## 0. THE τ VERDICT — DEVIATION, and the paper's shape is the correct one

**Our τ is not Cordial Miners' τ.** The difference is not a detail of the same design; it is a
different function with a different domain, and the property we are missing is one CM *proves as a
theorem* from a hypothesis CM *establishes by construction*.

The one-sentence statement:

> CM's τ orders **the anchor's own causal past** — a set fixed forever by the anchor block's own
> hash pointers. Our τ orders **the union of the causal pasts of whichever ratifiers this node
> currently happens to hold** — a set that grows every time a late block arrives.

CM, Alg. 2 line 37 — the entire per-anchor contribution:

```
37:    output xsort(b1, [b1] \ [b2])          ▷ Output a new equivocation-free suffix
```

`[b1]` is the *closure* of the anchor: `[b] := {b′ ∈ B : b ⪰ b′}` (CM Def. 19), i.e. everything
reachable from `b1` along `b1`'s own pointers. It cannot change when new blocks arrive, because
`b1`'s pointer set is signed and immutable. `[b2]` is the closure of the previous ratified leader.

Ours, `metatheory/Dregg2/Distributed/BlocklaceFinality.lean:409`:

```lean
def leaderCoverage (B : Lace) (participants : List AuthorId) (l : Block) (wavelength : Nat) : List BlockId :=
  let lr := roundOf B participants l.id
  let lwave := roundToWave lr wavelength
  let waveEnd := waveLastRound lwave wavelength
  let endBlocks := blocksAtRound B participants waveEnd
  (endBlocks.flatMap (fun bid => match B.lookup bid with
     | some b => if ratifiesEnrolled B participants b l then causalPastIncl B bid else []
     | none   => [])).dedup
```

`endBlocks` comes from `blocksAtRound B participants waveEnd` (`:291`) — a filter over the **whole
live lace `B`**. The anchor `l` appears only to *test* the ratifiers. What gets ordered is
`causalPastIncl B bid` of **the ratifiers**, not of the anchor.

The anchor's own past survives in exactly one place — as an equivocation filter, `:431`:

```lean
      | some b => ¬ hasEquivInPast B participants l.id b.creator
```

So we kept CM's equivocation-exclusion role for the anchor and dropped its **ordering** role. That is
the deviation.

### Why this is the fork, mechanically

The anchor `l` sits at the wave's *first* round; the ratifiers sit at the wave's *last* round. A
ratifier's causal past is therefore a strict superset of `[l]` — it includes everything from rounds
`lr+1 .. waveEnd` that the ratifier saw. So `leaderCoverage ⊋ [l]`, and it **grows monotonically
with arrivals** at the wave-end round.

Under CM, a block in rounds `r..r+w-1` that the round-`r` anchor does not observe is simply ordered
by a *later* anchor — it lands **after** everything already emitted. Under ours, that same block is
pulled into **this** anchor's segment the moment a wave-end ratifier observing it arrives. Because
`tauStep` (`:444`) appends segments in wave order and replaces `prevCovered` each step, a late
ratifier for wave *k* splices blocks into wave *k*'s segment — i.e. **mid-prefix**, ahead of
everything waves *k+1…* already contributed. That is the unbounded-depth reordering, and it needs no
Byzantine node: it needs only a late-arriving honest block.

### Is it a bug fix or a taste call? A bug fix.

This is the decision that was waiting, so state it plainly: **redesigning τ to anchor on the
committed block's causal past is a return to the specification, not a departure from it.** It is
ours to just do. It requires no judgement call about deviating from the literature, because the
deviation is what we have now.

Two further deviations found in the same region, both in the same direction (see §2):

1. **Our finality is non-monotone; CM's cannot be.** `finalLeaderAt` (`:384`) returns `none` unless
   `leaderCandidates` is a *singleton*: `| _ => none  -- zero candidates (leader silent) OR ≥2
   (leader equivocated at the slot)`. A late second leader-slot block by the same creator therefore
   **forfeits an already-anchored wave**, flipping a wave from final back to non-final. CM
   explicitly permits an equivocating leader to have several leader blocks (§4.2: *"Note that an
   equivocating leader can have several leader blocks in the same round"*) and resolves it by
   approval (Lem. 31: at most one of an equivocating pair can hold supermajority approval). CM's
   finality only ever turns **on**.
2. **Our anchor chain is recomputed; CM's is pinned.** CM's `previous_ratified_leader(b1)` (Alg. 2
   lines 41–43) selects from `R = {b ∈ [b1] \ {b1} : … ∧ ratifies([b1], b)}` — quantified over the
   **anchor's closure**, using plain `ratifies`, and consulting *finality nowhere*. Ours folds over
   `findAllFinalLeaders B P wl` (`:393`), a list recomputed from the live lace across all waves.

**Finality appears in CM's τ exactly once: choosing the head** (Alg. 2 line 32,
`τ′(last_final_leader())`). It appears nowhere in the recursion. That single structural fact is what
makes CM's history append-only, and we do not have it.

---

## 1. What Cordial Miners specifies for ordering

**Answer: the finalized order is a function of a committed anchor's causal past — the DAG-Rider /
Bullshark shape. It is arrival-independent and append-only by construction.**

CM §3, *Ordering* (p. 5):

> A final leader block *b* serves as the "anchor" of the ordering function τ, which topologically
> sorts (while excluding equivocations) **all the blocks observed by b** that have not been ordered
> yet. Thus, each time a wave ends with a final leader block, a portion of its preceding blocklace is
> ordered.

CM §5, Def. 6 — the formal object:

```
τ′(b) := xsort(b, [b])                     if [b] has no leader ratified by b, else
         τ′(b′) · xsort(b, [b] \ [b′])     if b′ is the last leader ratified by b in [b]
```

Every quantifier is over `[b]` — the anchor's closure. The only view-dependent step is *which* block
is the head, `last_final_leader()` (Alg. 2 lines 44–46), and that is monotone: `final_leader(b)` is
`super-ratifies(blocklace_prefix(depth(b)+w-1), b)` (Alg. 2 line 48), evaluated over a *depth-bounded
prefix* of the local blocklace, which only grows. Super-ratification over a growing set is preserved.

**So a late-arriving block cannot reorder CM's history.** Concretely: if the local last final leader
is `b̂` at round 30, and blocks then arrive that make an *old* leader at round 15 final for the first
time, `last_final_leader()` still returns `b̂` (deeper), τ still computes `τ′(b̂)`, and `τ′(b̂)`
depends only on `[b̂]`, which did not change. **Output identical.** This is precisely the case our
implementation gets wrong.

### Does CM deliberately differ from DAG-Rider here? No — and that matters

The ~2× latency claim (CM Tab. 1, p. 2) comes from **forgoing Reliable Broadcast in dissemination**,
not from changing the ordering rule. CM §1 (p. 2):

> The crux of the Cordial Miners protocols is that instead of using RB to eliminate equivocation
> (and absorbing its rather high latency), miners cooperatively create a data structure that
> accommodates equivocations, termed blocklace… When a miner wishes to disseminate a block, it
> simply sends it to all other miners, taking a single round of communication, instead of at least
> two when using reliable broadcast.

The cost of dropping RB is paid **inside the ordering function**, by adding equivocation exclusion
(`approves` / `xsort`) — not by loosening the anchor discipline. CM §1: *"by 'complicating' the local
ordering task to exclude equivocations, we forgo the extra communication rounds."* The anchor
discipline is *identical* to DAG-Rider's.

Compare DR Alg. 3 line 54:

```
verticesToDeliver ← {v′ ∈ ∪_{r>0} DAG_i[r] | path(v, v′) ∧ v′ ∉ deliveredVertices}
```

`path(v, v′)` — the committed anchor's causal past, minus an already-delivered **set**. Same shape as
CM's `[b1] \ [b2]` plus `outputBlocks`.

SH §2 states the invariant for the whole family, and it is the cleanest statement of it anywhere in
the corpus:

> 2. **Order the anchors.** All validators independently decide which anchors to skip and which to
>    order. … The key aspect is that each honest validator locally decides on a list of anchors, and
>    **all lists share the same prefix.**
> 3. **Order causal histories.** Validators process their list of ordered anchors one by one, and for
>    each anchor order all previously unordered vertices in **their causal history** by some
>    deterministic rule. By Completeness, all validators see the same causal history for any anchor,
>    so all validators agree on the total order.

and immediately after: *"The key correctness argument for all the above mention[ed] consensus
protocols relies on the fact that all validators agree on which anchors to order and which to skip."*

**Our τ breaks both halves.** Our anchor list is not append-only (`finalLeaderAt`'s singleton rule can
retract an anchor), and our per-anchor contribution is not the anchor's causal history.

---

## 2. Does CM guarantee prefix-monotonicity, and under what hypotheses? — THE CRUX

**Yes, CM guarantees it, as a theorem. The hypotheses are structural and established by
construction — not runtime conditions to be observed.**

CM Prop. 9 (§5, proof in App. C):

> **Proposition 9 (Monotonicity of τ).** Let *B* be a cordial blocklace with a supermajority of
> correct miners. Then τ is monotonic wrt the superset relation among closed subsets of *B*, namely
> for any two closed blocklaces *B₂ ⊆ B₁ ⊆ B*, **τ(B₂) ⪯ τ(B₁)**.

`⪯` is prefix (CM §2). This is exactly the property we want, and CM's three hypotheses are:

| CM hypothesis | Where CM establishes it | Do we? |
|---|---|---|
| **B is cordial** — every block acknowledges a supermajority of the previous round (Def. 25) | **Admission filter.** `correct_block(b)` (Alg. 1 lines 15–16) is a precondition of the receive rule (Alg. 3 line 49); *"incorrect blocks are ignored"* | **No enforcement found** — see below |
| **B₁, B₂ closed** — no dangling pointers (Def. 19) | **Buffering.** Alg. 3 line 49: *"Received 'out of order' blocks are buffered"* until `b.pointers ⊆ hash(blocklace)` | Not audited this pass |
| **supermajority of correct miners** | Model assumption, `f < n/3` (CM §2) | Model assumption, same |

The proof chain is worth stating because it shows what kind of thing the hypothesis is:

- **Prop. 3: *a cordial blocklace is leader-safe*** — where leader-safe (Def. 2) means *"every final
  leader block in B is ratified by every subsequent leader block in B."* The proof (App. C) is pure
  quorum intersection over the DAG: any later cordial leader observes a supermajority, which must
  intersect the ratifying supermajority in a correct miner, whose later block observes its earlier
  one. **It needs nothing but cordiality.**
- **Prop. 9** then shows the smaller blocklace's last final leader `b̂₂` necessarily *appears in the
  recursion chain* of `τ′(b̂₁)`, because `b̂₁` ratifies it (Prop. 3) and the recursion walks
  ratified leaders. Hence `τ(B₂) ⪯ τ(B₁)`.

### Therefore: our implementation has a bug, and our Lean assumes what CM proves

`metatheory/Dregg2/Consensus/TauPrefixMonotone.lean:204`:

```lean
theorem tau_executed_prefix_fixed {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (h : FinalizedRegionStable B B' P wl) :
    tauOrder B P wl = (tauOrder B' P wl).take (tauOrder B P wl).length :=
```

with the hypothesis at `:102` (**three** fields, not the two the file's own prose header at `:38`–`:43`
advertises):

```lean
structure FinalizedRegionStable (B B' : Lace) (P : List AuthorId) (wl : Nat) : Prop where
  leaders_extend :
    findAllFinalLeaders B P wl <+: findAllFinalLeaders B' P wl
  fold_agrees :
    (findAllFinalLeaders B P wl).foldl (tauStep B' P wl) ([], [])
      = (findAllFinalLeaders B P wl).foldl (tauStep B P wl) ([], [])
  enrollment_agrees :
    ∀ bid ∈ tauOrderUnfiltered B P wl, enrolledId B P bid = enrolledId B' P bid
```

Read against CM this is stark:

- `leaders_extend` — that the anchor list only extends — is **CM Prop. 3's conclusion**, which CM
  *derives from cordiality*. We take it as a hypothesis.
- `fold_agrees` — that re-running the fold over the *new* lace reproduces the *old* segments — is
  **exactly the property CM gets for free** by folding over `[b]` instead of over the live lace.
  There is nothing to assume when the input is immutable.

So `FinalizedRegionStable` is not an exotic side condition we forgot to check. **It is the theorem
CM proves, restated as an assumption, because our τ's domain makes it unprovable.** The file says as
much at `:99`–`:101`: *"`lagBase → lagGrown` (§4) witnesses that dropping `fold_agrees` admits an
honest, insert-valid reorder. The node currently checks NONE of the fields (the finding)."*

**Does our node establish it?** No. `FinalizedRegionStable` / `stableCheck` / `stable_check` have
**zero executable references** repo-wide; every `.rs` hit is a doc comment
(`node/src/execution_cursor.rs:22,35,198,432,435,521`; `node/src/blocklace_sync.rs:2694,2704`). The
only thing the node does is a *conclusion-level* observation: `observe_order`
(`node/src/execution_cursor.rs:203`) diffs the new order's prefix against the last and increments
`prefix_shifts`, logged and metered (`blocklace_sync.rs:2712`–`:2723`, `inc_tau_prefix_shift`) and
**gating nothing**. The code says so itself at `execution_cursor.rs:435`: *"The node checks
`stableCheck` nowhere; `observe_order` only counts the shift and logs it."*

### The execution cursor: CM authorises the caching, but only via Prop. 9

Worth stating precisely, because the cursor is *not* independently wrong. CM §5 (p. 9) explicitly
sanctions caching the prefix:

> Practically, a sequence up to a super-ratified leader is **final (Prop. 9)** and hence **can be
> cached**, allowing the next call to τ with a new super-ratified leader to be computed backward only
> till the previously-cached super-ratified leader…

That is what `ExecutionCursor` is. The paper *earns* the optimisation from Prop. 9. We take the
optimisation without Prop. 9.

One correction to the brief that prompted this pass: the claimed mechanism — *"the cursor never
re-serves, and a prefix shift causes a block to be re-served or silently skipped"* — is **refuted for
current code**. `pending` (`node/src/execution_cursor.rs:181`) is a set difference over an identity
set, not an index slice:

```rust
    pub fn pending(&self, ordered: &[BlockId]) -> Vec<BlockId> {
        ordered.iter().filter(|id| !self.executed.contains(id)).copied().collect()
    }
```

so on a prefix shift the already-executed block is dropped by the filter (not re-served) and the
newly-spliced block surfaces (not skipped) — pinned by
`identity_cursor_executes_each_finalized_block_exactly_once_across_catchup_reorg` (`:346`). The
index-slice version (`ordered[executed_up_to..]`) is the *superseded* bug, described in the past
tense at `:5`–`:17`.

**The fork is real; the mechanism is one step over.** Because `pending` is a *set* difference, *which*
blocks are outstanding depends on local poll timing, so two honest nodes apply the same finalized set
in **different sequences** — a lagged node applies a catch-up block at the END, a prompt node applies
it MID-PREFIX where τ puts it. The repo documents this at `execution_cursor.rs:400`–`:436` and
*asserts* it in `two_honest_nodes_that_polled_at_different_times_apply_a_different_sequence` (`:437`,
`assert_ne!` at `:482`), and the downstream receipt-continuity check
(`blocklace_sync.rs:9365`–`:9372`) then yields opposite verdicts. The module's own summary (`:433`):
the identity cursor *"preserves LIVENESS (exactly-once) and abandons the ORDER AGREEMENT the theorem
was supplying."*

CM has no such exposure, because under Prop. 9 a set-difference cursor and an index cursor **coincide**:
when the order is append-only, "not yet executed" is a suffix regardless of when you polled.

---

## 3. The equivocation-exclusion rule

**CM's rule is: keep both blocks, abstain from approving either, let the anchor decide, and repel the
equivocator going forward. It is emphatically *not* "keep the first one you saw."**

The five parts, all from CM:

1. **The blocklace stores equivocations; it does not filter them at receipt.** §1 (p. 2): *"miners
   cooperatively create a data structure that **accommodates equivocations**, termed blocklace."*
   §4.1: *"the blocklace created by Cordial Miners may include equivocations created by Byzantine
   miners, which are later excluded when each miner locally orders the blocks."*

2. **Approval abstains on sight of both.** Alg. 1 line 17:
   `approves(b, b1): return b1 ∈ [b] ∧ ∀b2 ∈ [b] : ¬equivocation(b1, b2)`. CM Fig. 1.B: *"the blue
   block of the next round, observing both equivocating red blocks, **approves neither**."* Approval
   is not transitive (§4.1) but *is* monotone per miner: *"if miner p approves b′ in B it also
   approves b′ in any B′ ⊃ B"* — because the witness is a specific p-block whose closure is fixed.

3. **The anchor decides inclusion, not the receiver.** Alg. 2 lines 39–40:
   `xsort(b, B) = topological sort wrt ≻ of {b′ ∈ B : approves(b, b′)}`. CM Fig. 4.C: *"The green
   fragment created by the green leader includes the V-marked red block, since the green leader does
   not observe the red equivocation. However, the X-marked red block is excluded from the purple
   fragment created by the purple leader, since the purple leader observes the equivocation."* This
   is what makes exclusion **deterministic across nodes**: every node computing the same anchor's
   segment reaches the same verdict, because the verdict is a function of the anchor's closure.

4. **Safety of exclusion is a counting lemma.** Lem. 31: *"For every two equivocating blocks in a
   blocklace, at most one can have a supermajority approval"* — via Obs. 30 (a miner approving both
   is itself an equivocator) plus quorum intersection. Note the honest bound: CM Fig. 1.D shows that
   **with two equivocators out of four, an equivocation *can* be ratified** — the guarantee is
   `f < n/3`, not unconditional.

5. **Repelling is a separate, forward-looking mechanism.** §3: *"after detecting an equivocation,
   correct miners ignore the Byzantine miner by not including direct pointers to their blocks."*
   Formalised as equivocator-repelling (Def. 29) with Prop. 39 guaranteeing an equivocator-free
   suffix. The admission check carries it: `correct_block(b)` (Alg. 1 line 16) requires
   `¬equivocator(b.creator, [b])`.

### Why first-write-wins is not a benign simplification

Under CM, dropping the second block of an equivocating pair at receipt breaks two separate things:

- **Prop. 36** (*"B(ρ) = B_p(ρ) for every correct p"* — all correct miners converge to the *same*
  blocklace) is the premise of CM's safety proof, Prop. 37. If node A drops `b₂` and node B drops
  `b₁` because they arrived in different orders, the laces do not converge, and Prop. 37 does not
  apply. **Arrival order is exactly the non-determinism CM's design removes**, by making the anchor
  rather than the receiver the decider.
- **Closure becomes uncomputable.** Alg. 3 line 49 buffers a block until `b.pointers ⊆
  hash(blocklace)`. A dropped `b₂` means any later block pointing at `b₂` can never be admitted — the
  node stalls on it — or, if the buffering rule is relaxed, the node computes `approves` against an
  incomplete closure and reaches a *different verdict from every other node*.

---

## 4. Federation membership and joining in the grassroots papers

**Short answer: the grassroots papers do not settle this, and they say so. Worse for the framing —
they name a protocol like ours as an example of what is *not* grassroots.** "Committee membership" is
indeed close to the wrong frame, but not for the reason the question supposed.

### 4a. The corpus explicitly classifies Cordial Miners as not grassroots

GS §2.1 (p. 7), immediately after Theorem 13:

> We note that blockchain consensus protocols with hardcoded miners, e.g. the seed miners of Bitcoin
> [12] or the bootnodes of Ethereum [13], as well as **permissioned consensus protocols with a
> predetermined set of participants such as Byzantine Atomic Broadcast [30, 16]**, are all
> **interfering**, as additional participants cannot be ignored.

Reference **[16] in GS is Cordial Miners itself** (*"Idit Keidar, Oded Naor, and Ehud Shapiro. Cordial
miners… DISC 2023"*, GS reference list p. 20). So Shapiro's own grassroots paper names Shapiro's own
consensus paper as the example of a *non-grassroots* protocol. This is not a tension in the corpus;
it is a deliberate layering, and it matters for what we may claim.

What *is* grassroots in the corpus is the **dissemination layer**: GS Prop. 29, *"The Cordial
Dissemination protocol CD is grassroots"* (GS:747). Ordering over a predetermined participant set is
not.

The formal notion (GS Def. 9): a protocol `F` is grassroots if `∅ ⊂ P ⊂ P′ ⊆ Π` implies
`TS(P) ⊂ TS(P′)/P` — a smaller community's behaviours must survive embedding in a larger one.
Theorem 13: *"An asynchronous, interactive, and non-interfering protocol is grassroots."* A fixed
committee fails **non-interference** (Def. 12) because a supermajority threshold over a fixed `Π`
cannot ignore added participants.

### 4b. Grassroots consensus is named as unsolved future work

GS §2.1, the very next sentences:

> However, Theorem 13 and the examples above **do not imply that ordering consensus protocols cannot
> be grassroots**. The problem is not with the consensus protocol as such, but **with the choice of
> its participants**. If participants in an instance of an ordering consensus protocol are
> **determined by the agents themselves via a grassroots protocol**, rather than being provided
> externally and a priori as in standard permissioned consensus protocols, or are required to include
> a predetermined set of initial participants as in Bitcoin and Ethereum, then the participants can
> reach consensus without violating grassroots. **Devising grassroots consensus protocols is a
> subject of future work** (see [21], Ch. 4).

**This is the honest answer to the question as asked: there is no specified join protocol for a
consensus federation in this corpus.** Our join channel cannot "match the intended model" because the
papers do not supply one. It is an invention — which is fine, and the papers even point at the shape
(participants determined by the agents themselves, in-band) — but it should not be described as
descent from a specified mechanism.

Note also GF's own table (GF §6.1, p. 14): Grassroots Flash is **`Consensus-based: No`**, with
**`Finality by/Trust in: Sovereign (= leader)`**. The grassroots payment line achieves
permissionlessness precisely by *not running consensus*. Its permissionlessness is not evidence that
a grassroots consensus federation exists.

### 4c. The one concrete join mechanism in the corpus — and what it does and does not license

GSN's WhatsApp-like protocol (WL) is the only membership protocol specified in the corpus. GSN §2.2
(p. 9): *"Any agent p can create a group with p as its sole member. A group creator can invite other
agents to become members and remove members at will. An invited agent may join the group and leave it
at will."*

The mechanism, GSN Alg. 3 (p. 15) — a **two-block in-band handshake**:

```
37: upon decision to invite q to group id do
38:   b ← new_block( (invite, q), {id} )
39: upon decision to accept invitation to join group id do
40:   if ∃b = (id′, (invite, p), {id}) ∈ B ∧ id.creator = id′.creator then b ← new_block(accept, {id′})
```

and membership is a **derived predicate over the blocklace**, not a registry — GSN Alg. 3 line 58:

```
58: procedure member(q, B)
59:    return ∃b, b′, b′′ ∈ B :
60:    b = (id, (group, name), ∅) ∧ id.creator = q′ ∧
61:    (q = q′ ∨ b′ = (id′, (invite, q), id) ∧ id′.creator = q′ ∧
62:    b′′ = (id′′, accept, {id'}) ∧ id′′.creator = q)
```

Four properties worth extracting, because they *are* settled:

1. **One sponsor suffices — there is no quorum.** The inviter is the group *creator* (`id.creator =
   id′.creator`). No supermajority of existing members votes.
2. **Both halves are blocks in the lace.** Invitation and acceptance are ordinary blocks with
   ordinary hash pointers; there is no side channel.
3. **Membership is computed, not stored.** `member(q, B)` is a structural predicate over `B`. There
   is no separate membership registry that could disagree with the lace.
4. **Consent is two-sided and explicit.** GSN p. 14: *"Acknowledgment of receipt of the invite does
   not imply acceptance — to accept, q has to create the corresponding accept block."*

**But this licenses much less than it appears to.** WL groups are *social* groups, each realised by
an **independent blocklace** (GSN §2.2: *"each hyperedge/group is realized by an independent
blocklace"*), running **no consensus** and **no supermajority**. Its safety statement is
correspondingly weak — GSN p. 10: *"We show below how the protocol preserves group integrity,
**provided the group creator is correct**."* A single trusted founder is the entire fault model.

So: a single-sponsor, in-band, two-block, consent-both-sides join with membership as a derived
predicate is **exactly right for a WL-style group** and is **not** a specified answer for admitting a
validator to a Byzantine-fault-tolerant committee, where the supermajority threshold `⌊(n+f)/2⌋+1`
(CM Def. 21) changes the moment `n` changes, and where "provided the sponsor is correct" is precisely
the assumption BFT exists to avoid.

**What no paper in this corpus specifies:** how a BFT committee changes size safely; what happens to
in-flight waves across a membership change; whether finality must pause. CM assumes a fixed `Π`
throughout (§2: *"a set Π of n ≥ 3 miners"*). CM App. D contemplates only *shrinking* the effective
set — *"As faulty miners are exposed, they are repelled and therefore need not be counted as parties
to the agreement"*, lowering the threshold toward simple majority — and files even that as future
work. **Growth is not treated at all.**

---

## 3b. What we do about equivocation — and whether it agrees

**Verdict: the blocklace layer is broadly faithful and in one respect stronger than CM. The
*finalization-vote* layer is a mechanism CM does not have at all, and its first-write-wins rule has
no counterpart in the paper to agree or disagree with. Two narrower mismatches are named below.**

### Agrees, and well

| CM | Ours | |
|---|---|---|
| `equivocation(b1,b2)` = same creator, mutually non-observing (Def. 17) | `detect_equivocation` (`blocklace/src/finality.rs:1743`) — the incomparability test, comment cites the paper form | ✅ faithful |
| equivocations retained in the lace, not filtered at receipt (§1, §4.1) | offender recorded in `equivocators`, block **retained as evidence** (`finality.rs:1540`–`1557`) | ✅ faithful |
| anchor decides segment inclusion via `approves` (Alg. 2 lines 39–40) | `hasEquivInPast` filter in `leaderSegment` (`BlocklaceFinality.lean:431`; `ordering.rs:691`–`693`) | ✅ role preserved |
| equivocating leader anchors nothing (Lem. 31 ensures ≤1 ratified) | `finalLeaderAt` singleton rule (`BlocklaceFinality.lean:384`), theorem `finalLeaderAt_needs_unique_candidate` (`:1043`) | ⚠ same intent, **stronger and non-monotone** — see §0 |
| repel/excommunicate the equivocator (§3, Def. 29, Prop. 39) | `auto_evict_equivocator` (`blocklace/src/constitution.rs:174`), wired at `node/src/blocklace_sync.rs:5566`; plus slashing (`federation/src/court.rs:191`), which CM does not specify at all | ✅ **exceeds** the paper |

### Mismatch 1 — two equivocation detectors with different scopes

`detect_equivocation` (`finality.rs:1743`) uses CM's round-independent incomparability test.
`EquivocationIndex` (`ordering.rs:205`–`228`) — the one that actually drives *ordering* exclusion —
groups by `(creator, round)` and flags only `ids.len() > 1`:

```rust
                groups.entry((block.creator, round)).or_default().push(*id);
        …
            if ids.len() > 1 {
```

Same-round ⟹ incomparable (CM notes this in the Prop. 9 proof: *"two different blocks of the same
depth cannot observe each other"*), so this is **sound but incomplete**: an equivocating pair at
*different* rounds that are mutually non-observing satisfies CM Def. 17 and `detect_equivocation`, but
is invisible to `EquivocationIndex`, hence not excluded by `xsort`. Since equivocating blocks are
deliberately retained in the lace, the two detectors can disagree about a block that is present.
**Worth a targeted test rather than an assumption either way** — I did not construct the witness.

### Mismatch 2 — the finalization-vote layer has no counterpart in CM

`node/src/finalization_votes.rs:596`:

```rust
        let signers = self.votes.entry(vote.block_id).or_default();
        // First-write-wins per signer: an equivocating member cannot displace
        // the vote already counted for it, nor be counted twice.
        let is_fresh = !signers.contains_key(&vote.voter);
        signers.entry(vote.voter).or_insert((…));
```

Measured behaviour: two conflicting votes for the **same** `block_id` (differing `merkle_root` /
`receipt_stream_root` — and those are the signed content, `:141`–`:151`) → the first is kept, the
second **silently discarded**, returning `Counted`/`AlreadyQuorum`, indistinguishable from a benign
re-emission. In the common case the second is not even verified: the fast path at `:581`–`:590`
short-circuits on `(block_id, voter)` presence *before* `verify_hybrid`. Two votes for **different**
`block_id`s both count in full — the dedupe is keyed by `block_id` first and nothing scans for a
repeat voter across blocks. `RecordOutcome` (`:291`–`:302`) has four variants and none reports
equivocation; nothing is proved, persisted, or metered.

**The right comparison is not "does this match CM's rule" — it is that CM has no such channel.** In
CM, ratification is not a message. `ratifies(B1, b2)` (Alg. 1 lines 18–19) counts *creators of
ordinary blocks* in `[B1]` that approve `b2`. There is no vote type, no signature collection, no
quorum certificate. Consequently **"voting twice" is not a distinct fault in CM — it is ordinary
blocklace equivocation**, caught by the machinery that already exists, proved safe by Lem. 31, and
punished by repelling.

We built a second, parallel attestation channel and then had to invent an equivocation policy for it
from scratch. First-write-wins is a *defensible* policy for that invented channel — safety at this
layer comes from root agreement (the Lean `quorumRoot` export at `:618`–`:627` requires a
supermajority of distinct signers on **one** `(ledgerRoot, streamRoot)` pair, so a double-voter splits
its weight rather than forging two quorums) — but it *tolerates* equivocation rather than detecting
it, and it is a surface CM's design does not have.

The layers are also **not connected**: `VoteCollector` holds no reference to
`Blocklace::equivocators()`, so a member proven to have forked *blocks* is evicted from the
constitution and from τ while its already-recorded finalization votes stay in the tally; and a member
that equivocates only at the vote layer is never detected at all.

---

## 4b. What we built for joining, and whether it agrees

**Verdict: it is an invention, because there is nothing in the corpus to match. Its *shape* is
closer to GSN's WL join than to anything else in the literature, but it is a BFT committee change,
which no paper here specifies. This one is genuinely ember's call, not a spec question.**

| GSN WL (the corpus's only join protocol) | Ours |
|---|---|
| one sponsor, the group creator, **no quorum** | one sponsor to propose + **`⌊2n/3⌋+1` of the current committee** to ratify (`constitution.rs:776`; `blocklace_sync.rs:3170`) |
| invite + accept are **ordinary blocks in the lace** | join request is **not a block** and never enters the lace (`blocklace_sync.rs:661`–`665`); it rides a dedicated gossip envelope (`net/src/gossip.rs:3176`–`3252`) |
| membership is a **derived predicate** `member(q,B)` over the lace | membership is on-chain state replayed into `Constitution` — `committee_replay.rs:1`–`3`: *"the constitution as a PURE VIEW of the chain, never a second source of truth"* |
| consent two-sided and explicit | two-sided: self-certified request + ML-DSA proof of possession (`blocklace_sync.rs:3037`–`3049`), then committee ratification |
| no key material; group key shared secretly by founder | ML-DSA proof of possession, domain-separated `JOIN_REQUEST_PQ_BINDING_V1` (`blocklace_sync.rs:667`–`712`) |

The ML-DSA proof of possession has **no analogue in the corpus** — CM assumes *"each miner is
equipped with a single and unique cryptographic key-pair, with the public key known to others"*
(§2) and never discusses key registration. It is ours, and the code gives a sound reason for it
(`blocklace_sync.rs:3037`): without it *"the committee would admit a member whose hybrid id never
authors a block, and under the fail-closed projection that is a permanent finality halt for
everyone."* That is a real hazard our hybrid identity creates and the papers never face.

Two findings adjacent to the join path that the papers *do* bear on:

- **"A live Join HALTS finality" is now obsolete as the normal case, live as a failure mode.** The
  fail-closed halt is current code (`blocklace_sync.rs:2179`–`2197`: *"finality HALTS until the
  missing member's ML-DSA key is committed"*), and the historical deadlock is documented at
  `:645`–`:659`. Well-formed joins now commit the ML-DSA key at proposal-registration time
  (`:18775`–`:18780`), but a join whose key is uncommittable or disagrees still halts finality on
  every node with only a `warn!` in the way (`:18781`–`:18789`). **CM offers no guidance here** — it
  assumes a fixed `Π` and never treats growth.
- **`auto_approve_joins` converts the federation to effectively permissionless, and one trigger is a
  stray file.** `node/src/lib.rs:2823`: `let auto_approve_joins = auto_approve_joins_flag ||
  data_path.join(".devnet").exists();`. A `.devnet` marker in a production data directory silently
  admits any peer that can reach the gossip port. This is not a papers question; it is a
  custody/gate question and belongs on the short list of things that deserve a pause.

---

## 5. What else the papers settle that we have been guessing at

Ordered by how much they change what we should do.

### 5.1 Cordiality is an *admission check*, and it is the hypothesis under everything

This is the most valuable single item in the corpus for us, and it reframes §2.

CM Def. 25: *"A block b ∈ B of round r is **cordial** if r = 1 or it acknowledges blocks by a
supermajority of miners of round r − 1."* Alg. 1 lines 15–16 makes it a predicate on a single block:

```
15: procedure correct_block(b):
16:    return {b′.creator : hash(b′) ∈ b.pointers} is a supermajority ∧ ¬equivocator(b.creator, [b])
```

and Alg. 3 line 49 makes it a **precondition of receipt** — *"incorrect blocks are ignored."*

From that one cheap, local, per-block check the whole safety story follows: cordial ⟹ leader-safe
(Prop. 3) ⟹ τ monotone (Prop. 9) ⟹ τ safe (Prop. 10) ⟹ protocol safe (Prop. 37).

**We appear not to enforce it.** A repo-wide search for the cordiality predicate found no admission
gate in `blocklace/` (`rg -i cordial` over `blocklace/src/` returns nothing; the local-authorship gate
in `try_add_block_with_predecessors` is `consensus-time-v1`, `blocklace/src/finality.rs:1258`). If
that is right, we are missing the hypothesis *and* the mechanism that would establish it.

**The shape of the fix this suggests is much cheaper than a runtime stability check.**
`FinalizedRegionStable`/`stableCheck` compare two whole laces and two whole τ folds — expensive, and
nobody calls them. CM's condition is a **per-block predicate over that block's own pointers**,
evaluated once at receipt, and it *implies* the stability property as a theorem. If τ is re-anchored
per §0, cordiality-at-admission is the natural companion, and it is the thing to build.

### 5.2 CM's answer to Byzantine flooding: at most two tips per miner

CM Alg. 1 line 5:

```
 5:    b.pointers ← hash(tips), where tips are the tips of blocklace_prefix(d), at most two tips per miner
    ▷ Def. 19; two-tips limitation to prevent a Byzantine miner from flooding the blocklace before
    ▷ being excommunicated
```

A structural cap on the pointer set, at block *creation*. **We have no such limit** (no `max_tips` /
two-tips rule found). What we have instead is `enforce_member_cap`
(`node/src/finalization_votes.rs:347`–`390`), which bounds memory at the *vote* layer by evicting a
member's oldest "lonely" un-attested block. That is a reasonable ad-hoc defence for the invented vote
channel, but it is not the paper's answer, and the paper's answer is simpler and applies where the
flooding actually happens.

### 5.3 We are running CM's Eventual-Synchrony instance — check we took the whole instance

Ours: `wavelength = 3` (`node/src/finality_gate.rs:82`, `ordering::OrderingConfig::default`) and
`wave_leader` is round-robin (`blocklace/src/ordering.rs:270`). That is exactly CM's ES instance
(Alg. 4 §4.2: `w ← 3`, leader *"selected deterministically"*), not the asynchronous one (`w = 5` with
a retrospective shared coin, §4.1). Coherent so far.

But CM's ES instance is a **package**, and the round-advance rule is part of it. Alg. 4 line 67
`es_advance_round()` advances only on the per-round finality conditions **or a timeout**, and CM §6.2
says why in a sentence that applies directly to us:

> These conditions are to prevent the adversary from ordering the messages after GST, in particular,
> the leader block and the blocks that super-ratify it, **as the leader is known in advance**.

With a publicly predictable round-robin leader and no such gating, an adversary controlling delivery
order can starve waves indefinitely. Prop. 38 (ES leader-liveness w.p. 1) is stated **only under
`timeout > ∆`**. I did not audit our round-advance rule this pass — **this is the next thing to
check**, and it is a liveness question, not a safety one.

### 5.4 Supermajority: our threshold coincides with CM's at `n = 3f+1` and is never weaker

CM Def. 21: a supermajority is `|P| > (n+f)/2`. Ours: `(n * 2 / 3) + 1`
(`blocklace/src/ordering.rs:299`). At `n = 3f+1` both give `2f+1`. Off that line ours can be
*stricter* (e.g. `n=6, f=1`: CM `> 3.5` → 4; ours → 5), which is safe but costs liveness. No action;
recorded so nobody re-derives it.

### 5.5 CM anticipates the shrinking threshold — and we already do it

CM App. D:

> As faulty miners are exposed, they are repelled and therefore need not be counted as parties to the
> agreement, which means that the number of remaining faulty miners, initially bounded by f,
> decreases. As a result, the supermajority needed for finality is not `(n+f)/2` … but
> `(n+f−2f′)/(2(n−f′))`, where `f′` is the number of exposed faulty miners.

CM files this as future work. `auto_evict_equivocator` (`blocklace/src/constitution.rs:174`–`185`)
removes the equivocator and calls `compute_threshold(self.participants.len())` — i.e. we already do
the thing the paper contemplates. Worth knowing that this is *ahead of* the paper rather than a
deviation from it.

### 5.6 Garbage collection: the papers say we cannot have fairness and GC together in asynchrony

BS §7 is the only sustained treatment:

> One of the main practical challenges and a potential reason that DAG-based BFT protocols are not
> yet widely deployed is the need for **unbounded memory** to guarantee validity and fairness. …
> DAG-Rider, Aleph, and Narwhal use a round-based structured DAG, but **do not provide a solution**.

Narwhal's GC *"sacrifices the Validity (fairness) property … blocks of slow parties can be garbage
collected before they have a chance to be totally ordered."* CM App. D adopts Bullshark's framing:
fairness is achievable in synchronous periods, so in the **ES** version one can be fair after GST
*and* garbage collect. Since we are running the ES instance (§5.3), that route is open to us — but it
is a design we would have to build, and no paper here hands it over.

### 5.7 Fairness: CM's τ liveness is weaker than DAG-Rider's, by construction

DAG-Rider carries **weak edges** specifically so that every block is eventually ordered (DR §5; BS §7
notes *"weak links to refer to yet unordered blocks in previous rounds, which guarantees that every
block is eventually ordered"*). CM has no weak edges. Its liveness is Obs. 11 — *"If a p-block b by a
miner p not equivocating in B is **observed by a final leader** in B, then b ∈ τ(B)"* — plus Prop. 5's
condition that the miner be **disseminating** (Def. 27) and non-equivocating. A correct-but-isolated
miner whose blocks no final leader ever observes is not covered. This is a real difference between the
two protocols and is easy to mistake for an implementation gap on our side; it is not.

### 5.8 The equivocating leader is handled by approval, not by forfeiting the wave

Restating §0's second deviation here because it is a place where the paper solved a problem
differently and better. CM §4.2 accepts that *"an equivocating leader can have several leader blocks
in the same round"* and does not treat that as fatal to the wave: Lem. 31 guarantees at most one of
them can hold supermajority approval, so at most one can be ratified, so the wave still resolves.
Our `finalLeaderAt` (`BlocklaceFinality.lean:384`) instead returns `none` on `≥2` candidates,
discarding the wave — and, because the count is over the live lace, **retracting waves already
anchored** when a second leader-slot block arrives late. CM's rule is both more live and monotone.

---

## Summary

| # | Question | Papers say | We do | Agree? |
|---|---|---|---|---|
| **0/1** | Ordering input | Anchor's causal past `[b1] \ [b2]`, fixed by signed pointers (CM Def. 6, Alg. 2:37) | Union of causal pasts of live-lace ratifiers at wave end (`BlocklaceFinality.lean:409`) | ❌ **DEVIATION** — bug fix, ours to do |
| **2** | Prefix-monotonicity | **Guaranteed** (CM Prop. 9) under cordial + closed + supermajority-correct — all established *by construction* | Assumed as `FinalizedRegionStable` (`TauPrefixMonotone.lean:102`), **evaluated nowhere** (zero executable refs repo-wide) | ❌ we assume what CM proves |
| **2** | Prefix caching | Explicitly authorised **because of Prop. 9** (CM §5 p. 9) | `ExecutionCursor` does it without Prop. 9 → two honest nodes apply different sequences (`execution_cursor.rs:437`, asserted) | ❌ optimisation without its premise |
| **3** | Equivocation, blocklace layer | Retain both; anchor decides via `approves`; repel (CM Alg. 1:17, Alg. 2:39, Def. 29) | `detect_equivocation` faithful; retained as evidence; anchor filter present; evict **and slash** | ✅ mostly, and exceeds on slashing |
| **3** | Equivocation, ordering index | Round-independent incomparability (CM Def. 17) | `(creator, round)` groups (`ordering.rs:205`) — sound, **incomplete** | ⚠ narrower; needs a test |
| **3** | Finalization votes | **No such channel exists in CM** — ratification is ordinary blocks | First-write-wins collector, unconnected to blocklace equivocators (`finalization_votes.rs:596`) | ⚠ no counterpart; invented surface |
| **4** | Federation membership | **Not settled.** CM is named as *not grassroots* (GS §2.1, ref [16]); grassroots consensus is **future work** | Permissioned: sponsor + `⌊2n/3⌋+1` ratification | — invention, and legitimately so |
| **4** | Join mechanism | Only GSN WL: one sponsor, in-band blocks, membership as derived predicate — for a **non-consensus** group with a trusted founder | Out-of-band gossip envelope, ML-DSA PoP, on-chain committee | — different problem; ours is reasonable |
| **5.1** | Cordiality | **Admission check** (CM Alg. 1:15, Alg. 3:49) — the hypothesis under all of it | No enforcement found in `blocklace/` | ❌ missing, and it is the cheap fix |
| **5.2** | Flood defence | ≤2 tips per miner at creation (CM Alg. 1:5) | Absent; ad-hoc `enforce_member_cap` at vote layer | ❌ missing |
| **5.3** | ES instance | `w=3` + deterministic leader **+ timeout-gated round advance, `timeout > ∆`** (CM Alg. 4:67, Prop. 38) | `w=3` + round-robin ✅; round-advance rule **not audited** | ? next thing to check |

### Three things that follow

1. **Re-anchor τ on the committed block's causal past.** This is a return to CM Def. 6, not a
   departure from it — no taste call required, and the greenfield doctrine says land it.
2. **Enforce cordiality at block admission.** It is a per-block check over that block's own pointers
   (CM Alg. 1:15) and it is what *earns* prefix-monotonicity as a theorem. It is far cheaper than the
   whole-lace `stableCheck` nobody calls, and it makes `FinalizedRegionStable` derivable instead of
   assumed.
3. **Make finality monotone.** Drop the "≥2 leader candidates ⇒ forfeit the wave" rule in favour of
   CM's approval-based resolution (Lem. 31), so a late block can never retract an anchored wave.

### Where the papers do not settle it — say so plainly

- **BFT committee growth.** No paper here specifies how a committee changes size, what happens to
  in-flight waves, or whether finality must pause. CM assumes a fixed `Π` (§2) and treats only
  *shrinking*, as future work (App. D). Our join design is ours to justify on its own terms.
- **Grassroots consensus.** GS §2.1 names it as *"a subject of future work."* We may claim grassroots
  descent for **Cordial Dissemination** (GS Prop. 29) and should not claim it for the ordering layer.
- **Whether our `(creator, round)` equivocation index is exploitable.** Structurally narrower than CM
  Def. 17; I did not construct a witness. Test it, do not assume either way.
