# Dynamic committees: what the literature actually settles

**Date:** 2026-08-08
**Method:** read-and-think. No protocol code changed by this pass.
**Corpus:** `pdfs/` (28 PDFs), read as text. Every claim about a paper carries paper +
section/theorem/algorithm-line. Plus `github.com/hellas-ai/awesome-consensus` (README fetched
2026-08-08) as an index check for sources the Zotero library lacks.

**Companion:** `docs/reference/FEDERATION-DESIGN-GAPS-2026-08-08.md` measures our federation
against this. **Predecessor:** `docs/reference/CONSENSUS-FROM-SOURCE-2026-08-08.md` (`66681e080`) —
its τ verdict stands; §0 below corrects one of its negative claims.

Citation shorthand: **DZ** = Duan & Zhang, *Foundations of Dynamic BFT* (S&P 2022, eprint
2022/597). **LL** = Li & Lesani, *Reconfigurable Heterogeneous Quorum Systems*, full version
(DISC 2024, arXiv:2304.02156v2). **LPR** = Lewis-Pye & Roughgarden, *Permissionless Consensus*
(arXiv:2304.14701v5). **CM** = Keidar, Naor, Poupko, Shapiro, *Cordial Miners* (arXiv:2205.09174v6).
**GS** = Shapiro, *Grassroots Systems* (2301.04391). **GA** = Shapiro, *Grassroots Architecture for
Digital Democracy* (2404.13468). **OG** = Badertscher, Gaži, Kiayias, Russell, Zikas, *Ouroboros
Genesis*. **DPRB** = Anikina, Bezerra, Kuznetsov, Schiff, Schmid, *Dynamic Probabilistic Reliable
Broadcast* (arXiv:2306.04221v2).

---

## 0. THE CORRECTION — "no paper treats BFT committee growth" is false

`CONSENSUS-FROM-SOURCE-2026-08-08.md` closes with:

> **BFT committee growth.** No paper here specifies how a committee changes size, what happens to
> in-flight waves, or whether finality must pause.

For the corpus it read (Cordial Miners + grassroots + DAG-BFT lineage) that was **accurate**. As a
statement about the literature it is **wrong**, and the corpus now contains the refutation.

**BFT committee growth is a named, formalised, proved, implemented and benchmarked problem.** It is
called *dynamic BFT* or *reconfiguration*. DZ gives it a formal syntax, six graded security
definitions, four protocols, machine-independent proofs, and a 10,000-LOC Go implementation
evaluated to n=30. **Rondo** (§5.1) transplants it onto HotStuff, by one of DZ's own authors, with
an explicit install rule and drain rule. **LPR §15.3** (§4.2b) states the boundary rule for a
chained protocol, with the consistency violation you get without it spelled out in fn. 51. LL gives
the quorum-system-level treatment, including two **impossibility** theorems about what a
reconfiguration protocol can preserve. All of it was sitting one citation away:
DZ's related-work section (§II) alone names Paxos reconfiguration [30], SMART [34], Raft joint
consensus [38], BFT-SMaRt [50], DynaStore [2], Vertical Paxos, DBRB [20], and the whole
virtual-synchrony line [7, 11, 37, 46].

**The class of error is worth naming**, because it is the one this repo keeps paying for: *a
negative claim inherits the shape of the shelf it was drawn from.* "The papers do not settle this"
was true of a shelf assembled to answer a **τ ordering** question. The correct output of that pass
was "this corpus does not contain the reconfiguration literature; go get it" — not a negative about
the literature.

What *does* survive, and is confirmed below:

- **No paper in this corpus treats reconfiguration of a DAG-BFT protocol** (§3). That negative I
  will defend, and I name exactly what I searched.
- **CM itself assumes a fixed Π** (CM §2: *"a set Π of n ≥ 3 miners"*) and its App. D contemplates
  only *shrinking*, as future work. Verified: `pdfs/cordial-miners-shapiro-2205.09174.pdf` App. D,
  and a full-text grep of the paper for `member|join|dynamic|reconfigur` returns nothing else.

---

## 1. Foundations of Dynamic BFT (DZ) — the directly on-point paper

**What it is.** A formal treatment of BFT where replicas join and leave, plus **Dyno**, a
partially-synchronous dynamic BFT protocol built on PBFT-shaped machinery (DZ §VI uses Bracha
broadcast as the normal-case oracle; `init()`/`deliver()` are the interface). Leader-based, view
changes, `n ≥ 3f+1` per configuration.

### 1.1 The model — every object we are missing has a name here

DZ §III.B:

- A **configuration** `c` is an integer; `M_c` is its membership. `c` is initialised to 0 and a
  replica changes configuration by **installing** one.
- Def. III.1–III.8 grade "correct" by configuration: *correct in c*, ***c*-correct** (correct in `c`
  *and* either `c` is the latest for everyone or the replica is in `M_{c+1}`), ***c*-faulty**,
  ***g*-correct** (correct in all its configurations), ***g_c*-correct**.

That grading exists because of a fact DZ §IV states and we have not internalised:

> The agreement property … requires that if a correct sender stays online for a sufficiently long
> time, a correct receiver will receive the messages from the sender. **This, however, is not the
> case for dynamic BFT.**

DZ §I is blunter, and it is a direct hit on the "we can reason about this the usual way" instinct:

> We find that even some classic protocols in the secure distributed computing community (e.g.,
> [46]) simply assume message delivery across configurations and **the proofs for these protocols
> are actually flawed.**

Reference [46] is Schiper's dynamic-atomic-broadcast specification — i.e. the standard reference
work in this area had a broken proof for exactly this reason. A perfect channel guarantees delivery
only when the sender is correct *for all time*; a member that leaves later was never such a sender.

### 1.2 The three assumptions DZ requires — all three are choices we have not made

DZ §III.D:

| Assumption | Statement | Our status |
|---|---|---|
| **Standard quorum** | per-configuration optimal resilience: `f_c ≤ ⌊(n_c−1)/3⌋`, `Q_c = ⌈(n_c+f_c+1)/2⌉` | we recompute a threshold per roster, but see §1.5 |
| **Bounded churn** | *"from configuration c to c+1, at least `Q_c` c-correct replicas are still in c+1"* | **unstated anywhere** |
| **Known genesis** | *"the initial configuration is known by all replicas in the universe Π"* | ✅ `genesis.json` |

A fourth, optional, stronger one — the **G-correct assumption** — is *"there exist at least
`F = max({f_c})+1` replicas that are correct across all configurations"*, i.e. enough correct
replicas never leave. DZ uses it to buy stronger agreement (Thm. VII.1) *without changing the
protocol*, and is candid that it is impractical because it requires knowing `max(f_0, f_1, …)` in
advance (DZ §VII, p. 10).

### 1.3 The property that dynamic BFT needs and static BFT does not

DZ §III.E adds two properties to the static four:

- **Same configuration delivery.** *"If a correct replica `p_i` (resp. `p_j`) delivers `m` in
  configuration `c_i` (resp. `c_j`), then `c_i = c_j`."*
- **Enhanced total order** (the unification of that with total order): *"If a correct replica in
  configuration `c` delivers a request `m` with a sequence number, and another correct replica in
  configuration `c′` delivers a request `m′` with the same sequence number, then `m = m′` **and
  `c = c′`**."*

**Read that last conjunct slowly.** A sequence number must determine not only *what* was executed
but *under which committee*. That is a property about our chain that we have never stated, and it
is the one that makes "which roster does this vote count against" a well-posed question instead of
a race.

DZ §III.E then works through two failed attempts at a client-facing liveness property before
landing on **consistent delivery**: *"A correct client submitting `m` will deliver a correct
response which is consistent with the state in some configuration where `m` is delivered."* The
reason the obvious attempt fails is worth quoting because it is a hazard we have (§4 of the
companion doc):

> Even if the client learns the information of the configuration `c` for which the request `m` is
> delivered … the reply messages sent by correct replicas in configuration `c` may not be able to
> reach the client. This is because the perfect channel guarantees message delivery only when the
> sender is—all the time—correct, but the sender may leave the system in some future configurations.

DZ §III.F/Table I then grades **agreement** into six variants (`V`, `V₁`, `V₂`, `V′`, `V₁′`, `V₂′`)
by whose correctness appears in the if-clause and the main clause, and maps each to a construction:
Dyno (`V` under standard quorum; `V₁` under G-correct), Dyno-A (`V₁` under standard quorum),
Dyno-C / Dyno-AC (`V₂`). This is the most useful piece of engineering taxonomy in the paper: **the
strength of your agreement guarantee across a membership change is a dial, and it costs a specific
mechanism to turn it.**

### 1.4 The Dyno mechanisms — this is the parts list

From DZ §V.B and Figs. 4–7. Each is a discrete mechanism with a stated job:

1. **Configuration as ordinary state; membership requests are ordinary requests.** (§V.B, and DZ
   credits Paxos [30], Schiper [46], BFT-SMaRt [50] for the strategy.) But DZ is explicit that this
   *alone* is not enough: *"doing so alone without further modifying the protocol, may create
   liveness issues (zero throughput), as we will theoretically show for any leader-based BFT
   protocol in Sec. IV and experimentally show for BFT-SMaRt in Sec. VIII."*

2. **A deterministic intra-batch order: regular requests first, then membership requests, then
   install.** Fig. 5 `deliver(batch)`: reply to every regular request, *then* `c ← c+1`, *then*
   apply each `ADD`/`REMOVE`. This is what makes "which configuration executed this request" a
   function of the committed order rather than of local timing.

3. **Temporary membership (the learner phase).** §V.B: *"each new replica acts as a learner.
   Existing replicas send the normal-case operation messages to both replicas in the current
   configuration and all the temporary members. **The quorum size, however, still remains the same
   as the current configuration.**"* Fig. 5 says it twice: `f_c = ⌊(|M|−1)/3⌋` and `Q_c` are
   computed from `M`, not `TM`.

4. **State transfer before counting — and it is load-bearing for *safety*, not just liveness.**
   §VI.A: *"After `p_i` delivers the join request, it waits until it completes state transfer by
   accepting `2f_c+1` `HISTORY` messages. After that, `p_i` participates in the normal-case
   operation."* The proof of Lemma C.9 Case (1) leans on it directly:

   > any new replica that joins the system participates in the protocol after it completes state
   > transfer from replicas in `c`. Therefore, if any of the `f_c+1` correct replicas is a new
   > replica, **it will not accept `m′` if `m` is included in its execution history**.

   and Case (3) again: *"Before `p_i` participates in the protocol, it completes state transfer with
   `Q_c` replicas in configuration `c` … a contradiction with the fact that `Q_c` replicas have sent
   PREPARE messages for `m`."* **A joiner that votes before state transfer is a safety bug, not a
   performance bug.**

5. **Configuration history `chist`** (§VI.B) — a genesis-rooted, sequentially-ordered list of
   membership batches, each carrying a **proof of delivery** (`Q_c` signatures from `M_c`). Lemma
   C.1: verifiable by *any* replica or client from `M_0` alone, inductively. Lemma C.2: **totally
   ordered** — two valid `chist` cannot disagree, by quorum intersection at the first divergence.
   This is a portable-membership-certificate design, and it is what lets a stranger check the
   current committee without trusting whoever told them.

6. **Configuration discovery as a named sub-protocol** (§VI.B, Fig. 7 self-discovery; App. B lazy
   discovery and configuration master). DZ §I: *"The configuration discovery protocols are not just
   crucial from the functionality perspective but to the correctness of our dynamic BFT protocols."*

7. **View-change messages carry `c`, and are forwarded across configuration gaps** (Fig. 6). A
   replica receiving a `VIEW-CHANGE` with `c′ < c` forwards it to `M_c \ M_{c′}`; with `c′ > c` it
   adopts `M_{c′}` (after verifying the membership proof) and re-sends to `M_{c′} \ M_c`. This is
   the specific fix for DZ Fig. 3's three view-change pathologies (§IV): the new leader cannot
   collect enough view-change messages; the designated leader does not know a view change is
   happening; **multiple replicas each believe they are the leader**.

8. **Leave completes only after the leaver delivers its own `REMOVE`** (Dyno-C, §VII, footnote 2).
   Weakenable: *"a replica can leave after it is certain that the `REMOVE` request will be
   delivered, e.g., after it receives a prepare certificate."*

### 1.5 The cross-configuration quorum-intersection arithmetic — the thing to actually compute

DZ's safety proofs (Lemma C.7, Lemma C.9) are exactly a **quorum intersection argument across a
configuration boundary**. Lemma C.9 Case (1), for one join:

> `Q_c + 1` replicas have sent `COMMIT` messages for `m′` in `c′`. Since `Q_c` replicas have sent
> `COMMIT` messages for `m` in `c`, the two quorums in total have size `2Q_c + 1`. … Since
> configuration `c′` has `n_c + 1` replicas, the two quorums have at least
> `2Q_c + 1 − (n_c+1) = 2⌈(n_c+f_c+1)/2⌉ − n_c ≥ f_c + 1` replicas in total.

Case (2), for `l` removals, and Case (3) for mixed. For multiple joins DZ says `n_c → n_c + l` and
`Q_c → Q_c + q` with `0 ≤ q ≤ l`, and states a tighter bound on `q` which the text extraction
renders ambiguously (`⌈l/3⌉` or `⌈2l/3⌉`) — **I could not resolve which from the PDF text and do
not rely on it.** The inequality is the portable part; the constant is not.

**So instantiate the inequality for our threshold formula.** Ours is `T(n) = ⌊2n/3⌋ + 1`
(`blocklace/src/ordering.rs:299`). Config `c` has `n` members; config `c+1` adds `l` joiners. A
`c+1` quorum has at least `T(n+l) − l` members drawn from the *old* roster, so

```
|Q_c ∩ Q_{c+1} ∩ M_c|  ≥  T(n) + T(n+l) − l − n
```

and safety needs that to exceed the Byzantine bound `f = ⌊(n+l−1)/3⌋`. Asymptotically
`T(n)+T(n+l)−l−n ≈ n/3 − l/3 + 2` against `f ≈ (n+l)/3`, giving `2 > 2l/3`, i.e. **`l ≤ 2`**.
Instantiated:

| n → n+l | T(n) | T(n+l) | old-roster intersection | f | safe? |
|---|---|---|---|---|---|
| 4 → 5 (l=1) | 3 | 4 | 2 | 1 | ✅ |
| 4 → 6 (l=2) | 3 | 5 | 2 | 1 | ✅ |
| **4 → 7 (l=3)** | 3 | 5 | **1** | **2** | ❌ |
| 7 → 8 (l=1) | 5 | 6 | 3 | 2 | ✅ |
| 7 → 9 (l=2) | 5 | 7 | 3 | 2 | ✅ |
| **7 → 10 (l=3)** | 5 | 7 | **2** | **3** | ❌ |

**At most two members may be installed per configuration step** under our threshold formula, on the
intersection argument alone. DZ recovers larger batches, but *only* via mechanism (4) — the joiner
cannot contradict what it state-transferred. **We have neither the bound nor the mechanism**, so we
currently have no argument at all. (Derivation mine, from DZ's inequality; the numbers are
arithmetic and checkable.)

### 1.6 What DZ costs

DZ §VIII: Dyno-S (the intuitive design, where every membership change forces a view change)
produces *"a window of zero throughput"* — the paper's whole point is that this is avoidable. Dyno
handles membership changes without a view change and without throughput degradation, at 10k LOC in
Go, measured against BFT-SMaRt to n=30 (`f=1..5`, 3f+1). BFT-SMaRt's own reconfiguration is
measured dropping to zero throughput for up to 50s.

---

## 2. Reconfigurable Heterogeneous Quorum Systems (LL) — the quorum-level treatment

**What it is.** A model where *each process declares its own quorums* (LL Def. 1), the properties a
quorum system must keep (consistency/intersection, availability, **inclusion**), reconfiguration
protocols for Join/Leave/Add(q)/Remove(q), **two impossibility theorems**, and a graph
characterisation (the *quorum graph*, whose unique **sink component** is where all coordination is
actually needed).

Our system is the degenerate homogeneous case: LL §3 *HQS Instances* calls it a **dissemination
quorum system (DQS)**, *"and the cardinality-based quorum system as a special case"*, which
*"declares a global set of quorums for all processes"* and *"is outlived for all well-behaved
processes W"*. So LL's heterogeneity machinery is not our machinery — **and I will not pretend it
is.** What transfers is the reconfiguration analysis.

### 2.1 The reconfiguration attack — this is our hazard in its general form

LL §5, *Reconfiguration Attacks*, verbatim in substance:

> Let `P = {1,2,3,4}` where the Byzantine set is `B = {4}`. Let `Q(1) = {{1,2,4}}`,
> `Q(2) = {{1,2},{2,3}}`, `Q(3) = {{2,3}}`. This quorum system enjoys quorum intersection … Let
> process 2 locally add a quorum `q₁ = {2,4}` … Similarly, let process 3 locally add a quorum
> `q₂ = {1,3}` … **Both reconfiguration requests seem safe, and if they are requested concurrently,
> they may be both permitted. However, the two new quorums do not intersect.** An attacker can
> issue a transaction to spend some credit at process 2 with `q₁`, and another … at process 3 with
> `q₂`. That leads to a **double-spending and a fork.** Even if processes 2 and 3 send their
> updated quorums to other processes, the attack can be successful **if the time to send and
> receive updates is longer than the time to process a transaction.**

Homogenise it and you get *our* shape exactly: **two nodes that hold different rosters compute
different quorums, and two quorums drawn from different rosters need not intersect.** The final
sentence is the operative one — the window is not "membership change is unsafe", it is "the
interval during which two correct nodes disagree about the roster is unsafe", and its length is a
propagation delay you do not control.

### 2.2 The impossibility theorems

- **LL Thm. 21.** *"There is no Leave or Remove reconfiguration protocol that is policy-preserving,
  availability-preserving and terminating."*
- **LL Thm. 22.** *"There is no Add reconfiguration protocol that is policy-preserving,
  consistency-preserving, and terminating."*

with the definitions at LL §5: *terminating* = every operation by a well-behaved process eventually
completes; *policy-preserving* = a Leave/Remove only removes individual minimal quorums, a Join does
not change existing quorums, an `Add(q)` by `p` only adds `q` to `p`'s quorums;
*consistency-preserving* = maps consistent systems to consistent systems; *availability-preserving*
= only affects availability of the process requesting Leave, or Remove of its last quorum.

LL resolves both by **never sacrificing consistency** (§6, §8): it ships an availability+consistency
Leave/Remove protocol and a policy+consistency one, and an Add protocol preserving everything but
policy.

**Honest scope note.** *Policy-preservation is about heterogeneous trust declarations.* In a
cardinality system there is one global policy, so Thms. 21–22 do not bind us as stated — a fact I
want on the record so nobody cites them at us later as a blocker. What binds us is the *method*: LL
proves you must **pick which property you sacrifice, explicitly, before writing the protocol**, and
that consistency is the one you never sacrifice. Our design has never made that choice out loud.

### 2.3 What LL's Join actually does, and the property nobody names

LL Alg. 3 + Lemma 24. A joiner `p` submits an initial trusted set `ps`, probes those processes for
*their* quorums, and **grows** its tentative quorums (`S ← S \ {q} ∪ {q ∪ q′}`) until they are
*quorum including* (L. 23), then adopts them. Lemma 24: this preserves quorum intersection,
availability and inclusion, *"since the existing quorums have intersection at `O`, and the new
quorums are supersets of existing quorums"*, and *"the quorums of existing processes do not
change."*

**Join is the easy direction and LL says so** (§6: *"The Join protocol is straightforward"*).
Because a joiner's quorums are supersets of existing ones, intersection is free. **Leave is the
hard direction** — it needs total-order broadcast, a `tomb` set of maybe-departed processes, a
`Check` round, and a local test that the intersection of the leaver's own quorums minus itself is
still blocking (Alg. 1 L. 14, L. 22). The asymmetry is a fact about the problem, not about LL.

The property that has no counterpart in our vocabulary is **quorum inclusion** (LL Def. 9): every
quorum should include a quorum of each of its members. LL §1: *"This property trivially holds for
homogeneous quorum systems where every quorum is uniformly a quorum of all its members."* So it is
free for us — *provided we stay homogeneous*, which is a constraint worth knowing we are relying on
if anyone ever proposes per-node trust or weighting.

### 2.4 The optimisation that generalises

LL Lemma 20: *"Any leave or remove operation by a process outside the sink component of the quorum
graph preserves consistency"* — hence needs **no coordination at all**, only a notification to
followers (Alg. 1 L. 19–20, the blue path). Thm. 19: all well-behaved processes of the minimal
quorums lie in the single sink component; Lemma 18: there is only one.

Generalised: **the set of members whose departure can break intersection is identifiable, and it is
smaller than the whole roster.** In a cardinality system the sink is everyone, so this buys us
nothing directly — but it is the right question to ask of any weighting scheme we might add.

---

## 3. Reconfiguration *of a DAG protocol* — this negative I will defend

**Nothing in this corpus treats reconfiguration of a DAG/blocklace consensus protocol.** Here is
exactly what I searched, so the claim is falsifiable.

Full-text grep for `reconfigur|epoch|membership|dynamic|join|churn|validator set|committee change`
over the extracted text of: `dag-rider-all-you-need-is-dag-2102.08325`,
`bullshark-dag-bft-protocols-made-practical-2201.05677`, `shoal-dag-bft-latency-2306.03058`,
`shoal-plus-plus-2405.20488`, `banyan-fast-rotating-leader-bft-2312.05869`,
`cordial-miners-shapiro-2205.09174`. Every hit inspected. Results:

- **DAG-Rider** — two hits, both irrelevant (a *dynamic adversary*, DR §2; a bibliography entry).
  Fixed `Π` throughout.
- **Bullshark** — two hits: a dynamic adversary (§2), and one *related-work* sentence about
  **Mir-BFT's** evaluation (§10): *"Crash-faults lead to throughput dropping to zero for up to 50
  seconds, and then operation resuming after a reconfiguration to exclude faulty nodes."* That is
  Bullshark reporting someone else's number. Bullshark itself has no reconfiguration.
- **Shoal / Shoal++** — every "dynamic" hit is *dynamic anchor re-interpretation* or *dynamic
  leader scheduling*, i.e. **which validator leads**, over a **fixed** validator set. Shoal++ §1:
  *"dynamically re-interpret the anchor"*. Not membership.
- **Banyan** — "epoch synchronization" appears once, in related work about Jolteon/Ditto's
  asynchronous fallback. Not membership.
- **Cordial Miners** — §2 fixes `Π`; App. D's only membership-adjacent item is *shrinking* the
  effective set as equivocators are repelled, and even that is filed as future work.

**The adjacent line that does exist, and is not the same thing.** `awesome-consensus` names
**Slipstream** (Polyanskii et al., 2024) — *"Ebb-and-Flow Consensus on a DAG"*, with an optimistic
ordering *"live and secure in a **sleepy model** under up to 50% Byzantine nodes"* and a final
ordering safe under 33% — and **Tangle 2.0**, a *"stake- or reputation-based weight function"* over
a DAG. ⚠ **I read the abstracts only; those PDFs are not in `pdfs/`.** But the shape is clear and
the distinction matters:

> **Dynamic availability ≠ reconfiguration.** The sleepy/ebb-and-flow line lets participants be
> *offline and online* against a **fixed** identity set (or a stake distribution that is itself
> settled on-chain). Reconfiguration changes **who is in the set**. Slipstream does not tell us how
> to admit a member; it tells us how to stay live when members nap.

**What the absence implies for us — and it is not "we're on our own":**

1. **The reconfiguration mechanisms in DZ are protocol-shaped, not PBFT-shaped.** Configuration
   numbers, batch-boundary installation, learner phase, state-transfer-before-counting, verifiable
   configuration history, and the bounded-churn assumption are all statable over a blocklace. Only
   DZ mechanism (7) — view-change forwarding — is PBFT-specific, and it has a DAG analogue (§3.1).

2. **A DAG has one hazard PBFT does not, and it is ours.** In PBFT a configuration change happens
   *between* consensus instances at a sequence number. In a DAG, **the committee is an input to the
   ordering function itself** — round membership, the supermajority test in `ratifies`, wave-leader
   selection, and the cordiality admission check all read the roster. So a roster change does not
   merely partition the request stream; it **changes the function that computes the order of blocks
   that already exist.** Re-run `τ` after a roster change and you may get a different order for
   *the same blocklace*. Nothing in the DAG literature has had to face that, because nothing in the
   DAG literature changes the roster.

3. **This is the same shape as the τ deviation we already reproduced.** `CONSENSUS-FROM-SOURCE`
   §0's finding was: `τ` reads the **live lace** where CM reads the **anchor's fixed closure**, so a
   late arrival mutates already-emitted history. Roster-dependence is the same defect on a second
   axis: `τ` reads the **live roster** where it must read a **committed** one. The fix has the same
   shape too — pin the input to something the committed object determines.

### 3.1 What the DAG analogue of DZ's mechanisms looks like

Stated here as the literature-side observation; the design is in the companion doc §5.

| DZ mechanism | PBFT anchor | Blocklace anchor |
|---|---|---|
| configuration number `c` | in every message | in every **block** and every vote |
| install at batch boundary | `deliver(batch)` | install at a **wave boundary**, keyed to the anchor that ordered the `Join` |
| enhanced total order (`s` ⟹ `m` **and** `c`) | sequence number | **the roster is a function of the committed prefix**, so `τ` uses `c(prefix)` not `c(now)` |
| learner / temporary membership | `TM` set, quorum still over `M` | joiner authors and receives blocks, but is **not counted in supermajority tests** until installed |
| state transfer before counting | `2f+1` `HISTORY` msgs | joiner must hold the committed prefix up to the install point |
| configuration history `chist` | signed per-configuration certificate chain | genesis + the finalized membership blocks — **already a chain**, which is an advantage |
| view-change carries `c`, forwarded across gaps | Fig. 6 | a block whose `c` the receiver does not know must **buffer**, exactly like a dangling pointer (CM Alg. 3 line 49) |

The last row is the pleasant surprise: **a blocklace already has the buffering discipline that
DZ has to add by hand.** CM buffers a block until its pointers are all present; extending that to
"until its configuration is known" is the same mechanism, not a new one.

**And the corpus offers two mutually exclusive answers to *when the change takes effect*, both
sound, and we must pick one deliberately rather than drift into neither:**

- **(i) Lag it** — OG (`R`-slot epochs, stake from `ep−2`, `R ≥ 144Δ/βf`) and Rondo (install only on
  a commit certificate over the boundary block from `2t+1` of the **old** configuration). The lag is
  *derived from a settlement argument*, never chosen as a round number.
- **(ii) Anchor it and make laggards catch up retroactively** — Hammerhead. Zero lag, but you owe a
  **strong induction over the sequence of derived values, traversed without skips**, plus a
  quorum-intersection argument that a laggard's later commit forces it through the same sequence
  (Obs. 2 + Prop. 1).

What all three forbid is the same thing: **reading the live/subjective view.** Hammerhead names it
most directly — *"two validators might see a different subset of votes … we introduce a delay at the
calculation of the reputation score."*

---

## 4. Is "committee membership" the right frame at all?

Three separate answers, and they do not agree with each other. That disagreement is itself the
finding.

### 4.1 The grassroots line says permissioned ordering consensus is not grassroots — and offers an
### admission mechanism anyway, one layer up

`CONSENSUS-FROM-SOURCE` §4a established this and it survives re-reading: GS §2.1 names *"permissioned
consensus protocols with a predetermined set of participants such as Byzantine Atomic Broadcast [30,
16]"* as **interfering**, with `[16]` being Cordial Miners itself; and GS §2.1 files grassroots
consensus as *"a subject of future work."*

What that pass did not reach — **GA §3.6, *Grassroots Federated Assemblies*** — is directly on our
topic and says something we should sit with:

> A federation may include people and/or child federations, forms voluntarily and is governed by a
> small (say 100-member) assembly chosen by **sortition** from its individual members and the
> members of the assemblies of its child federations. **The assembly of a federation is sovereign to
> decide on the admission and removal of its members**, as well as on the application to join
> higher-level federations.

(GA cites Halpern, Procaccia, Shapiro, Talmon, *Federated Assemblies* [21] and *Grassroots Federated
Assemblies* [22], the latter "in preparation (2024)" — **neither is in `pdfs/`**; this is the
highest-value acquisition target from this pass.)

So the grassroots line *does* have an admission/removal doctrine: **a sovereign assembly decides,
and it decides removal as well as admission.** The shape of our design — existing members ratify a
candidate — is squarely inside it. Two observations follow:

- Our design is **not** a departure from the grassroots frame at the governance layer. It is a
  departure at the *consensus* layer, where the frame explicitly has nothing yet.
- GA names **removal** in the same breath as admission. A membership doctrine with admission and no
  removal is not the grassroots one; it is half of it.

And GA §3.6's Fig. 3 makes the structural point that our word "federation" is doing double duty:
in the grassroots sense a federation is *nested* — communities federate into larger federations, and
a member may belong to several. Our "federation" is one flat committee. Not wrong, but the word is
borrowed, and the borrowed thing has a shape we are not implementing.

### 4.2 The permissionless hierarchy places us — and LPR names our design and declines to call it
### permissionless

*(Section built on a delegated close read of LPR; see §6 provenance note. Quoted passages were
checked against the extracted text.)*

LPR's hierarchy is **four** settings, not three (LPR §1.2, Table 1), graded by how much the protocol
knows about current participants: **fully permissionless** (nothing; Bitcoin) · **dynamically
available** (a known identifier list, current participants a *subset*; Ouroboros) ·
**quasi-permissionless** (*every* identifier with a non-zero resource balance is active; Algorand) ·
**permissioned** (the list is *"fixed at the time of the protocol's deployment … with no dependence
on the protocol's execution"* — defined only informally, LPR §1.2 item 4).

The activity assumptions are the whole difference. Dynamically available (§7.1): *"if there exists
an honest player assigned a non-zero amount of stake … then **at least one** such player is active
at t."* Quasi-permissionless (§9.1): *"**every** honest player that is assigned a non-zero balance …
is active at t."*

The results, from LPR's own abstract:

> (1) In the fully permissionless setting … every deterministic protocol for Byzantine agreement has
> a non-terminating execution. (2) **In the dynamically available and partially synchronous setting,
> no protocol can solve the Byzantine agreement problem with high probability, even if there are no
> Byzantine players at all.** (3) In the quasi-permissionless and partially synchronous setting, by
> contrast, assuming a bound on the total size of the Byzantine players, there is a deterministic
> protocol solving state machine replication. (4) In the quasi-permissionless and synchronous
> setting, every proof-of-stake state machine replication protocol that uses only time-malleable
> cryptographic primitives is vulnerable to long-range attacks.

**Where we sit — and the answer is sharper and less flattering than "we're in (3)".** LPR model a
roster exactly like ours as a *protocol-defined resource* (§8.2, Appendix B, for Byzcoin/Hybrid
Consensus/Solida): *"a protocol-defined resource that allocates non-zero balance to the members of
the current committee (i.e., the committee members according to the most recently confirmed
block)."* But §8.3 then asks whether such a resource is **reactive** — roughly, whether the
environment or other players can *force* it to change — and answers for a roster the incumbents
alone control: no.

> a variant of that protocol could select a *single static committee* that is then tasked with
> carrying out state machine replication (e.g., using a PBFT-style permissioned protocol) for an
> unbounded duration. … **Can one call such a protocol '(quasi-)permissionless' with a straight
> face?**

**So: we are permissioned in LPR's sense, and that is a load-bearing good thing, not an
embarrassment.** Two consequences, and both matter:

1. **All of LPR's positive results are ours.** Thm. 9.1: partial synchrony, `ρ < 1/3`, a
   *deterministic* protocol that is `ρ`-resilient, `(1/3,1)`-accountable and optimistically
   responsive. Non-reactivity also **exempts us from LPR Thm. 11.1** — the result that kills
   stake-derived reactive membership at *every* `ρ > 0` in partial synchrony. §11 says so directly:
   without reactivity *"a protocol could include the (fixed) initial stake distribution as a
   (non-reactive) on-chain resource … [and] use the players allocated non-zero initial stake to
   carry out a permissioned state machine replication protocol such as PBFT."*

2. **The price is an activity assumption we must actually satisfy.** The quasi-permissionless
   assumption is that **every** honest roster member is active at every timeslot. On the other side
   of it sit Thms. 7.2/7.3/7.4 — and the accountability one is the killer. LPR §7.4: *"in the
   dynamically available, authenticated, and partially synchronous setting, no blockchain protocol
   can be `(ρ₁,ρ₂)`-accountable for **any** `ρ₁ > 0` and `ρ₂ ≥ 0`."* **Accountable finality is
   something we have *because* we are permissioned.** Any design that says "treat a silent member as
   absent and lower the threshold" trades it away for nothing.

### 4.2b LPR §15.3 — the one passage in the permissionless literature that is a reconfiguration rule

Inside the PoS-HotStuff construction proving Thm. 9.1, LPR must actually change the player set, and
they give an operational rule. **This is the single most transferable passage in the paper for us.**

> To deal with a changing player set, we divide the instructions into **epochs** and have the player
> set change with each epoch… To ensure that the player set changes only once with each epoch,
> blocks are confirmed **in batches**, with all blocks with heights in `(eN, eN+N]` confirmed at the
> same time. (§15.3)

The hazard they identify is *indirect* confirmation — a block confirmed by inheritance from a
descendant rather than by its own certificate:

> if a potentially epoch-ending block `B` at height `eN+N` receives only stage 1 and 2 QCs (say),
> which identifiers should be allowed to propose and vote on descendants of `B`? … another block
> `B′` at height `eN+N` might well also receive stage 1 and 2 QCs, **leading to conflicting opinions
> about the next epoch's player set**.

And the rule:

> allow the player set for epoch `e` to continue proposing and voting on blocks of heights greater
> than `eN+N` **until they produce a (directly or indirectly) confirmed block `B*` of height
> `eN+N`**. Once they do so, any blocks produced in epoch `e` with height `> eN+N` … are kept as
> part of the protocol's permanent history … crucially, **any transactions in these blocks are
> treated by the protocol as if they had never been included in any block**. The player set for
> epoch `e+1` treats `B*` as a genesis block for the epoch.

with the reason in fn. 51: *"the player set for epoch `e+1` may not have been present to implement
HotStuff's locking mechanism during epoch `e`"* — so the incoming set cannot safely inherit anything
the outgoing set had merely voted on, and a consistency violation follows if it does.

**Three things to take:** (a) the roster changes only at a **batch-confirmed** boundary; (b) work
past the boundary by the old set is retained as *history* but its transactions are **un-included**;
(c) the new set treats the boundary block as **its genesis**. And a fourth, from §9.2/§15.4: LPR's
quorum predicate is *"both player- and time-relative"* — a QC is defined **relative to the set of
transactions confirmed in previous epochs** (QC2, QC4). Neither LPR nor Pastro proves a constant
threshold *unsafe*; **neither uses one.**

### 4.2c Pastro — the consensus-free branch, and the vocabulary it gives us for free

Kuznetsov, Pignolet, Ponomarev, Tonkikh, *Permissionless and Asynchronous Asset Transfer* (DISC 2021
/ *Distributed Computing* 36(3), 2023) is the one asset-transfer paper with a real dynamic-membership
story. Its membership is *derived*: `members(C) = {p | ∃tx ∈ C. tx.τ(p) > 0}`,
`quorums(C) = {Q | Σ stake(q,C) > (2/3)M}` — *"a process joins the asset-transfer system as soon as
it gains a positive stake in a configuration and leaves once its stake turns zero"* (§4). Joining is
*receiving money*; there is no sponsor and no vote.

**We cannot use its mechanism** — consensus-freedom rests on per-account commutativity, and all
three asset-transfer papers state the boundary explicitly. QAAT §3 fn. 4: *"In systems where
accounts can have multiple owners, **total ordering is needed**, i.e., consensus or atomic
broadcast."* Pastro §7 files general smart contracts as an open hybrid; CryptoConcurrency §10 files
optimally-concurrent generic SMR as open. **A state machine is a maximally-shared account.**

**But its vocabulary is exactly what we lack**, and every item names a hazard we have:

- **installed / candidate / superseded / active** configurations (§6.1) — with the safety bound
  quantified over every **active candidate** configuration, not just the installed one. Ours has one
  word, "the committee", for all four states.
- **Configuration availability** (§6.1): `Σ_{q ∈ correct(C,t)} stake(q,C) > (2/3)M` for every active
  candidate `C` — and the release condition, *"the condition allows the adversary to compromise a
  candidate configuration once it is superseded."*
- **The slow-reader attack** and its defence: a **two-phase** operation whose second phase detects
  that the configuration moved underneath you, forcing a restart. (§5, crediting Kuznetsov & Tonkikh
  DISC 2020.)
- **Forward-secure signatures keyed by configuration height** (§5): *"before installing a new
  configuration, one should ask holders of `>2/3` of stake of the old one to upgrade their private
  keys and destroy the old ones"* — so a member that was correct in `C` but compromised or departed
  in `C′` **cannot deceive a peer still operating in `C`.** ⚑ This has no analogue in our design and
  is directly aimed at a member we vote *out*.
- **Unbounded configuration updates** (§2) — Pastro explicitly *"does not bound the number of
  configuration updates for the sake of liveness"*, unlike the earlier asynchronous-reconfiguration
  line, but §3 fn. 2 still requires *"the rate at which processes are added is not too high."*

### 4.3 So: is the frame the design error?

**No — but "committee" is doing two jobs and we should split them.** The committee is
simultaneously (a) *the quorum system* — the set whose supermajority makes a thing final, which must
be sharply defined, agreed, and changed by an explicit protocol; and (b) *the membership roll* — who
is in this federation socially, which is governance and which GA §3.6 says an assembly decides. DZ
separates exactly these: *"our syntax follows that of Schiper to separate dynamic BFT from its
membership service"* (DZ §III.G). We have fused them: one `MembershipAction` both admits a person
and moves the quorum denominator.

The frame error, if there is one, is not "permissioned". It is **fusing the governance decision with
the quorum-system reconfiguration and giving the fused thing one atomic step.**

---

## 5. The adjacent lines — and Rondo turns out to be the closest paper to our problem

*(This section rests on delegated close reads; see the provenance note in §6. Three of the four
titles are misleading about what the paper contains, which is why the section exists.)*

### 5.1 Rondo — the operational reconfiguration protocol, and it is Dyno on HotStuff

Rondo (Meng, Sui, Yang, Rong, Xu, Chen, Yan, **Duan**, 2024) is billed as a randomness beacon, and
the beacon is not the interesting part for us. **Rondo-BFT is Dyno's technique transplanted onto
HotStuff**, by one of Dyno's authors, and it is the most operationally detailed reconfiguration
protocol in the corpus. Rondo §I: *"Different from Dyno that can be viewed as a
reconfiguration-friendly version of PBFT, Rondo-BFT can be viewed as a reconfiguration-friendly
version of HotStuff."* It cites Dyno `[44]` for the configuration model and notation (§III), both
assumptions (§III), the four correctness properties (§III-A), the view-change forwarding technique
(§VII), state transfer (§VII), and for the motivating negative result (§II).

**The protocol, because this is the parts list we should be copying:**

1. **Membership requests are admitted only at an epoch boundary.** §V-A: *"they are only processed
   in the first round of every epoch in the agreement phase"*, and *"**To simplify our protocol and
   not waste the secrets shared by Breeze, we only support membership requests at the boundary of
   epochs.**"* Mechanically: block `b` may carry membership requests iff `b.height mod B = 1`.

2. **Temporary membership + immediate state transfer.** On seeing an `ADD`, each `P_i ∈ M_e` adds
   `P_ε` to its own `TM` and sends its local state to `P_ε` via a `catchup` message. Proposals go to
   `TM`, quorums are counted over `M_e`. (Fig. 9; Fig. 14 lines 13/20/24 all read *"from
   `⌈(2|M|+1)/3⌉` nodes **in M**"*.) Same shape as DZ §V.B.

3. **⚑ Install is gated on a certificate from the OLD configuration.** A node in `M_{e+1}` installs
   `M_{e+1}` only after receiving decide/commit for the epoch's **last** block (`height = eB`) from
   **`2t+1` nodes in `M_e`**, and then sets `cview ← v+1`. Rondo §IV states the purpose:

   > before any correct node installs a new configuration, it needs to collect a view-change
   > certificate `vc` signed by **at least `2t+1` nodes in the current configuration**. Accordingly,
   > more than `t+1` correct nodes in the previous configuration are aware of the new configuration.
   > Finally, **only one leader will be selected** once a view change occurs.

   The named hazard it closes (§IV): *"multiple nodes **from different configurations** may compete
   for becoming a new leader."*

4. **A drain rule for leavers, in two directions.** A node in `M_{e-1}` but not `M_e` *"waits until
   receiving the pre-commit message in epoch `e` **and** delivering all the blocks in epoch `e−1`
   before leaving the system"* (Fig. 14 line 16). And a node may not exit until it holds a
   `prepareQC` from an epoch `e′ > e` proving it is out (Thm. 13's proof).

5. **Cross-epoch safety is a lemma, not an assumption.** Lemma 4: two blocks with valid `prepareQC`s
   in the same view must be in the same epoch — the induction being that correct members of the old
   configuration will not vote for a lower epoch once installed. Lemma 5 extends to a branch.
   Theorem 10 is **enhanced total order** in Rondo's own words: *"If a correct node in epoch `e`
   delivers a request with sequence number `k`, and another correct node delivers `rq′` in epoch
   `e′` with the same sequence number, then **`e = e′` and `rq = rq′`.**"* — DZ §III.E, verbatim.

6. **The one-correct assumption.** §III: *"There exists at least one correct replica in `M_0` that
   never leaves the system."* It is load-bearing in Lemma 9 / Thm. 11 (liveness) / Thm. 13
   (agreement): the permanent member is the relay that forwards view-change messages *across*
   configurations. ⚑ **If we build a leave path, check whether our liveness argument secretly
   depends on the same thing.**

7. **No pause, no quiesce.** §VIII measures reconfiguration latency as *"only slightly longer than
   the average latency of generating beacon outputs"*, with no beacon gap. The cost is message
   complexity: *"`O(n)` message complexity in normal-case operation and `O(n²)` messages only during
   configuration changes and view changes."*

**Two honest limits.** Rondo states **no bound on batch size or churn rate** — Lemmas 4/5 quantify
over `M_e`/`M_{e+1}` as sets, so the shape admits an arbitrary batch, but §VIII only ever exercises
±1: *"we add/remove one node at a time."* And its liveness rests on (6).

**One transferable rule from the beacon half.** Rondo avoids a DKG by making every epoch's secrets
*fresh*, because *"The DKG setup, however, especially during system reconfiguration … can be
costly"* (§I). **Any per-configuration cryptographic setup is a reconfiguration tax, and the design
move is to eliminate the setup, not to optimise the reconfiguration.**

### 5.2 Ouroboros Genesis — a lag *discipline* in a model that is not ours, plus one primitive we need

OG's contribution: *"parties to safely join (or rejoin) the protocol execution using only the genesis
block information … without any additional advice—such as checkpoints"*.

**The lag structure, precisely.** During epoch `ep`, the stake distribution `S_ep` is *"the
distribution recorded in the ledger up to the last block of epoch **`ep − 2`**"*, and the epoch
randomness `η_ep` is derived from VRF values in *"the first **two thirds** of epoch `ep − 1`"*
(§3). The epoch splits into thirds and each third does a job (App. E): the first `R/3` guarantees
chain growth exceeding the common-prefix parameter, so *"after these slots, all alert players agree
on the stake distribution at the end of the previous epoch"*; the second `R/3` guarantees at least
one honest VRF value *determined after the stake distribution is fixed* (anti-grinding); the last
`R/3` lets everyone agree on the randomness. The epoch length is **derived**, not chosen:
`R ≥ 144Δ/βf`.

**Take:**

- **The lag is derived from a settlement argument.** Not a round number. Our analogue: waves between
  "join ratified" and "join effective" should be derived from "every honest validator's committed
  prefix contains the ratification", not picked.
- **Freeze the derived quantity before the entropy that consumes it.** If wave-leader selection ever
  becomes non-round-robin and randomised, the roster must be frozen strictly before that entropy.
- **⚑ Validate a candidate against ITS OWN declared configuration.** `IsValidChain` (App. B, Fig. 15)
  derives `S_C^ep` and `η_ep^C` **from the candidate chain `C` itself**, never from the validator's
  local distribution. This is the primitive that lets a node evaluate a block produced under a
  roster it has not installed, without either accepting blindly or rejecting it for being ahead. OG
  gets it free because *the chain is the configuration*. **We would have to add the field.**
- **`2s ≤ R/3` is the deepest form of the rule** (Thm. 2's proof): *"since `2s ≤ R/3`, the chains
  `C_loc` and `C_cand` use the same stake distribution and randomness to determine slot leaders for
  the interval."* The window over which you compare two candidates must itself fit inside the
  frozen-configuration region — otherwise you are comparing two objects evaluated under different
  configurations. That generalises past fork choice to **any cross-view comparison**.
- **`Delay` is unknowable to the party experiencing it.** §1: *"it is impossible for a party to
  determine whether it is already synchronized."* Remark 2: a rejoining party's stake *"has to be
  counted towards the adversarial stake even though the party is not formally corrupted"* until it
  holds its synchronising chain. **A newly-ratified validator cannot locally decide when it is
  safely caught up; the protocol must decide** (Rondo's `catchup` + install-on-commitQC).

**Refuse: the mechanism.** `maxvalid-bg` is a *fork-choice* rule and exists because in longest-chain
PoS the participant set is implicit and there is nothing better to measure than chain density. A
quorum-certificate system has *direct* evidence and needs no proxy; importing a density heuristic
would be strictly weaker than what we already have. (Note also: the word *"plenitude"* does not
appear in OG — the rule is described as local chain growth. And OG has **no membership operation at
all**; a party joins the *network*, not the *committee*.)

### 5.3 Hammerhead — leader schedule, not committee; but it is the DAG-native proof shape

Hammerhead (Tsimos, Kichidis, Sonnino, Kokoris-Kogias) is Bullshark-lineage DAG-BFT with **leader
reputation**. It swaps leader *slots* between the `f` lowest- and `f` highest-reputation validators.
Members of the demoted set remain full validators: their blocks stay in the DAG, their edges count
toward the `n−f` parent requirement, they count in every quorum. `n`, `f`, and `2f+1` never move.

**It does not treat validator-set change.** A full-text grep for `validator set`, `committee change`,
`reconfigur*`, `membership`, `epoch change`, `new validator`, `stake change` returns **zero hits**;
"epoch" means only *schedule epoch*. There is no punt to quote — the topic is absent. ⚠ Hammerhead
runs on Sui mainnet, and Sui *does* change its validator set at epoch boundaries, so the
schedule/committee interaction exists in production and is **outside this paper's model and proofs.**
Do not read Prop. 1 as covering a roster change; its induction quantifies over schedules derived
from a fixed `Π`.

**What it does give us is the determinism argument for a DAG-derived quantity, and it is exactly the
argument we need for a DAG-derived roster.** §3:

> when we commit a sub-dag in Bullshark this happens **through a subjective view of the DAG**. This
> means that two validators might see a **different subset of votes** … In order to resolve the
> first challenge **we introduce a delay at the calculation of the reputation score.** … **we
> calculate the reputation score up to but EXCLUDING the committed leader.**

with **Observation 2** — *"every honest party will (i) commit `u` and (ii) upon committing `u` will
have the SAME causal history for `u` in its DAG"* — and **Proposition 1 (Schedule Agreement)**:
*"if an honest validator `p_i` switches to schedule `S`, eventually every honest validator will
switch to schedule `S`"*, proved by strong induction over `S_0 → S_1 → …` plus quorum intersection.

**And Hammerhead makes the opposite choice from Genesis/Rondo on effect timing: no lag at all.** §3:
*"Once the `S′` is calculated, the new schedule takes effect immediately."* Laggards apply the
change **retroactively** (§3.1). What buys the immediacy is the induction: §3 says the schedules must
be traversed *"through an induction and **WITHOUT SKIPS**"*.

⚠ **Two prose/pseudocode discrepancies worth knowing before treating Alg. 2 as a spec**, both
reported by the reading lane and both sitting on our bug class: the prose says the score window
*excludes* the committed leader while `updateSchedule` (Alg. 2 line 39) says *"up to `v.round`"*
inclusive — which would read votes outside the certified prefix and be non-deterministic; and
`orderHistory` returns at a schedule switch without visibly discarding an anchor stack that was
built under the superseded schedule. The safety proofs rely on the prose reading.

### 5.4 Dynamic Probabilistic Reliable Broadcast — the "dynamic" is not membership

**Confirmed by the reading lane at source.** DPRB §3.1, immediately below Algorithm 1: *"we assume
the set of participants `Π` (`|Π| = n`) to be **static**: the set of processes remains the same
throughout the execution."* §8: *"**Future work** could further explore how this flexibility can be
leveraged by integrating dynamic membership mechanisms into the protocol."* The dynamism is
**witness sampling against an adaptive adversary**, and the internal thresholds are the classical
static `⌊(n+f)/2⌋+1`.

**But the paper contains one mechanism that is directly transferable, and it is the only construction
in the whole corpus that achieves safety under divergent views with *no version number on the
wire*.** The design is a two-radius containment: **accept** from the narrow witness set `W` (radius
`d₂`), but **send to** the wide potential-witness set `V` (radius `d₁`), with

> **Theorem 4 (Witness Inclusion).** As long as **`d₁ − d₂ ≥ 2λγ`**, for any pair of correct nodes
> `p_i` and `p_j`, and instance `(id, seq)`: `W_i(id,seq) ⊆ V_j(id,seq)`.

where `λγ` is literally the maximum drift between two correct nodes' local states (App. B bounds
the symmetric difference of their histories by `2λγ`). §1: *"we **do not need the processes to
perfectly agree** on the witnesses for any particular event … **a sufficient overlap is enough**."*
Unbounded drift falls back to Bracha's full `O(n²)` broadcast over the whole roster (§6/App. D).

**Its limit is exactly the thing we would want it for.** The theorem reasons only over the randomness
histories `R_i` vs `R_j`; the selection is over `j ∈ Π_i`. **If `Π_i ≠ Π_j` the inclusion fails
immediately for any node in `Π_i \ Π_j`, and no radius slack recovers it, because the failure is in
the index set rather than the metric.** And the paper does contain a mechanism that mutates `Π_i`
per node — App. A's `convicted ← convicted ∪ {id}` with *"correct processes can subsequently exclude
the misbehaving party from the system"*, unsynchronised and unanalysed; App. E.1 files *"a
reconfiguration mechanism that detects and evicts misbehaving users"* as open. ⚑ **That is our
`auto_evict_equivocator`, in a paper, unanalysed.** (The `Π_i`-divergence inference is the reading
lane's, checkable against Eq. 1 and the App. B proof; the paper does not state it.)

### 5.5 The three static BRB papers — confirmed static, and one reframing worth stealing

- **Locher, *BRB with Low Communication and Time Complexity*** — §2: *"The considered network
  comprises `n = 3t+1` nodes"*, with `k := 2t+1` baked into the erasure code. Membership appears
  once, in §6, as somebody else's problem, citing **DBRB (OPODIS 2020)** as ref. [16].
- **Albouy et al., *Near-Optimal Communication BRB under a Message Adversary*** — static `n`, **but
  it models churn as message loss**, and that reframing is the cheapest thing here to adopt. §1:
  *"This message adversary abstracts cases related to **silent churn**, where nodes may voluntarily
  or involuntarily disconnect from the network **without explicitly notifying other nodes**."*
  Assumption 2.1 is `n > 3t + 2d` and delivery power `ℓ = n − t − (1+ε)d`. **Cordial dissemination
  is best-effort, i.e. a `d > 0` regime whether or not we model it.**
- **Locher & Shoup, *MiniCast*** — `t < n/3`, zero hits for membership/churn/reconfiguration.
  Upgrades the *corruption* model to adaptive, not the *membership* model.

**And the cross-cutting complexity finding: reconfiguration silently invalidates in-flight encoded
state, not just setup.** All three index their erasure codes and Merkle/vector commitments by `n` —
MiniCast uses `(n, n−t)` and `(n, n−2t)` codes and an `n`-leaf tree; Locher uses `(n, 2t+1)`. **A
fragment or root computed under `n` is not decodable or verifiable under `n′`, and none of these
protocols can *detect* the mismatch, because `n` is an ambient constant rather than a field on the
wire.** That is the same defect class as our missing configuration number, arriving from a
completely different direction.

### 5.6 DBRB — the paper we do not have, and the design fork it represents

DZ §II describes it:

> Guerraoui et al. recently proposed **dynamic Byzantine reliable broadcast (DBRB)**, where replicas
> can join and leave the system dynamically [20]. … From the technical perspective, **DBRB allows
> divergent view paths that will eventually converge to the same view.**

**DBRB is in `pdfs/` — no. In `awesome-consensus` — no. Cited as *the* dynamic-membership BRB
reference by two of the three static BRB papers and by Pastro.** Full citation, as it appears:
Guerraoui, Komatović, Kuznetsov, Pignolet, Seredinschi, Tonkikh, *Dynamic Byzantine Reliable
Broadcast*, OPODIS 2020.

It is the top acquisition target, because *"divergent view paths that eventually converge"* is a
**materially different answer** from DZ's totally-ordered configuration history, at exactly our
layer. Choosing between them without reading it would be choosing blind. Note also the author
overlap: Kuznetsov wrote DBRB *and* DPRB, and in DPRB chose static `Π` deliberately.

---

## 6. Provenance — which claims I verified at source

Because a previous pass in this area asserted a negative from an incomplete corpus, here is the
ledger.

**Read in full text by me, claims quoted from the extracted PDF:**
`zot-foundations-of-dynamic-bft.pdf` (§§I–VIII, Figs. 4–8, App. B, App. C proofs C.1–C.9);
`zot-reconfigurable-heterogeneous-quorum-systems.pdf` (§§1–6, Defs. 1–11, Lemmas 20/24, Thms.
19/21/22, Alg. 1, Alg. 3); `cordial-miners-shapiro-2205.09174.pdf` App. D;
`grassroots-architecture-digital-democracy-2404.13468.pdf` §§3.2–3.6. The §3 negative (no DAG paper
treats reconfiguration) is my own grep-and-inspect over the six named DAG papers.
The §1.5 arithmetic is my derivation from DZ's inequality, instantiated on our `T(n)=⌊2n/3⌋+1`.

**Read by a delegated lane and integrated here:** LPR §§1.2, 2.1, 7–11, 15.3 and Pastro /
CryptoConcurrency / QAAT (§4.2–4.2c); Rondo, Ouroboros Genesis, Hammerhead (§5.1–5.3); DPRB and the
three static BRB papers (§5.4–5.5). I re-read LPR's abstract and DPRB's abstract directly. Where §§4.2–5
state a mechanism without a quotation, treat it as one remove from source.

⚠ **Two claims in §5 that I am flagging as *reported discrepancies*, not verified findings:** the
Hammerhead prose-vs-Alg. 2 off-by-one on the reputation window, and the DPRB `Π_i`-divergence
inference. Both are the reading lane's, both are checkable, neither is quoted from a paper's own
statement. If either becomes load-bearing for a design decision, verify it first.

**Abstract only, PDF not held:** Slipstream, Tangle 2.0 (§3).

**Named in the literature, not held, and worth acquiring — in priority order:**
1. **Guerraoui, Komatović, Kuznetsov, Pignolet, Seredinschi, Tonkikh, *Dynamic Byzantine Reliable
   Broadcast*, OPODIS 2020** (DZ ref. [20]; cited by Locher §6 ref. [16], by the near-optimal MBRB
   paper, and by Pastro ref. [14]) — the reconfiguration result at *our* layer, with a
   *divergent-then-convergent* view model that is a genuine alternative to DZ's.
2. **Kuznetsov & Tonkikh, *Asynchronous Reconfiguration with Byzantine Failures*, DISC 2020**
   (Pastro ref. [20]) — the source of the **slow-reader attack** and of the forward-secure-signature
   technique; Pastro's substrate.
3. **Abraham, Malkhi, Nayak, Ren, Spiegelman, *Solida: A blockchain protocol based on reconfigurable
   Byzantine consensus*, arXiv:1612.02916** (LPR ref. [3]) — the title is our question.
4. **Halpern, Procaccia, Shapiro, Talmon, *Federated Assemblies* / *Grassroots Federated
   Assemblies*** (GA refs. [21], [22]) — the grassroots line's own admission-and-removal doctrine.
5. **Aguilera et al., *DynaStore*** (DZ ref. [2]) and **Kuznetsov, Rieutord, Tucci Piergiovanni,
   *Reconfigurable lattice agreement and applications*, OPODIS 2019** (Pastro ref. [19]) —
   reconfiguration **without consensus**, the design fork we have not considered.
6. **Lorch et al., *SMART*** (DZ ref. [34]) and **Raft joint consensus** (DZ ref. [38]) — the two
   canonical answers to "run two configurations at once", which is the design we will otherwise
   reinvent.
7. **Frey, Gestin, Raynal, *The synchronization power (consensus number) of access-control objects:
   the case of allowlist and denylist*, DISC 2023** (QAAT ref. [22]) — literally "what is the
   consensus number of a membership list". ⚠ QAAT cites it only for an anonymity impossibility; the
   title is the lead, not a claim from its text.

---

## 7. Summary — what is settled, and by whom

| Question | Settled? | By what |
|---|---|---|
| Can a BFT committee grow safely? | **Yes** | DZ Thm. VI.1 (Dyno: agreement `V`, total order, liveness, consistent delivery under standard quorum); Rondo-BFT on HotStuff |
| What is the extra correctness property dynamic BFT needs? | **Yes** | DZ §III.E: **same-configuration delivery** / enhanced total order (`s` ⟹ `m` *and* `c`), plus consistent delivery. Restated as Rondo Thm. 10 |
| When may a new configuration be **installed**? | **Yes, and it is a certificate rule** | Rondo §IV / Fig. 9: only on a commit certificate over the boundary block from **`2t+1` of the OLD configuration**. LPR §15.3: only at a **batch-confirmed** boundary, with post-boundary transactions **un-included** (fn. 51) |
| Must a joiner wait before its vote counts? | **Yes, for safety** | DZ §V.B learner phase + §VI.A state transfer, used in the proof of Lemma C.9; Rondo `TM` + `catchup` |
| Must a leaver wait before it goes? | **Yes** | Rondo Fig. 14 line 16 drain rule + Thm. 13; DZ Dyno-C's `REMOVE`-delivery constraint |
| What bounds the churn? | **Yes** | DZ §III.D: `≥ Q_c` c-correct replicas persist into `c+1`; plus the cross-config intersection inequality (§1.5). Rondo adds a **one-correct-forever** assumption for liveness |
| Can membership change without a throughput stall? | **Yes** | DZ §VIII (Dyno vs Dyno-S vs BFT-SMaRt); Rondo §VIII (no beacon gap) |
| Can a stranger verify the current committee from genesis? | **Yes** | DZ §VI.B `chist`, Lemmas C.1–C.2; independently OG's bootstrap-from-genesis |
| Should a block be validated against **its own** declared configuration? | **Yes** | OG `IsValidChain` (App. B, Fig. 15) derives the config from the candidate chain, never from the local view |
| What can a reconfiguration protocol preserve? | **Yes, with impossibilities** | LL Thms. 21, 22 — pick your sacrifice; never sacrifice consistency |
| Is concurrent independent reconfiguration safe? | **No, and it forks** | LL §5 reconfiguration attack |
| Is Join or Leave the hard one? | **Leave** | LL §6 vs Lemma 24; DZ's `V₂` variants exist entirely to handle leavers; Pastro's forward-secure key rotation exists for departed-member deception |
| Should the quorum threshold be a constant? | **No paper proves it unsafe; no paper uses one** | LPR §9.2/§15.4 QCs are *"player- and time-relative"*; Pastro `quorums(C)`; DZ/Rondo `Q_c` per configuration |
| Which permissionless setting are we in? | **Permissioned, in LPR's sense** | LPR §8.3: a roster the incumbents alone control is a **non-reactive** protocol-defined resource. Buys Thm. 9.1 and exemption from Thm. 11.1; costs the every-honest-member-active assumption, and accountability is **impossible** on the other side of it (§7.4) |
| Can a derived quantity take effect with **zero** lag? | **Yes, at a price** | Hammerhead: immediate + retroactive, bought by a strong induction over schedules **traversed without skips** (Obs. 2, Prop. 1). The alternative is a derived lag (OG, Rondo) |
| Safety under **divergent views with no version on the wire**? | **Yes, for a metric-sampled quorum** | DPRB Thm. 4: `d₁ − d₂ ≥ 2λγ` — accept narrow, send wide, slack ≥ 2× max drift. ⚠ **cannot** absorb index-set (`Π_i`) divergence |
| Reconfiguration of a **DAG** protocol | **NOT SETTLED** | six DAG papers searched, §3; nearest neighbours (Slipstream, Tangle 2.0) are *dynamic availability*, a different problem; Hammerhead moves the schedule, not the roster |
| Reconfiguration where the **ordering function itself reads the roster** | **NOT SETTLED, and not posed** | §3 item 2 — this is our original problem |
| Dynamic membership at the **reliable-broadcast** layer | **SETTLED ELSEWHERE, not held** | DBRB (OPODIS 2020). Every BRB paper in `pdfs/` is static-`n` and cites it |
| Grassroots consensus with self-determined participants | **NOT SETTLED** | GS §2.1, *"a subject of future work"*. But GA §3.6 **does** give an assembly-level admission *and removal* doctrine |
