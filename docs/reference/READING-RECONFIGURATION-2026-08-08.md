# The install discipline: what the reconfiguration literature obliges, and what we would have to build

**Date:** 2026-08-08
**Method:** read-and-think over the reconfiguration cluster in `pdfs/`. **No protocol code changed.**
**Predecessors** (`5baa476a8`), which this doc builds on and **corrects in two places**:
`docs/reference/DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md` (what the papers settle) and
`docs/reference/FEDERATION-DESIGN-GAPS-2026-08-08.md` (what we have). Read their §0s first.

**The commissioning verdict this pass was asked to make actionable:** *"we built the join channel — a
reasonable invention — and skipped the install discipline, which is a solved problem."* That verdict
survives, and it is now sharper: **the install discipline is not merely solved, it is solved four
different ways, and three of the four never need the theorem we are missing.**

Citation shorthand. **DZ** = Duan & Zhang, *Foundations of Dynamic BFT* (S&P 2022). **DBRB** =
Guerraoui, Komatović, Kuznetsov, Pignolet, Seredinschi, Tonkikh, *Dynamic Byzantine Reliable
Broadcast* (OPODIS 2020, arXiv:2001.06271v2 technical report — **now in `pdfs/`**, it was the prior
pass's #1 acquisition target). **KT20** = Kuznetsov & Tonkikh, *Asynchronous Reconfiguration with
Byzantine Failures* (DISC 2020) — **also now held**, prior target #2. **SKM17** = Spiegelman, Keidar,
Malkhi, *Dynamic Reconfiguration: Abstraction and Optimal Asynchronous Solution* (DISC 2017).
**Gauss** = Clement, Crooks, Giridharan, Shamis, *It's not a lie if you don't get caught: simplifying
reconfiguration in SMR through dirty logs* (arXiv:2602.09441v2, Jul 2026). **Rondo** = Meng, Sui,
Yang, Rong, Xu, Chen, Yan, Duan (2024). **LL** = Li & Lesani, *Reconfigurable Heterogeneous Quorum
Systems*. **LPR** = Lewis-Pye & Roughgarden, *Permissionless Consensus*. **Lutris** = Blackshear et
al., *Sui Lutris* (CCS 2024). **Mysticeti** = Babel et al. (NDSS 2025). **CM** = *Cordial Miners*.

---

## 0. Two corrections, and they change the shape of the problem

### 0.1 ⚑ "No paper in this corpus treats reconfiguration of a DAG protocol" is **false**, and the paper that refutes it was already on the shelf

The predecessor defended that negative and named the six papers it grepped: DAG-Rider, Bullshark,
Shoal, Shoal++, Banyan, Cordial Miners. That list is accurate and those six really are silent. But
`pdfs/` holds two more DAG papers that were not in the list, and **both have a reconfiguration
section**:

- **Sui Lutris §4.2 *Committee Reconfiguration*** — a four-step protocol (Register / Ready /
  End-of-Epoch / Handover) with theorems. Its abstract claims it is *"the first to provably show the
  safe and efficient reconfiguration of a consensusless blockchain"*, and **Theorem 1 (Sui Lutris
  Safety)** is exactly the install-point obligation stated as a theorem: *"At the start of every
  epoch, all correct validators have the same state."* Proved by induction over epochs.
- **Mysticeti §IV-D *Epoch change and reconfiguration*** — the epoch-change bit, and an explicit
  quorum-intersection safety argument over the epoch's final commit.

⚑ **And Lutris is not a proposal — it is an operated protocol.** §1 and §6, verified at source: Sui
mainnet *"launched in May 2023, and has been operating continuously using the protocols described
here, **with no downtime for a year**, as of May 2024 … operated by **107 geo-distributed
heterogeneous validators** and processes over 3.1 million certificates a day … over **383 epochs
changes** using the Sui Lutris protocols."* And its consensus engine is a DAG-BFT of exactly our
lineage: §2.1, *"In our implementation, we specifically use the **Bullshark** protocol [38]"* — i.e.
one of the six papers the predecessor grepped and found silent. **The reconfiguration for Bullshark
exists; it is just not in the Bullshark paper**, and it has run 383 times in production.

**What I searched, so this negative-about-a-negative is itself falsifiable.** A full-text grep of
*every* PDF in `pdfs/` — not a title-selected subset — for
`reconfigur|epoch change|membership|validator set|committee`, with every hit inspected. That is how
Lutris §4.2 and Mysticeti §IV-D surfaced. Full search ledger in §8.

This is the same class of error the predecessor's own §0 named — *a negative claim inherits the shape
of the shelf it was drawn from* — committed one level down, against a **subset of the shelf**. The
generalisable lesson: when a negative is defended by "I grepped these six", the exposure is not the
grep, it is **the census that produced the six**. I do not know how that census was drawn, but the
observable fact is suggestive: the two DAG papers in `pdfs/` that were missed are the two whose titles
carry no hint that they contain a reconfiguration section, and both are in files named for their
*primary* subject (`sui-lutris-broadcast-and-consensus`, `mysticeti-uncertified-dags`). A
corpus-wide grep costs seconds and does not care what a paper is called.

**What survives is narrower, and far more useful than the false version.** Read the two papers
together with Rondo, LPR §15.3 and Gauss and one fact is uniform:

> ⚑ **In every reconfigurable protocol in this corpus, the roster is CONSTANT for the lifetime of a
> consensus instance.** Mysticeti: *"quorum-based blockchains typically operate in epochs, allowing
> validators to join and leave the system **at epoch boundaries**"*; the committee for epoch `e+1` is
> settled by a smart contract before the epoch closes. Lutris: registrations close at the `S`th
> checkpoint, *"This function establishes the **static** stake distribution for the next epoch."*
> Gauss: epoch `i+1` is a **different consensus instance** `C_{i+1}` with membership `M_{i+1}`. LPR
> §15.3: the new player set treats the boundary block *"as a genesis block for the epoch"*.

So "a DAG whose ordering function reads the roster while the roster moves" is **not an open research
frontier**. It is a shape nobody builds, and the literature's uniform answer to it is *don't*. That is
a much better position than "we are on our own": we are not missing a theorem, we are missing a
**boundary**. The theorem only becomes necessary if we insist on the design that everyone else
declines (§3.4).

Even DZ and Rondo, the two that *do* mutate a running instance's membership, pay for it with an
apparatus — configuration numbers on every message, view-change forwarding across configuration gaps,
a cross-configuration quorum-intersection lemma — that exists **solely** to survive that choice.

### 0.2 ⚑ DBRB does **not** have partially ordered configurations. The premise of the DBRB-vs-DZ question is wrong.

DZ §II characterises DBRB as *"DBRB allows divergent view paths that will eventually converge to the
same view."* Read alone, that sentence promises a partially-ordered configuration model. **The paper
proves the opposite.** From the DBRB technical report itself:

- §3.1: *"Our protocol ensures that all valid views are **comparable**."*
- **Lemma 25**: *"views that are installable in `s` form a **sequence of views**."*
- **Lemma 26**: for any two views `v, v′` in the current state, *"either `v ⊂ v′` or `v ⊃ v′`"*.
- **Lemma 27**: *"`s` is a sequence of views."*
- §A.2 summary: *"we proved (Lemma 26) that **all views in the current state of the system `s` are
  comparable** … Moreover, we showed that installable views in `s` form a sequence of views (Lemma
  25)."*

**Is Mysticeti's rule a THIRD answer?** It reads like one — *"A deterministic consensus commit `C`
sets the boundary between epochs `e` and `e+1`"* (§IV-D) — but it answers a different question, and
noticing that is what makes it usable. **DZ and DBRB answer *what shape the configuration history
has*; Mysticeti and Lutris answer *which object locates the install point*.** The two axes are
orthogonal, and Mysticeti's own sentence shows it presupposes the first: *"Guaranteeing reconfiguration
safety is straightforward in systems mandating consensus for all transactions, such as Mysticeti-C,
**owing to the total ordering property inherent in consensus** … This makes sure that all transactions
completed in epoch `e` are included in and come before commit `C`."* The commit *is* a point in the
total order; the configurations it separates are still a chain, indexed by commits.

⚑ **But on the axis it does answer, it is the best answer for us, and better than D3's certificate
framing on its own** — because it needs **no separate agreement**. Rondo's `2t+1`-of-`M_e`
view-change certificate, Gauss's `Done()` transactions and Lutris's End-of-Epoch messages are all
devices for manufacturing an agreed install position in a protocol that does not already produce one
at the right granularity. A blocklace does: a super-ratified final leader is exactly *"a deterministic
consensus commit"*, and it is an object we already compute. So the install position is a **function of
committed structure**, not a new round-trip — which is also why it is the one answer whose cost does
not grow with roster size.

What actually diverges in DBRB is the **proposal**, not the installation. Two members may `propose`
conflicting sequences; the algorithm merges them (Alg. 2 lines 44–47) and the *result* is a chain.
And processes may sit at **different points of the same chain** at the same instant — that is the
"divergent paths" DZ meant, and it is a statement about *who has installed what*, not about the shape
of the configuration history.

**KT20 states the same requirement as a property, and gives it the sharpest formalisation in the
cluster.** §3.3, *Reconfiguration Validity*: *"Every installed configuration `C` is a join of some set
of verifiable input configurations. Moreover, **all installed configurations are comparable**."*
§3.2, *BLA-Comparability*: *"All verifiable output values are comparable."* And §4 splits candidate
configurations into **pivotal** (*"the last configuration in some verifiable history"*) and
**tentative**: *"A nice property of pivotal configurations is that it is impossible to 'skip' one in
a verifiable history."* **That is the precise content of "divergent then convergent": tentative
configurations may be skipped by some processes; pivotal ones may not; and the whole history is a
chain.**

SKM17 says it a third way with the same shape: the algorithm *"will enforce a **containment order**
among activated configurations"* (§3), and property **S1 (Speculation)** requires that any
configuration a peer might have *skipped* is nevertheless carried in the speculation set so its state
can be transferred forward.

**The partially-ordered option exists, is named, and every paper here declines it.** DZ §II, on
group-communication models: *"In a partitionable one, **views are partially ordered**, i.e., multiple
disjoint views may exist at the same time. **The paper studies the primary partition model only.**"*
DBRB's own related work notes that even DynaStore, which *"implicitly generates a **graph** of views"*,
uses that graph only *"as a way of identifying a **sequence** of views in which clients need to
execute their r/w operations."* Nobody operates over the partial order. Everybody extracts a chain.

---

## 1. Q1 — What exactly must hold at an install point

### 1.1 The properties, verbatim, so they can be implemented rather than paraphrased

DZ §III.E adds two properties to static BFT's four:

> **Same configuration delivery.** *"If a correct replica `p_i` (resp. `p_j`) delivers `m` in
> configuration `c_i` (resp. `c_j`), then `c_i = c_j`."*
>
> **Enhanced total order** (their unification of same-configuration delivery with total order): *"If a
> correct replica in configuration `c` delivers a request `m` with a sequence number, and another
> correct replica in configuration `c′` delivers a request `m′` with the same sequence number, then
> `m = m′` **and `c = c′`**."*

DZ §III.G is worth knowing because it prices the property: Schiper's specification has total order and
same-configuration delivery *separately for regular and membership requests*, and DZ shows those four
properties together are **equivalent** to enhanced total order — while total order alone (without
same-configuration delivery) admits the anomaly of DZ Fig. 2, where `p₁` delivers the membership
request before a regular request and `p₂` delivers them the other way round. **That anomaly is exactly
what a roster-reading ordering function produces**, and it is why the property is not optional
bookkeeping.

DZ §III.E also works through two failed attempts at the client-facing property before landing on
**consistent delivery**; the reason the obvious one fails is a fact we should internalise, since it
also kills any "the leaver will just answer the last few requests" instinct:

> *"the perfect channel guarantees message delivery only when the sender is—all the time—correct, but
> the sender may leave the system in some future configurations."*

**Rondo restates enhanced total order as its Theorem 10 verbatim** (verified at source), so this is
not one paper's idiosyncrasy. And **Lutris §2.2 states the cross-epoch obligation in the form closest
to what we would want to prove**, because it quantifies over epochs in the property itself rather than
in a separate one:

> **Safety.** *"If two transactions `t` and `t′` are executed on correct validators, **in the same or
> different epochs**, and take the same inputs, then `t = t′`."*
> **Liveness.** *"All valid transactions sent by correct clients are eventually processed until final
> **(and their effects persist across epoch boundaries)**."*

### 1.2 The obligation list — minimum, and what is bought on top

Reading DZ, Rondo, DBRB, KT20, SKM17, Lutris and Gauss against each other, the obligations sort into
three tiers. **The first tier is not negotiable in any of the seven.**

**Tier 1 — required for safety by every construction in the cluster**

| # | Obligation | Where it is stated |
|---|---|---|
| **I1** | **Every delivery names a configuration**, and the naming is a function of the committed object, not of local time. | DZ §III.E same-configuration delivery; Rondo Thm. 10; DBRB associates *every* `prepare`/`ack`/`commit`/`deliver` with one specific view (§4.2) |
| **I2** | **Configurations are totally ordered.** Installed/activated ones form a chain by containment. | DBRB Lemmas 25–27; KT20 *Reconfiguration Validity*; SKM17 §3 containment order; DZ Lemma C.2 |
| **I3** | **A member of the new configuration does not act in it until it holds the state**, and the state comes from a *quorum* of the old one. | DZ §VI.A (`2f_c+1` `HISTORY`); Rondo `catchup` + `TM`; DBRB Alg. 3:66 (`wait for v.q state-update`); Lutris Step 2 `Ready`; Gauss `Ready()` |
| **I4** | **The install point is fixed by a certificate from the OLD configuration**, not by a local clock or a local tally. | Rondo §IV (`2t+1` of `M_e`); Lutris Step 4 (`2f+1` End-of-Epoch); Gauss (`f_i+1` `Done()`); DBRB Alg. 3:59 (`install` carries a quorum of signed `converged`); LPR §15.3 |
| **I5** | **Cross-configuration quorum intersection holds — or the design makes it unnecessary** by never letting two configurations share an instance. | DZ Lemma C.8 (holds it); Gauss / Lutris / LPR §15.3 / Mysticeti (avoid it) |
| **I6** | **A receiver that cannot yet evaluate a message's configuration buffers it**; it never reinterprets it under the local one. | DBRB §4.2 (`prepare`/`commit` are processed only when `v = cv`); DZ Fig. 6 (view-change forwarding both directions); CM Alg. 3:49 gives us the mechanism free |
| **I7** | **The boundary is straddle-free**: no unit of work is counted partly under `c` and partly under `c+1`. | DZ Fig. 5 `deliver(batch)`: reply to *all* regular requests, **then** `c ← c+1`, **then** apply ADD/REMOVE. See §5.2 |

**Tier 2 — required for liveness, and each is an assumption someone must own**

- **Bounded churn.** DZ §III.D: *"from configuration `c` to `c+1`, at least `Q_c` `c`-correct replicas
  are still in `c+1`."* DBRB Assumption 1 + Assumption 3. KT20 §3.3: the number of verifiable input
  configurations is finite in any infinite execution, and *"can be shown to be necessary"*.
- **A relay that spans the gap.** Rondo §III: *"There exists at least one correct replica in `M_0`
  that never leaves the system"* — load-bearing in Lemma 9 / Thm. 11 / Thm. 13. DZ Fig. 6 achieves the
  same effect with forwarding rather than an assumption.
- **Old configurations stay available until they EXPIRE, not until they are superseded.** SKM17
  Def. 1 *Availability*: *"The adversary can crash at most a minority of `C.membership` **between the
  time when `introduce(C)` occurs and until `C` is expired**."* This is the obligation people forget:
  a configuration that has been proposed but not activated is still load-bearing.
- **Genesis is known to everyone.** DZ §III.D; DBRB Assumption 2. ✅ we have this.

**Tier 3 — what Dyno adds for PERFORMANCE, and which is therefore optional**

DZ is explicit that the naive design works and is merely slow: Dyno-S, in which every membership
change forces a view change, produces *"a window of zero throughput"* (§VIII), and BFT-SMaRt's own
reconfiguration is measured dropping to zero for up to 50 s. Everything below buys that window back:

1. **The learner phase's *early start*.** The safety requirement is only "do not count before state
   transfer" (I3). Starting the transfer at *proposal* time rather than at install — DZ §V.B, Rondo
   Fig. 14 line "sends local state to `P_ε` via a `catchup` message" — is a latency optimisation.
2. **No view change on a membership change.** Dyno's whole §V.B–VI.A apparatus exists so the change
   rides the normal path.
3. **Configuration discovery variants** (DZ App. B lazy discovery, configuration master).
4. **Rondo's fresh-per-epoch secrets** instead of a re-run DKG (§I). The transferable rule: *any
   per-configuration cryptographic setup is a reconfiguration tax, and the move is to eliminate the
   setup rather than optimise the reconfiguration.*
5. **Gauss's `Ready()` round.** Gauss says so itself: *"Submitting `Ready()` messages to consensus
   increases latency for new configurations to become active, but is key to achieving **minimal
   downtime**."*

**A minimum-viable install discipline is therefore I1–I7 plus Tier 2, and it may quiesce.** We do not
have to earn Dyno's zero-stall property to be correct. Saying that plainly matters, because the
cheapest correct design is available and the expensive one is not a prerequisite.

---

## 2. Q2 — DBRB vs DZ for a partially-ordered log: the verdict

**Verdict: the question's premise does not hold, and the answer is neither "DBRB" nor "DZ" but a
distinction they both make and we have not.**

**The blocklace's partial order is a partial order over MESSAGES. Neither paper asks for a total order
over messages at the point where reconfiguration needs one — they ask for a total order over
CONFIGURATIONS.** Those are different objects at wildly different cardinalities: blocks arrive
continuously; configurations change tens of times over a system's life. DZ's totally-ordered `chist`
and DBRB's totally-ordered view sequence are the *same* requirement (§0.2), and satisfying it costs us
a chain of at most dozens of elements. **There is no impedance mismatch.** A blocklace already
produces a total order — τ — and the configuration chain is a function of it.

What genuinely differs between the two is **how the chain is reached**, and there DBRB is the better
fit, for one specific reason:

### 2.1 ⚑ The one mechanism to steal from DBRB: concurrent membership changes MERGE, they do not race

DBRB Alg. 2, lines 41–51. When a member receives a `propose` for a sequence that conflicts with its
own:

```
44:   ω  = most_recent(seq)
45:   ω′ = most_recent(SEQ_v)
46:   ▷ merge the last view from the local and q's proposal
47:   SEQ_v = LCSEQ_v ∪ {ω ∪ ω′}
```

**The union of the two most-recent views.** Two concurrent joins do not produce two competing
configurations one of which wins; they produce **one** configuration containing both. DBRB Lemma 10
then proves that any two sequences converged-on to replace the same view are comparable, because a
correct process that sent `converged` for `seq₁` can only ever send `converged` for a superset.

This is lattice agreement in the specific: KT20 makes it explicit (*"every installed configuration is
a **join** of some set of verifiable input configurations"*), and SKM17's `ChangeConfig(Proposal)`
returns a configuration `C ⊇ Proposal` for the same reason.

**Our design races.** `apply_if_passed` applies whichever proposal crosses threshold first; a second
proposal for the same candidate then hits `constitution.rs:117`'s
`if self.participants.contains(node_key) { return false; }` and becomes **passed-but-unapplied
forever** (FEDERATION §2.7). The merge rule dissolves that entire hazard class rather than patching
it: there is no "second proposal", there is one configuration that is the join of the pending changes.

It also dissolves the *reconfiguration attack* LL §5 describes — two nodes concurrently adopting
non-intersecting quorums — because a join of two change-sets cannot be incomparable with either.

### 2.2 The second thing to steal, and it is a constraint not a mechanism: DBRB's impossibility results

DBRB App. A.6 proves that **you cannot promise a departing member anything**:

> **Theorem 81 (Strong Validity Impossibility).** No algorithm can implement Strong Validity in `M`.
> **Theorem 82 (Strong Totality Impossibility).** No algorithm can implement Strong Totality in `M`.

where Strong Validity (Def. 79) is *"If a correct participant `s` broadcasts `m` at time `t`, then
every correct process **that is a participant at time `t`** eventually delivers `m`"* and Strong
Totality (Def. 80) covers *"every correct process `q` that did not leave the system before `t`"*. The
model `M` is **crash-only with at most one failure** — strictly weaker than ours — and the proofs are
two-run indistinguishability arguments.

**Consequence for our drain rule (FEDERATION §3.5).** A drain rule of the form "the leaver must
deliver everything that was delivered before it left" is **not implementable**. DBRB's own validity and
totality are weakened exactly to exclude leavers (*"if it is a participant at time `t′ ≥ t` and
**never leaves the system**"*). So the drain rule must be an obligation on the **remaining** system —
"the leaver may not stop serving until evidence `X` exists" (Rondo Fig. 14 line 16; DZ Dyno-C fn. 2) —
and never a promise to the leaver. SKM17 gives the clean statement of what the leaver *is* owed: an
operator *"can safely switch `s` off **immediately once** `ChangeConfig({−s})` **returns**"* (§3), i.e.
the protocol owes a **signal**, not a delivery guarantee.

### 2.3 Where DZ still wins, and it is not the ordering model

DZ's advantage over DBRB for us is that DBRB solves **broadcast**, not **consensus** — DZ says so
(§II) — and a blocklace under τ is a total-order primitive over shared state. Our state machine is a
maximally-shared account, so the consensus-free branch cannot carry the whole system (the predecessor
established this at §4.2c via QAAT §3 fn. 4). **But reconfiguration is not the state machine.** The
configuration chain is a small, monotone, join-semilattice-valued object, and the consensus-free
constructions are *exactly* the right tool for it. Using DBRB's merge for the configuration chain and
τ for the request stream is not a hybrid hack; it is what KT20 §3.4 calls decoupling a *reconfigurable*
object into a *dynamic* object plus an external history-builder.

---

## 3. Q3 — The intersection bound: verified, corrected, and generalised

### 3.1 The derivation is sound; the citation and the general rule both need fixing

**Confirmed.** The inequality `|Q_c ∩ Q_{c+1} ∩ M_c| ≥ T(n) + T(n+l) − l − n` is right: a `c+1`-quorum
has `T(n+l)` members of which at most `l` are joiners, so at least `T(n+l) − l` lie in `M_c`; a
`c`-quorum has `T(n)` members, all in `M_c`; inclusion–exclusion in a universe of size `n` gives the
bound. And **`4 → 7` really does break**: `T(4)+T(7)−3−4 = 3+5−3−4 = 1`.

**Three corrections.**

**(a) The arithmetic is DZ Lemma C.8, not C.9.** Lemma C.8 is the same-view cross-configuration lemma
and carries Cases (1)/(2)/(3) and the `2Q_c+1−(n_c+1)` computation. Lemma C.9 is the across-views
lemma and has no arithmetic. Verified against a `pdftotext -raw` extraction (the `-layout` extraction
interleaves the two columns and merges them).

**(b) ⚑ DZ's own stated bound on multi-join quorum growth is FALSE.** The prior pass flagged the text
as rendering ambiguously between `⌈l/3⌉` and `⌈2l/3⌉` and declined to rely on it. `-raw` resolves it:
the paper says **`⌈l/3⌉`** — *"For the case where multiple replicas join, `n_c` becomes `n_c + l` and
`Q_c` becomes `Q_c + q` where `0 ≤ q ≤ l` (concretely, `q` is bounded by `⌈l/3⌉`)."* With DZ's own
`Q_c = ⌈(n_c+f_c+1)/2⌉` and `f_c = ⌊(n_c−1)/3⌋` this is refuted by arithmetic: `Q(4)=3`, `Q(7)=5`, so
`l = 3 ⇒ q = 2 > ⌈3/3⌉ = 1`. The same violation occurs at `l ≥ 3` from every `n ≡ 1 (mod 3)`.
**The correct bound is `q ≤ ⌈2l/3⌉`**, which follows from the closed form
`Q(3a)=2a, Q(3a+1)=2a+1, Q(3a+2)=2a+2` (increments `+1,+1,0` repeating) and is tight at `l ≡ 0 (mod 3)`.
Nothing in DZ's proofs depends on the parenthetical; the inequality is the portable part, as the prior
pass correctly said. Recorded so nobody re-derives it or trusts the constant.

**(c) The Byzantine bound to compare against is `f` of the SMALLER configuration.** The intersecting
set lies in `M_c ∩ M_{c′}`; a member that behaves correctly in both cannot equivocate; so the bad set
is bounded by the Byzantine members of `M_c ∩ M_{c′}`, hence by `min(f_c, f_{c′}) = f(min(n_c, n_{c′}))`.
For **joins** that is `f_c` (the prior pass used `f_{c+1}`, which is conservative but not tight); for
**leaves** it is `f_{c′}`. This is also what DZ does — Case (1) concludes `≥ f_c + 1`, Case (2)
concludes `≥ f_{c′} + 1`.

### 3.2 Our threshold, placed

`T(n) = ⌊2n/3⌋ + 1` (`blocklace/src/ordering.rs:317`), whose own docblock already gives the
equivalent form `n − ⌊(n−1)/3⌋`. Two facts fall out:

- ⚑ **`T(n)` is exactly DBRB's quorum size.** DBRB §3.1: *"We choose the quorums to be all subsets of
  size `v.q = |v| − ⌊(|v|−1)/3⌋`."* Identical for every `n`. We independently reinvented the
  *dissemination* quorum of the consensus-free line.
- **`T(n) ≥ Q_DZ(n)`, strict exactly at `3 ∣ n`.** Since `T(n) = n − f(n)`, our quorum is never
  smaller than DZ's optimal one, so DZ's safety arguments apply *a fortiori*, and at `n ≡ 0 (mod 3)`
  we get slack DZ does not.

| n | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---|---|---|---|---|---|---|---|---|---|
| `T(n)` = DBRB `v.q` | 3 | 4 | **5** | 5 | 6 | **7** | 7 | 8 | **9** | 9 |
| DZ `Q_c` | 3 | 4 | **4** | 5 | 6 | **6** | 7 | 8 | **8** | 9 |

### 3.3 ⚑ The corrected rule: it is not "at most two", it is a function of `n mod 3` — and it happens to be two at our sizes

**Join condition:** `T(n) + T(n+l) − l − n ≥ f(n) + 1`.
**Leave condition:** `T(n) + T(n−l) − n ≥ f(n−l) + 1`.

Computed exhaustively (`scratchpad/bound.py`, ten lines, re-derivable in a minute):

| `n mod 3` | max joins per step | max leaves per step (contiguous) | example |
|---|---|---|---|
| **1** | **2** | **2** | `n = 4, 7, 10, 13` |
| 2 | 4 | 3 | `n = 5, 8, 11` |
| 0 | 6 | 4 | `n = 6, 9, 12` |

**So the prior pass's headline — "at most two installs per configuration step" — is CORRECT for our
roster shape and correct as a universally safe rule, but its justification was a loose asymptotic
(`2 > 2l/3`) that hid the `n mod 3` structure and understated what a 6- or 9-member federation can
do.** Both readings of `f` agree at `n ≡ 1 (mod 3)` (tight `f(n)` and conservative `f(n+l)` both give
`l ≤ 2` at `n = 4, 7, 10, 13`), so **the operating rule is robust to the ambiguity and the rule for us
is `l ≤ 2`.** We run at `n = 4`.

Instantiated for the sizes in play, with both readings shown:

| step | `T(n)` | `T(n′)` | intersection | needs (tight, `f(min)`) | needs (conservative) | safe? |
|---|---|---|---|---|---|---|
| 4 → 5 | 3 | 4 | 2 | 2 | 2 | ✅ |
| 4 → 6 | 3 | 5 | 2 | 2 | 2 | ✅ |
| **4 → 7** | 3 | 5 | **1** | **2** | **3** | ❌ |
| 7 → 8 | 5 | 6 | 3 | 3 | 3 | ✅ |
| 7 → 9 | 5 | 7 | 3 | 3 | 3 | ✅ |
| **7 → 10** | 5 | 7 | **2** | **3** | **4** | ❌ |
| 7 → 6 | 5 | 5 | 3 | 2 | — | ✅ |
| 7 → 5 | 5 | 4 | 2 | 2 | — | ✅ |
| **7 → 4** | 5 | 3 | **1** | **2** | — | ❌ |

⚠ **Two traps in the leave direction that a naive implementation will hit.**

1. **The safe-`l` set for leaves is NOT downward-or-upward closed.** At `n = 7` the condition passes
   for `l ∈ {1, 2, 4}` and *fails* at `l = 3`. `l = 4` "passes" only because the survivor set has
   `n = 3`, `f = 0` — it tolerates nothing, so the intersection requirement collapses. A `max_l`
   implementation that checks the endpoint rather than the whole prefix would admit a shrink that is
   only vacuously safe. **Enforce the contiguous prefix, and floor the roster at 4.**
2. **Leaves are the direction state transfer does not rescue** (§3.4).

### 3.4 ⚑ What state transfer buys — precisely, and it is less than "everything"

DZ Lemma C.8 Case (3), verbatim, is where the mechanism is load-bearing:

> *"If there exists a correct replica `p_i` in `Q_{c′} − f_{c′}` that is not in `S`, `p_i` must have
> joined the system in `c` … Before `p_i` participates in the protocol, it completes state transfer
> with `Q_c` replicas in configuration `c`, i.e., all delivered requests before the `⟨ADD,i⟩` request.
> If `p_i` delivers `m′`, it does not have `m` in the execution history. Thus, none of `Q_c` replicas
> has sent a valid prepare certificate for `m` during state transfer, a contradiction."*

Read carefully, state transfer performs a **substitution of arguments**, not a strengthening of the
bound:

- **Without it**, safety rests on *"the two quorums share a member that behaved correctly in both
  configurations"* — a counting argument, which is what the `l ≤ 2` ceiling prices.
- **With it**, safety rests on *"a new member's state is a function of a QUORUM of the old
  configuration, so it cannot certify anything that quorum had already certified against"* — which
  does not count at all, and therefore has **no `l` ceiling for joins**.

Three conditions on that substitution, each of which we would have to actually enforce:

- The transfer must be from a **quorum** (`Q_c` / `2f_c+1` `HISTORY` messages), not from one peer.
- The joiner must be **unable to act before it completes** — DZ's Fig. 5 puts the joiner in `TM` and
  computes `f_c`, `Q_c` from `M`, never `TM`. Rondo's Fig. 14 says it three times: *"from
  `⌈(2|M|+1)/3⌉` nodes **in M**"*.
- Readiness must be **protocol-decided**. OG §1: *"it is impossible for a party to determine whether
  it is already synchronized."* Lutris Step 2 gates on *a quorum of NEW validators* having called
  `Ready`; Gauss gates on **all** members of `M_{i+1}`.

**And it does nothing for leaves.** DZ Case (2) — `l` removals — contains no appeal to state transfer;
it is pure quorum intersection, and it cannot be otherwise, because there is no new member whose state
could be constrained. **So the churn bound is permanently a bound on DEPARTURES, and only temporarily a
bound on arrivals.** That asymmetry is the mirror image of LL §6's (*"The Join protocol is
straightforward"*, Leave needs total-order broadcast and a `tomb` set) and of DZ's own `V₂` variants
existing entirely to handle leavers.

### 3.5 The third answer, which the whole handover family gives: the bound is not needed at all

Gauss, Lutris, Mysticeti and LPR §15.3 never state a cross-configuration intersection lemma, because
**no two configurations ever run the same instance**. Gauss Theorem 1's proof is one paragraph: each
outer-log position corresponds to an inner-log position in exactly one epoch, each epoch's inner log is
agreed by that epoch's own consensus, and the sanitiser is deterministic. **If we adopt a handover
boundary, `l` is unbounded** — Gauss's stated goal 1 is *"It should be possible to replace any and all
participants from one configuration to the next."*

The price is §4.

### 3.6 The consensus-free line's own churn bound, which is the strongest statement in the cluster

KT20 §3.5, and this deserves to be quoted because it is the only place anyone prices *concurrency*
rather than *magnitude*:

> *"For reconfigurable objects we impose a slightly more conservative requirement: every combination
> of verifiable input configurations that is not yet superseded must be available … when `k`
> configurations are concurrently proposed, we require **all possible combinations, i.e., `2^k − 1`
> configurations, to be available.**"*

So in the merge-don't-race design (§2.1), the cost of `k` concurrent membership proposals is
exponential in `k` in the number of configurations that must remain live — and KT20's own mitigation
is that *"in practice, at most `k` of them will be chosen"*. **Concurrency in reconfiguration is
expensive in a way magnitude is not.** Rate-limit proposals; do not rate-limit batch size.

---

## 4. Q4 — The dirty-logs paper: what it simplifies, at what cost, and whether it reaches a DAG

### 4.1 Simplifies relative to *protocol-coupled* reconfiguration — that is the whole claim

Gauss §1: *"all existing reconfiguration algorithms today tightly couple the reconfiguration logic
with a single consensus protocol. There does not currently exist a clean way to update consensus."*
Its three goals are **arbitrary membership change**, **full modularity**, **minimal downtime**, and its
generality claim is that *"two epochs `i` and `i+1` can differ in their consensus protocol, membership,
**as well as failure thresholds**."*

The mechanism is two ideas stacked:

1. **Horizontal reconfiguration** (from Horizontal Paxos / SMART): epoch `i+1` is a **separate
   consensus instance**; the two run concurrently.
2. **The inner/outer log split** — the "lie". *"a transaction marked as committed in a consensus
   protocol's **inner log** need not necessarily be marked committed in the **outer log** exposed to
   other components, as long as the overall SMR properties are preserved."*

Three phases: **Prepare** (an `EpochChange()` transaction commits in `L_i` at position `K`; incoming
members sync and submit `Ready()` transactions **to `C_i`**) → **Handover** (when *all* `Ready()`s are
committed, at position `h`, every replica forms the *same* handover certificate; *"The log sanitizer of
`R(i,k)` simply ignores all transactions at positions `h′ > h` in `L_i` and does not submit them to
the outer log `O`. They will never appear committed to the overall SMR node."*) → **Shutdown** (`f_i+1`
`Done()` transactions in `C_{i+1}` make `i+1` fully active and let `i` wind down).

The key structural property that makes the truncation safe is stated plainly: *"By definition, all
replicas output the same inner log. They consequently all form the same handover certificate, and stop
processing the inner log of epoch `i` at the same position `h`."*

### 4.2 The cost, itemised

- ⚑ **Committed work is discarded.** Anything in `L_i` past `h` is un-included — *"a client resubmits
  `T5`"* in the worked example. This is only a "lie you don't get caught in" if **the inner log is
  never exposed**. Any component that reads the consensus output directly is a leak.
- **The `Ready()` gate is n-of-n on the incoming set.** *"If **all** `Ready()` transactions from
  members of epoch `i+1` appear committed in the log before a new epoch change transaction is
  observed"*. One unresponsive incoming member stalls the transition indefinitely; the only recovery
  is Case 2 preemption by a *later* `EpochChange()`, which is an operator action. (Lutris is strictly
  better here: Step 2's cutoff is *"when a **quorum** of new validators is ready"*.)
- **Two instances run concurrently**, and both memberships must be live.
- ⚑ **The paper proves safety only.** §4 opens *"short proof sketches describing how our
  reconfiguration engine Gauss preserves the SMR properties of safety **and liveness**"* and then
  states **exactly one theorem** — Theorem 1 (Safety). There is no liveness theorem and no
  liveness lemma. Given the n-of-n `Ready()` gate, that is the gap that matters.
- **Evaluation is thin**: a local testbed, four transitions (4→4, 4→7, 7→10, 10→13), ~430–438 ms each,
  with *"The Ready to Handover phase takes approximately 93% of the total epoch change latency"*, and
  *"We expect that this would further increase when we deploy the protocol in a geo-distributed
  setting."*

### 4.3 Does it apply to a DAG? Yes — and Sui Lutris is the same idea, three years earlier, with proofs

Gauss's own worked example is **Mysticeti → PBFT** (epoch `k` uses Mysticeti with `M_k = {R1..R4}`,
`f_k = 1`; epoch `k+1` uses PBFT with a disjoint `{R5..R8}`). The only thing Gauss needs from the
underlying protocol is a **committed total order** that every correct node computes identically — which
a DAG-BFT provides by construction.

And the four-step Lutris protocol is Gauss's three phases with better liveness properties, real
theorems, and 383 production executions **on a Bullshark DAG**:

| Gauss | Lutris §4.2 | note |
|---|---|---|
| `EpochChange()` at position `K` | Step 1 Register, closing at the `S`th checkpoint | Lutris freezes the *next* roster on-chain |
| `Ready()` from **all** of `M_{i+1}` | Step 2 Ready, cutoff at a **quorum** of new validators | strictly better |
| handover certificate at `h`; discard `> h` | Step 3 End-of-Epoch; Step 4 *"roll back the execution of any transaction that did not appear in any checkpoint"* | same "dirty log" move |
| `f_i+1` `Done()` | `2f+1` End-of-Epoch | Lutris is stricter |
| Theorem 1 (safety, sketch) | Theorem 1 + Theorem 2 + Lemma 15, plus Theorem 5 liveness | Lutris discharges what Gauss sketches |

Lutris also names the quiesce explicitly — at the cutoff *"the old committee stops signing new
transactions or locking objects"* — and Mysticeti generalises it into a block field, the
**epoch-change bit**, which disables the consensusless fast path near the boundary and closes the
epoch *"Upon committing blocks from `2f+1` validators with the epoch-change bit set via the consensus
path"*.

### 4.4 ⚑ The one hard conflict with our code

**Gauss and Lutris both require that a commit past the boundary be DROPPABLE. Our `attested` set is
sticky.** `node/src/finalization_votes.rs:412–419`:

> *"MONOTONE-SAFE across the boundary: blocks already consensus-attested under the old committee STAY
> attested (the `attested` set is sticky) … so there is no instant in which an unattested committee
> holds finalization authority."*

Those two rules cannot both hold. If we adopt a handover boundary, either stickiness goes, or the
sticky set becomes the **outer** log and τ's raw output becomes the **inner** one — in which case that
docstring's no-gap argument is about the wrong object, on top of the separately-recorded problem that
`EpochReconfig.lean::epoch_handoff_no_gap` models `federation/src/epoch.rs`, which has no production
callers (FEDERATION §2.2). **Decide the boundary design before touching either.**

---

## 5. Q5 — Threshold as a function of the roster

### 5.1 What ours is, and what it is not

`T(n) = ⌊2n/3⌋+1` **is** a function of the roster's cardinality; what it is not is a function of a
*configuration*. `VoteCollector` holds **one** `committee` and **one** `quorum_threshold`
(`node/src/finalization_votes.rs:248,255`), not indexed by block, height or epoch, and `reconfigure`
(`:420–430`) overwrites both. So the tally is against whatever is live when `record` runs. That is the
defect; the formula is fine.

### 5.2 What the literature uses, and the only real question it settles

| construction | threshold | indexed by |
|---|---|---|
| ours | `⌊2n/3⌋+1 = n − ⌊(n−1)/3⌋` | *nothing* — one live scalar |
| **DBRB** §3.1 | `v.q = |v| − ⌊(|v|−1)/3⌋` — **identical to ours** | the **view** `v` carried in every message |
| DZ §III.D | `Q_c = ⌈(n_c+f_c+1)/2⌉` | the **configuration** `c` |
| Rondo Fig. 14 | `⌈(2|M|+1)/3⌉` over `M`, never `TM` | the **epoch** `e` |
| Gauss §2 | `f_i` an explicit per-epoch parameter, changeable independently of membership | the **epoch** `i` |
| Pastro §4 | `quorums(C) = {Q : Σ stake(q,C) > (2/3)M}` | the **configuration** `C`, stake-weighted |
| LPR §9.2/§15.4 | QCs *"player- and time-relative"*, defined relative to transactions confirmed in previous epochs | the **epoch** |
| LL §3 | declared per process; ours is LL's degenerate cardinality/DQS case | the **process** |

**Every one of them indexes it. None of them uses an unindexed one.** So the answer to "what should
the threshold be" is: **the formula stays; the binding changes.** `T` becomes `T(c)`, a value of the
configuration object, carried in the vote's signed preimage, and a vote is counted against the
configuration it names or not at all.

**One extra finding on the formula itself, which forecloses a plausible wrong move.** Ladelsky &
Friedman, *On Quorum Sizes in DAG-Based BFT Protocols* (arXiv:2504.08048 — ⚠ **abstract only, PDF not
held**) find that *"DAG-Rider's correctness is maintained with `2f+1` nodes, [but] the asynchronous
versions of both Tusk and Bullshark inherently depend on having `3f+1` nodes, regardless of
equivocation."* **The quorum a DAG protocol needs is a property of its commit rule, not a universal
constant.** So the threshold is not independently tunable: whatever we set, it is the commit rule
(CM's *"more than two-thirds"*) that fixes what is admissible, and changing one without re-deriving
the other is unsound. Anyone proposing to move the threshold owes a re-derivation of the τ commit
argument, not just an arithmetic check.

### 5.3 ⚑ What breaks for in-flight blocks — and the three known answers, none of which is ours

The measured hazard: a block at 3-of-4 — already a quorum — loses that status when a join moves the
threshold to 4, and nodes applying the transition at different points of their poll cycle disagree
about whether it is attested.

**Answer 1 — DZ: make the boundary straddle-free, so nothing is in flight.** DZ Fig. 5, `deliver(batch)`:

```
func deliver(batch)
    for m = ⟨SUBMIT,c′,⟨REQUEST,cid,o⟩⟩ in batch: reply(m)     ← ALL regular requests first
    if there are membership requests: c ← c + 1                 ← THEN install
    for ⟨ADD,j,m⟩  in batch: M ← M ∪ p_j                        ← THEN apply
    for ⟨REMOVE,j,m⟩ in batch: M ← M − p_j
```

The install is a *point in the committed order* with no unit of work straddling it. This is the
cheapest of the three answers and the one that fits our substrate best: a wave boundary is already
such a point. Note what DZ accepts as the price — `M` grows at delivery so `Q` grows *immediately*,
while the joiner cannot vote until state transfer completes, so for a window the system needs a larger
quorum from *fewer able voters*. That liveness cost is exactly what the bounded-churn assumption
(*"at least `Q_c` `c`-correct replicas are still in `c+1`"*) exists to cover.

**Answer 2 — the handover family: quiesce, then truncate.** Lutris (*"the old committee stops signing
new transactions"*), Mysticeti (the epoch-change bit), Gauss (`h`), LPR §15.3 (post-boundary
transactions *"treated by the protocol as if they had never been included in any block"*). Costs
downtime and un-inclusion; buys unbounded `l` and protocol replacement.

**Answer 3 — Hammerhead: apply immediately, retroactively.** Costs the strong induction over derived
values *"traversed without skips"*, and Hammerhead only ever moves leader *slots*, never membership,
over a fixed `Π`. Still the design fork the predecessor flagged as ember's call (FEDERATION §3.2).

**⚑ What is not an answer, and is what we do: keep the old verdict sticky while the new threshold
governs new votes.** That is a *third* rule, authorised by neither configuration. Its concrete
failure: a block that crossed 3-of-4 stays attested in memory on a node that was running, and is
below the new threshold of 4 for a node that restarts and reassembles from persisted votes —
`assembled_quorum` (`:485–520`) drops any voter missing from the *current* `pq_committee` and then
requires `>= self.quorum_threshold`, so it returns `None`. **One node has it final, another cannot
reconstruct that it ever was.** The stickiness is not a mitigation; it is a second source of truth.

### 5.4 Should the threshold depend on *who*, not just *how many*?

Only weakly supported, and it carries a debt. LL Def. 9's **quorum inclusion** — every quorum should
include a quorum of each of its members — *"trivially holds for homogeneous quorum systems where every
quorum is uniformly a quorum of all its members"* (LL §1). It is free for us **because** we are
cardinality-based. Any per-node weighting or trust declaration makes it a proof obligation, and LL
Thms. 21/22 then force an explicit choice of which property to sacrifice. **Recommendation: keep
cardinality until someone is willing to own the inclusion proof.** The `AmendThreshold` proposal
variant, which is dead from the wire (FEDERATION §2.12), should be deleted rather than left as a
loaded gun.

---

## 6. A concrete install discipline

Ordered by dependency. **D0 first** — everything else is unstatable without it. Each item names what
must be *proved*, because a design with an unstated proof obligation ships without one.

### D0 (prerequisite, already designed) — a configuration identity derived from the committed past

Exactly FEDERATION §3.1: `config_seq` on blocks and inside the `FinalizationVote` signed preimage,
derived from the block's own causal past (OG's `IsValidChain` discipline), with buffering for blocks
whose configuration cannot yet be derived, and **refusal** — never reinterpretation — on disagreement.
Do not re-derive it here. Two things this pass adds to it:

- The identity should be the **change-set**, not just a counter: DBRB's `v.changes`, SKM17's
  `C ⊆ Changes`, KT20's configuration lattice. A counter cannot express D2's merge; a change-set can,
  and containment gives comparability for free.
- Tracking **removals explicitly** matters — SKM17 §3: *"Tracking excluded servers in addition to the
  configuration's membership is important in order to reconcile configurations suggested by different
  clients."*

*Prove:* derivability (`config_seq(b)` is a function of `[b]`), buffer termination, refusal totality.

### D1 — the configuration history is a CHAIN, and that is a theorem to state

Installed configurations are totally ordered by containment. This is not a design choice we are making
against the grain of a partially-ordered substrate; it is the invariant DBRB (Lemmas 25–27), KT20
(*Reconfiguration Validity*) and SKM17 (containment order) all prove, and the partial-order
alternative (the partitionable model) is declined by every paper in the cluster.

*Prove:* comparability of installed configurations. In a blocklace this should be nearly free — it is
a property of a fold over the committed order — which is itself the argument that D0 must land first.

### D2 — ⚑ merge, do not race

A configuration transition takes the **join** of the pending change-set, not the first proposal to
cross threshold. DBRB Alg. 2:47 (`SEQ_v = LCSEQ_v ∪ {ω ∪ ω′}`); KT20 (*"a join of some set of
verifiable input configurations"*); SKM17 D1 (Validity: `D ⊇ P`, and no spurious changes).

Deletes the duplicate-sponsorship hazard (FEDERATION §2.7) and the dead
`PendingJoinRequest.proposed` field rather than repairing them, and forecloses LL §5's reconfiguration
attack structurally.

*Prove:* validity in SKM17's two parts — the result contains every proposed change, and contains no
change nobody proposed. The second half is the access-control obligation: KT20's `VerifyInputConfig`,
which exists *"to prevent Byzantine clients from reconfiguring the system in an undesirable way or
simply flooding the system with excessively frequent reconfiguration requests"* — the answer to
`auto_approve_joins` reactivity (FEDERATION §2.8) in the reconfiguration literature's own vocabulary.

### D3 — the install point is a COMMIT, and the commit is the certificate

FEDERATION §3.2's rule, now with four independent confirmations at source and one simplification.
Rondo §IV (`2t+1` of the **old** configuration over the epoch's last block); Lutris Step 4 (`2f+1`
End-of-Epoch); Gauss (`f_i+1` `Done()`) — and **Mysticeti §IV-D**, which needs none of those:
*"A deterministic consensus commit `C` sets the boundary between epochs `e` and `e+1`."*

⚑ **Take Mysticeti's form, not Rondo's.** The other three manufacture an agreed install position with
an extra round of messages because their protocols do not already produce one at the right
granularity. Ours does: in CM's vocabulary a **super-ratified final leader is that deterministic
commit**, we already compute it, and using it means the install position is a *function of committed
structure* rather than the output of a second agreement (§2.3). Nothing new goes on the wire but D0's
identity.

⚑ **Precondition — an append-only floor over the committed order.** "The commit sets the boundary" is
only meaningful if a commit cannot be retracted. Every DAG-BFT implementation carries such a floor
(`decidedWave` / `committedRound` / truncate-at-first-undecided) and **ours does not** — which means
today the object D3 wants to hang the boundary on is not yet irretractable. **The floor is a
prerequisite of D3, not an optimisation of it**, and it should land with D0.

⚠ Do not confuse that floor with the stickiness in §4.4. They are different objects and only one is
sound: a monotone floor over the **order** makes "committed" mean something (a prefix that never
changes); a sticky per-block **verdict** under a moving threshold is a second source of truth about a
single block, which is the defect. Adding the floor is the thing that would let us *remove* the
stickiness rather than needing it.

*Prove:* install agreement (every honest node installs at the same position in the order); no-gap;
and floor monotonicity — that the committed prefix is append-only, which is the property "commit"
must have before it can carry a boundary.

### D4 — a learner phase with a protocol-decided readiness certificate

Ratified ⇒ `Temporary`; receives everything, may author blocks, **is not counted in any supermajority
test**, threshold stays `T(c)`. Readiness is proved by **authoring a block whose causal past contains
the install anchor** — checkable by anyone against the closure, no new message type, and cheaper than
DZ's `2f_c+1 HISTORY` because the evidence is already a first-class object.

⚑ Note against a plausible shortcut: the transfer must be from a **quorum** of the old configuration
(§3.4). A single-peer catch-up does not license relaxing D5's bound.

*Prove:* readiness soundness (a member that authored such a block holds every committed turn up to the
install point); joiner liveness.

### D5 — the churn bound, and when each half may be relaxed

- **Now, both directions: `l ≤ 2` changes per configuration step, and never below 4 members.**
  Enforce the *contiguous prefix*, not an endpoint check (§3.3 trap 1).
- **Joins may be unbounded once D4 is ENFORCED** — not merely present. The substitution in §3.4
  requires that a temporary member cannot act, which is a property of the code, not of a docstring.
- ⚑ **Leaves stay bounded permanently** under a mutate-the-instance design. Nothing in DZ Case (2)
  appeals to state transfer and nothing can.
- **Rate-limit CONCURRENT proposals, not batch size** (KT20's `2^k − 1`, §3.6). Concurrency is the
  expensive axis.

*Prove:* `T(n) + T(n′) − |Δ| − min(n,n′) > f(min(n,n′))` for the permitted `Δ` — a Lean `theorem` over
the actual `supermajority_threshold`, quantified over `n`, **not** a `#guard` over the six rows of the
table in §3.3.

### D6 — the boundary discipline for in-flight work: pick ONE, and say which

The three answers are §5.3. **Recommendation: Answer 1 (DZ's straddle-free batch).** It costs no
downtime, no truncation and no second consensus instance; a wave boundary already is the point it
needs; and it composes with D3 rather than replacing it. The install ordering is: *order everything in
the wave → apply its effects → THEN install → the next wave runs under `c+1`.*

⚑ **If Answer 2 (handover/truncate) is chosen instead, `attested` stickiness must go** (§4.4) — and it
is the answer to pick if we ever want to change the *protocol*, not just the roster, which Gauss is
right that we eventually will.

*Prove:* no unit of work is counted under two configurations — i.e. enhanced total order (DZ §III.E),
which is the property this whole document is about.

### D7 — leave with a drain rule, stated as an obligation on the SURVIVORS

The leaver may not stop serving until it holds evidence it is out of a **later** configuration (Rondo
Fig. 14 line 16: *"waits until receiving the pre-commit message in epoch `e` **and** delivering all the
blocks in epoch `e−1`"*; DZ Dyno-C fn. 2). **And it must never be phrased as a guarantee to the
leaver** — DBRB Thms. 81/82 prove that unimplementable even for one crash fault (§2.2). What the leaver
is owed is SKM17's **signal**: the operator may switch it off the moment the removal returns.

State the liveness assumption out loud. Rondo's rests on *"at least one correct replica in `M_0` that
never leaves the system"*. Either adopt it and write it down, or prove liveness without it. ⚑ Do not
discover it at `n = 1`.

### D8 — eviction, and the general criterion it fails

FEDERATION §3.4 stands (`MembershipAction::Evict`, ordered and on-chain, zero approval votes because
the proof is self-certifying, `auto_evict_equivocator` **deleted**). Two additions.

**A supporting citation.** DPRB App. A's unsynchronised `convicted ← convicted ∪ {id}` is the same
mechanism, and DPRB App. E.1 files *"a reconfiguration mechanism that detects and evicts misbehaving
users"* as an **open question**. Ours is that open question, wired to production.

⚑ **And the criterion that decides it in one line, without appeal to any paper.** A live read may
decide **whether** you emit, never **what** you emit; and no verdict in the family may be retracted.
`auto_evict_equivocator` fails both clauses in both of its fields:

- `participants` feeds the leader schedule (`ordering.rs:290`), so a live read of it changes **what**
  τ emits, not whether.
- `threshold` feeds the ratification test, so the same.
- and the verdict is **retracted on restart**, because `committee_replay::derive_from_lace` folds only
  `Payload::MembershipVote` blocks and an auto-evict leaves no trace in the lace.

This is the same defect as the ordering one wearing a second hat, and stating it as a criterion rather
than as a list of five consequences is what makes it checkable against the *next* live read somebody
adds. Every field the install discipline introduces — `config_seq`, the per-configuration threshold,
the floor — must be tested against it before it goes in.

---

## 7. Where the literature does not decide

Stated plainly, and separated from "we did not read it".

1. **How far a committee may move in one step, in general.** DZ makes bounded churn an *assumption*
   and never derives a constant; the one constant it offers (`q ≤ ⌈l/3⌉`) is arithmetically false
   (§3.1b). Rondo states no bound at all and only ever exercises `±1` (§VIII: *"we add/remove one node
   at a time"*). DBRB Assumption 1 bounds the *total* number of requests, not the batch. **§3.3 is our
   derivation for our threshold, not a quotation.** It is checkable in a minute and I would rather it
   be checked than believed.
2. **Whether a DAG whose ordering function reads the LIVE roster can reconfigure at all.** Not
   because it is hard — because **nobody builds one** (§0.1). Reconfiguring a DAG is settled and
   operated: Lutris has done it 383 times on Bullshark with no downtime for a year. What is unstudied
   is the variant where the roster moves *inside* an instance, and the reason is that it is a design
   error rather than a frontier. If we keep it we owe the theorem ourselves; the cheaper move is to
   stop having the problem.
3. **The interaction of a leader schedule with a roster change.** Hammerhead proves schedule agreement
   over a fixed `Π`; Sui changes its validator set at epoch boundaries in production and Hammerhead
   runs on Sui, so the interaction exists in the field and is **outside that paper's model and
   proofs**. Nobody has written it down.
4. **Liveness of the modular handover design.** Gauss claims it in §4's preamble and proves only
   safety (§4.2). Lutris proves liveness for *its* protocol (Thm. 5) but not for a protocol-swapping
   generalisation.
5. **Whether the merge rule (D2) and the certificate-gated install (D3) compose.** DBRB merges but has
   no total-order consensus underneath; DZ/Rondo have consensus but do not merge — they order. The
   composition is ours to check and I did not find it stated anywhere.

---

## 8. Provenance

**Read at source by me, in full or in the named sections, from `pdftotext` extractions; every quotation
above checked against the extracted text.**

- `dbrb-dynamic-byzantine-reliable-broadcast-2001.06271.pdf` — §§1–6, Algs. 1–5, App. A.1–A.2
  (Defs. 3–8, Lemmas 9–32, Properties 1–3), App. A.6 (Defs. 79–80, Thms. 81–82).
- `zot-foundations-of-dynamic-bft.pdf` — §§II–VI, Figs. 4–6, Table I, App. C Lemmas C.7–C.9,
  Thms. C.2–C.4. ⚑ **The `-layout` extraction interleaves the two columns; the Lemma C.8 arithmetic is
  only legible under `pdftotext -raw`.** That is how the `⌈l/3⌉` ambiguity the prior pass flagged was
  resolved, and how the C.8-vs-C.9 mis-citation surfaced.
- `dirty-logs-reconfiguration-smr-2602.09441.pdf` — complete (§§1–7, Thm. 1, Fig. 2, evaluation).
- `async-reconfiguration-byzantine-failures-disc2020.pdf` (KT20) — §§1–4, the BLA properties, the
  reconfigurable/dynamic-object properties, §3.5 quorum assumptions, §4 pivotal/tentative.
- `dynamic-reconfiguration-optimal-async-disc2017.pdf` (SKM17) — §§1–4, Def. 1, properties D1/D2/S1/A1.
- `zot-rondo-…​.pdf` — §§IV, V-A, VII and Fig. 9/14 normal-case pseudocode, **re-verified at source**
  (the predecessor's Rondo section rested on a delegated lane; every Rondo claim repeated here is now
  first-hand). One nit: Rondo's prose says the install gate is `2t+1` **decide** messages, its Fig. 9
  pseudocode says **commit** messages; nothing here depends on which.
- `sui-lutris-broadcast-and-consensus-2310.18042.pdf` — §§1, 2.1, 2.2, 4.2, 6, and §5 Thms. 1/2/5,
  Lemmas 15/16. The production figures (383 epoch changes, 107 validators, no downtime for a year as
  of May 2024) and the Bullshark-as-consensus-engine claim are quoted from §1/§6 and §2.1, checked
  verbatim rather than relayed.
- `mysticeti-uncertified-dags-2310.14821.pdf` — §IV-D.
- `blocklace/src/ordering.rs:290–319`, `blocklace/src/constitution.rs:776–778`,
  `node/src/finalization_votes.rs:240–262, 405–435, 485–520` — read at source for §5.

**Computed, not quoted:** the §3.2/§3.3 tables and the `n mod 3` rule. Script at
`scratchpad/bound.py`, ten lines; the refutation of DZ's `⌈l/3⌉` is one line of it.

**Relied on the predecessors without re-verifying:** LL (Thms. 19/21/22, Lemmas 20/24), LPR (§§8.3,
9.1, 15.3, Thms. 9.1/11.1), OG, Pastro, DPRB, Hammerhead, the static-BRB trio. Where this document
cites them it is repeating `DYNAMIC-COMMITTEE-LITERATURE-2026-08-08.md`, which flags its own delegated
sections.

**Abstract only, PDF not held:** Ladelsky & Friedman, *On Quorum Sizes in DAG-Based BFT Protocols*
(arXiv:2504.08048), fetched 2026-08-08.

**Searched, to make §7's negatives falsifiable.** `scripts/lit-search.py` (Kagi), 2026-08-08, five
queries: *partially ordered configurations reconfiguration partitionable group communication
Byzantine* · *reconfiguration of DAG-based BFT consensus validator set epoch change* · *concurrent
membership changes lattice agreement configuration join semilattice Byzantine* · *bound on number of
replicas added per reconfiguration step quorum intersection churn rate BFT* · *leader election schedule
depends on validator set reconfiguration DAG determinism*. Plus a full-text grep of every PDF in
`pdfs/` for `reconfigur|epoch change|membership|validator set|committee`, which is how Lutris §4.2 and
Mysticeti §IV-D surfaced — **that grep is what the prior pass's six-paper census should have been.**

**Named by that search, not held, in priority order:**

1. **EbbFlow: *Non-blocking join synchronization in dynamic asynchronous BFT*** (Computer Networks,
   2026) — the abstract snippet begins *"Dynamic membership raises two concrete difficulties in
   asynchronous BFT. First, BKR-style protocols fix the fault thresh[old]…"*, which is Q5 verbatim.
2. **Robust and Automated Reconfiguration of Byzantine Wide-Area Replication** (arXiv:2606.16740,
   2026) — *"we identify three vulnerabilities in this process that Byzantine nodes can exploit"*, a
   five-step deterministic protocol. An adversarial reading of a reconfiguration protocol is exactly
   what we would want before shipping one.
3. **Ladelsky & Friedman** (above) — the full PDF, for §5.2's commit-rule-vs-quorum point.
4. Still outstanding from the predecessor's list and still worth having: **Halpern, Procaccia, Shapiro,
   Talmon, *Federated Assemblies*** (the grassroots line's own admission-and-removal doctrine) and
   **Aguilera et al., *DynaStore*** (the graph-of-views original that DBRB's related work summarises).
