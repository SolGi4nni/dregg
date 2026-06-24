# Consensus Grounding — Phase 2.1, grounded in two 2024 papers

*Brings two papers into the Titanium Phase 2.1 (the consensus long pole). They are read, not
cited-from-memory: Sridhar–Tas–Neu–Zindros–Tse, "Consensus Under Adversary Majority Done Right"
(arXiv 2411.01689, Nov 2024) and Wong–Kolegov–Mikushin, "Beyond the Whitepaper: Where BFT Consensus
Protocols Meet Reality" (zkSecurity/Matter Labs, Aug 2024). This note says exactly what we take from
each and how it reshapes the consensus fibre of the fibration (`B = Topology × FaultModel ×
CryptoStrength`).*

---

## 1 · Sridhar et al. — separate the resilience, and the *client model* is a base coordinate

**The single contribution that changes our framing:** the folklore "resilience" of a protocol — the
max adversary fraction under which it is *both* safe *and* live — is `min(t^S, t^L)`, and that min
**throws away the structure that matters**. Sridhar et al. separate:

- **safety resilience `t^S`** — max adversary-validator fraction under which *safety* (no two honest
  parties finalize conflicting states) holds;
- **liveness resilience `t^L`** — max fraction under which *liveness* (the protocol keeps making
  progress) holds.

The impact of losing safety (a fork, double-spend) and losing liveness (stall, can't get paid) on a
client is **different**, so a single number is the wrong security measure. dregg should state **both**,
separately, for its real deployment — never a single `f < n/3`.

**The culprit behind "99% vs 51%" confusion is the *client model*, not the network.** Both Dolev–Strong
(99%) and Nakamoto (49%) are *synchronous*; what differs is what clients are assumed to be. Two binary
client axes (plus a validator axis and a network axis) give a **16-model space**, each with a tight
achievable `(t^S, t^L)` pair (their Fig. 1):

| axis | values | what it means for dregg |
|---|---|---|
| **validator sleepiness** | always-on / **sleepy** | a phone validator is intermittent ⇒ dregg validators are *sleepy* |
| **client sleepiness** | always-on / **sleepy** | "your phone is a node / a merchant during business hours" ⇒ dregg clients are *sleepy* |
| **client interactivity** | silent / **communicating** | dregg clients gossip (Plumtree) ⇒ *communicating*, not silent |
| **network** | synchrony / **partial-synchrony** | dregg targets *partial-synchrony* (GST) |

Key facts we use:
- **Nakamoto** = sleepy-*silent* clients = 49% (`t^S = t^L = 1/2`); it does **not** benefit from being
  always-on in synchrony (Thms. 1–2).
- **Dolev–Strong** = always-on-*communicating* clients = 99% (`t^S = t^L` near 1).
- **The new middle result we want:** for **sleepy *communicating*** clients (their Fig. 1g, Thm. 4),
  one can achieve `t^S = 99%` and `t^L = 49%` *simultaneously* — an **asymmetric** resilience pair
  that strictly dominates Nakamoto's symmetric 49/49. There is also a dual protocol (Thm. 5) with
  `t^S = 49%, t^L = 99%`. So the *communicating* upgrade to sleepy clients buys real, asymmetric
  resilience that *silence* cannot.

**Design consequence for dregg (the actionable insight):** dregg's clients are *sleepy* (phones) and
*communicating* (gossip). That is exactly the regime where the **asymmetric pair is the right target**:
**prove a high safety resilience and a separately-stated, lower liveness resilience** — do **not**
collapse to one `f < n/3` number. Concretely, the blocklace's "a client only needs to *listen* to a
quorum it can verify offline" should be leveraged into a *high* `t^S`; liveness (DAG progress post-GST)
is the weaker, separately-bounded `t^L`. State both. This is the honest, fine-grained guarantee.

**Where this lands in the fibration:** the `FaultModel` coordinate of `B` is **refined** into Sridhar's
4-dimension model space `(validatorSleepiness, clientSleepiness, clientInteractivity, network)`. dregg's
real deployment is one point — `(sleepy, sleepy, communicating, partial-sync)` — and the consensus fibre
over it carries a **pair** `(t^S, t^L)`, not a scalar. The Hasse diagram (their Fig. 2) of "model X is
easier than Y" is literally a sub-order of our base `B`; `lift` reindexing *down* that order is the
reindexing of the resilience pair. (This is the first concrete instance of `FaultModel` having real
internal structure, not just `honest / f<n/3 Byzantine`.)

---

## 2 · Wong et al. — the failure taxonomy = our adversarial negative-tooth checklist

Wong et al.'s thesis: BFT protocols are safe *on paper* and break *in translation* — "left as an
exercise for the reader" gaps between whitepaper and code. Every formal-verification effort that only
proves the happy-path theorem misses exactly these. So we adopt their taxonomy as the **explicit list
of negative teeth** the dregg consensus formalization must exhibit (a proof is not "both directions"
until each applicable attack is *shown rejected* on a witnessing instance — vacuity discipline §9b).

| # | Wong failure class | dregg exposure | the negative tooth Phase 2.1 must carry |
|---|---|---|---|
| **3.1** | **f+1 attacks / slashing** — f+1 colluding validators = a "51%" fork; `n=3f+1` vs `n=5f+1` round/resilience tradeoff; slashing is fragile (accidental slashing, "token toxicity") | dregg picks a quorum rule; an f+1 coalition must not silently fork | `equivocation_excluded` — a double-signing validator's two conflicting blocks are *both in the blocklace* ⇒ self-incriminating evidence ⇒ excludable; and the quorum-intersection bound that makes f+1 the real threshold, *stated as `t^S`* |
| **3.2** | **reconfiguration / long-range** — validator-set churn; old keys → posterior corruption / costless simulation; "the elephant in the room" | dregg has cell-owner key rotation + emergent (non-fixed) validator groups ⇒ **directly exposed** | a finality rule pinned to an **authenticated, monotone** checkpoint so a rewrite from retired keys cannot re-anchor history (`no_conflicting_finalized_state` must survive key-set change, not just fixed-set) |
| **3.6** | **view synchronization / consecutive bad leaders** — chained/pipelined BFT liveness attacks via leader election | dregg is **leaderless** (blocklace DAG) ⇒ **sidesteps this entire class** | record it as an *architectural* advantage: no leader ⇒ no view-sync bug surface. (Prove liveness without a leader-election sub-protocol.) |
| **4.1** | **(distributed) DoS** — proving is expensive, junk is cheap | dregg's per-turn STARK proving is the asymmetry | ties to Phase 2.5 economics: `fee ≥ marginal junk cost`; a spam tooth |
| — | **weighted-BFT quorum exactness** — weighted-stake quorum off-by-one bugs | if dregg ever weights by stake/reputation | keep quorum **counting** (not weighted) for now; if weighted, prove the exact `2t+1`-by-weight intersection |
| — | **DAG-based (Narwhal/Bullshark)** — the closest cousins to our blocklace | dregg's Cordial-Miners *is* a DAG protocol | reuse their safety structure (cert ranks / quorum intersection, Wong Fig. 2 HotStuff-2 proof shape) for `cordial_agreement` |

**The one positive Wong hands us:** their §3.2 closes with *"user-based consensus could become
practical if augmented with **zero-knowledge proofs** to allow nodes to avoid having to re-execute
everything."* That is **exactly** dregg's recursive-proof light-client (Titanium 4.2, Silver→Gold):
a phone verifies `(head, state-query)` from one recursive STARK instead of re-running the chain. Wong
names it as the missing piece for safe user-based checkpoints against long-range attacks; dregg is
*building the thing they say is missing*. This is the strongest validation of the Gold vision in the
literature — call it out in the light-client soundness theorem.

---

## 3 · What Phase 2.1 must now prove (reshaped by the two papers)

The seam already exists: `Dregg2/Exec/ConsensusExec.lean` (finalized-order → executor,
`no_conflicting_finalized_state`, `tampered_order_diverges`) over the Cordial-Miners core
(`Proof.CordialMiners`, `cordial_agreement`). The papers reshape the *targets*:

1. **State a resilience PAIR, not a scalar.** Replace any implicit "safe-and-live at `f < n/3`" with
   an explicit `safetyResilience` and `livenessResilience` over the blocklace quorum model, in the
   dregg deployment point `(sleepy validators, sleepy communicating clients, partial-sync)`. Target the
   **asymmetric** shape (high `t^S`, separately-bounded `t^L`) Sridhar shows is optimal for sleepy
   communicating clients. Both as theorems; the gap between them is a *feature*, stated, not hidden.
2. **Equivocation-exclusion as a real theorem + tooth** (Wong 3.1). A cell-owner signing two
   conflicting turns leaves both in the blocklace ⇒ excludable evidence; prove it, and prove the
   *negative*: a single honest finalization cannot be forked by f+1 below `t^S`.
3. **Reconfiguration-safe finality** (Wong 3.2). The finality/checkpoint anchor must be authenticated
   and monotone across validator-set change, so retired keys cannot re-anchor (`no_conflicting_finalized_state`
   under key churn). This is the long-range tooth.
4. **Post-GST liveness without a leader** (Wong 3.6 sidestep). Prove progress from the DAG structure,
   recording leaderlessness as why the view-sync attack class is empty for dregg.
5. **Light-client soundness ties to Gold** (Wong 3.2 ZK note). The recursive proof that lets a sleepy
   client verify without re-execution is the *named* defense against long-range; state it as such.

**Fibration placement:** `FaultModel` gains internal structure = Sridhar's 4-dim model space; the
consensus fibre carries `(t^S, t^L)`; `lift` reindexes the pair down the model order (Sridhar Fig. 2 is
the order); the negative teeth are the Wong taxonomy instantiated at dregg's base point. Consensus stops
being "a scalar `f < n/3` we assert" and becomes "a *pair* we prove, with the real-world attack classes
each shown excluded."

---

## 4 · Honest scope / what we are NOT claiming

- We are **not** re-deriving Sridhar's 16-model characterization in Lean. We **adopt** its framing
  (separate `t^S`/`t^L`; client model as a base coordinate) and prove the *one* point that is dregg.
- The `tau` intra-segment linearization (`OPEN-CM-XSORT`) is still a carried open in `ConsensusExec`.
- Economic security / slashing (Wong 3.1's incentive half) is Phase 2.5, not 2.1 — named, deferred.
- Wong is an *experience* paper (no theorems); we take its taxonomy as a **test checklist**, not as
  cited lemmas. The teeth are ours to prove.
