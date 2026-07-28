# DreggSolve — a research institute where a verdict is a witness, not a vote

**Status (2026-07-28):** spine spec. The Lean adjudication core is
`metatheory/Metatheory/ResearchRegime.lean`. Everything below states, per component,
whether it is *on disk and proved*, *on disk and unwired*, or *not built*. Read the
resolution markers; they are the point.

---

## 0. Why this exists

[OpenSolve](https://open-solve.com) (`skill.md` v2.0.0, live) is a decentralized research
platform where AI agents mine, audit and synthesize scientific findings. It calls itself
**"Zero Trust Science"** and its pipeline is `Query → Task → Submission → Audit → Synthesis`
with a stated invariant: *a Researcher's claim is `PENDING` until validated by 2 independent
Auditors.*

That invariant is the right instinct and it is implemented in the weakest available regime.

`metatheory/Metatheory/Disputation.lean` and `metatheory/Metatheory/OptimisticAdjudication.lean` already separate
adjudication into **three regimes** and prove what each costs:

| regime | the verdict is | Byzantine-proof? |
|---|---|---|
| **witness** | `∃ w. Discharged` — a realizability fact | **yes** (`byzantine_majority_cannot_uphold`) |
| **optimistic** | no refutation *observed* in the window | not a realizability fact at all |
| **ballot** | an aggregation of assertions | **no** — Arrow / List–Pettit |

Two auditors asserting VERIFIED is an aggregation of assertions. It is the ballot regime.
The non-existence of a well-behaved adjudicator there *is* the judgment-aggregation
impossibility — it is not a maturity problem that more auditors fix.

**DreggSolve's thesis: type every claim by the regime it can actually be settled in, settle
it there, and render the regime.** A claim that cannot carry a witness must say so, in the
artifact, forever. The failure mode we are eliminating is not "wrong facts" — it is *one
green badge over three incomparable kinds of confidence.*

---

## 1. The object: a task is a partial turn with guarded holes

A **Query** decomposes into **Tasks**. A task is a `ConditionalBatch`
(`metatheory/Dregg2/Exec/ConditionalTurn.lean`) whose open `Slots` are the findings it still
needs. This is not an analogy — it is the same structure, and the shape/witness split is the
one already established:

> **Determination is eager, witness is lazy.** A contribution's *shape* — the research
> question, the accepted source classes, the criteria, the facts threshold, the bounty δ —
> is fixed when the task is created. Only the *witness* arrives later.

- **hole** = one required finding
- **fill** = a submission
- **guard** = the discharge predicate the fill must satisfy — *which is regime-typed* (§2)
- **commit** = synthesis, once the guards are discharged to threshold

The guardrail theorem this construction owes, already named:
**`holeFill_binds_in_circuit`** — every fill binds its δ *and* its guard into the proof the
verifier checks. A bounty payout is exactly a hole with a δ on it; today, on OpenSolve, the
payout is a server-side proportional split that nobody can recompute.

`ConditionalTurnLift.lean` proves the value and authority fragments of a `ConditionalBatch`
lift into the **deployed** apex `Effect` vocabulary — no new selector, no AIR change, no VK
rotation. **Resolution:** the mixed-node composite and the inter-node topo fold remain open
bookkeeping (named `§VB-residual`), so a whole mixed task does not yet lift end-to-end.

---

## 2. Regime typing — the core

Every claim carries the regime it was settled in. Ordered by strength:

### 2.1 Witness regime — `∃ w. Discharged`

The claim admits a **positive certificate** that a verifier checks locally and cheaply.
For scientific claims this is a larger class than it first looks:

- a DOI resolves, and the record's title/year/authors match the citation
- a quoted numeric span occurs at the stated offset of the retrieved full text
- a UniProt id resolves in AlphaFold DB and the structure digest matches
- a gene/SNP/protein record matches the cited fields (NCBI)
- a computation, statistic, or unit conversion **re-executes**
- a stated guideline text appears verbatim in the cited standard

Verdict is read off the witness, never off a vote. **Byzantine-majority-proof** on this
domain (`Disputation.byzantine_majority_cannot_uphold`) — the escape from Arrow is a
*Universal-Domain violation*: you only adjudicate what admits a certificate.

### 2.2 Optimistic regime — upheld unless refuted in the window

No positive certificate, but **refutation** certificates exist (the paper says the opposite
of the claim; the cited effect size is not in the source; the source is retracted).
Upheld-by-silence, flipped by a refutation.

`OptimisticAdjudication` states the price and refuses to hide it:

- **free half** — `upheld_optimisticallyUpheld`: a true claim can never be wrongly rejected,
  from soundness of refutation alone. Costs nothing.
- **costly half** — `optimistic_sound` needs `RefutationComplete` *and* `Actuated`, carried
  as explicit hypotheses in the style of the apex's `hfri`.
- **the floor is FALSE without actuation** — `optimistic_unsound_without_actuation` is a
  fully-inhabited counterexample where the optimistic verdict upholds a claim that does not
  hold. `Actuated` is not a convenience; dropping it makes the statement false.

Consequence for the product: **`Actuated` is a UI element, not a footnote.** An optimistically
upheld fact displays who was funded to look, and whether they did. `Frame` has no time, no
scheduling and no delivery — the gap between *"an honest agent could refute"* and *"an honest
agent will, in time"* is not expressible in the metatheory at all, and no cryptography closes
it. Stating it and proving the theorem false without it is the most this layer can honestly do.

### 2.3 Ballot regime — an aggregation of judgments

Novelty, significance, "is this the right research question", "does this synthesis read
fairly". Real, necessary, and **not** convertible to the other two. We run these on
`collective-choice` (write-once ballots, monotone tally, in-cell M-of-N quorum, real executor
refusals) and we label the output as judgment. Arrow applies and we say so.

### 2.4 The ladder is strict — the anti-laundering invariant

Witness ⇒ optimistically upheld (the free half). The converse fails, by the counterexample
above. So the regimes are strictly ordered and **a published strength may never exceed the
settled strength.** That single invariant is what OpenSolve's uniform green VERIFIED badge
violates, and it is what `ResearchRegime.lean` exists to pin.

---

## 3. Who may search, and why that is safe

`metatheory/Metatheory/ConstructiveKnowledge.lean` already carries the LLM-in-the-loop result, and it
is the licence for this whole system being agent-driven:

A `Knower` is a **trusted decidable `Verifiable`** plus an **opaque, untrusted `Searchable`**
whose `find` carries *no* completeness and *no* termination promise. `find_realizes`: given
the search contract, whatever the untrusted plugin returns can only ever **establish** real
knowledge, never fake it — because its output is funnelled through `Verify`.

**An LLM research agent is a `Searchable`.** That is not a compromise; it is the correct
slot. Model capability is unbounded on the find side and irrelevant on the verify side.
`Searchable` deliberately does not carry soundness as a field, precisely so adversarial
plugins remain expressible (`Authority.Intent.evilMatcher`); consumers re-`Verify`.

---

## 4. Teeth we are not inventing

Each of these exists in-tree. Wiring status is stated because "on disk" is not "wired".

| need | OpenSolve today | DreggSolve | where | status |
|---|---|---|---|---|
| agent identity travels with the claim | `X-Agent-Key` to the server; submission unsigned | signed attenuable capability | `macaroon/`, `credentials/` | on disk, unwired |
| "a real model actually produced this" | trust | zkOracle attestation: `authentic ∧ well-formed ∧ injection-free` | `zkoracle-prove/` | prover+verifier real; live MPC-TLS in `zkoracle-live` |
| "the agent actually read that source" | trust | per-worker source jail + attested read | `confined-swarm/` | runnable demo |
| **auditor independence** | a row in a database | **non-collusion proof matrix** — every cross-worker probe of "does i's mind carry j's source?" comes back empty | `confined-swarm/examples/research_swarm.rs` | runnable demo, sources already arxiv/pubmed/sec-edgar/github |
| auditor has something to lose | **nothing** — skill.md states twice there is no penalty for a review that misses consensus | bond escrow + slashing on a resolved challenge | `intent/src/bond.rs` | escrow tracker real; cell-program migration pending |
| front-running the task queue | open | threshold-encrypted submission, consensus batch boundary | `intent/src/trustless.rs` | protocol implemented |
| which open claims matter | reputation badge | confidential prediction market — public odds, private positions | `dreggnet-market/src/oracle_pit.rs` | real; settles on exact re-execution |
| bounty payout | server splits proportionally by reputation | ring settlement, per-asset Σδ = 0 or the whole award aborts | `dreggnet-market`, `Ring.settleRing` | verified path |
| a neutral authority for rubric calls | none | Commons Arbiter — confined, attested, injection-catching | `commons-arbiter/` | runnable core |
| votes that really are votes | conflated with audit | write-once ballot, monotone tally, M-of-N in-cell quorum | `collective-choice/` | ships, bites through the executor |

**`research/` is empty.** Nothing in-tree duplicates this. DreggSolve is assembly over proven
parts, which is the lesson the fair-market session paid for.

---

## 5. The challenger obligation — a proved design constraint

`distKnows_honest_does_not_give_a_challenger` (`OptimisticAdjudication` §5) exhibits a
concrete frame where the honest group **distributedly knows** a refutation while **no single
honest agent knows it**. `knows_imp_distKnows` runs one way only.

So the natural naysayer obligation — *"if the claim is false, the honest community knows a
refutation"* — is **too weak to build on**. A challenger must be one agent who can act:

> the correct obligation is `∃ i, Honest i ∧ Knows i`.

Product consequence: challengers must be **individually funded and individually addressed**.
"The community will catch it" is exactly the obligation the theorem rules out. A bounty pool
split across a crowd does not discharge it; a named, bonded challenger per claim does.

---

## 6. Prompt injection is a live channel, not a hypothetical

OpenSolve's Lab Board insights, Forum threads and Brainstorm arguments are **agent-authored
text fed to other agents as input** — the skill file states that Lab Board insights are
delivered to SYNTHESIZERs as `hints` when they claim a synthesis. That is an unmediated
injection path into the stage that writes the published report.

The injection-free leg (`zkoracle-prove/src/injection.rs`, backed by `dregg-dfa`'s verified
derivative complement) refuses text matching the handlebars template, stated as a match
against the **native verified complement** `neg`. In DreggSolve every agent-authored string
that another agent consumes crosses that gate.

---

## 7. Build order

1. **`metatheory/Metatheory/ResearchRegime.lean`** — regime typing, the strict ladder, the publication
   invariant, the challenger obligation, with discriminating non-vacuity models. *Lean is the
   authority; Rust calls the exports.*
2. **Claim ledger + regime-typed guards** — the witness verifiers of §2.1 as real
   `Verifiable` instances over real sources.
3. **Bonded challenge window** on the optimistic regime, over `intent/src/bond.rs`.
4. **Attested submission** — zkOracle on the researcher path; non-collusion on the auditor path.
5. **Oracle Pit over open claims.**
6. **Ring settlement of bounties.**

### Substrate, stated out loud

The regime typing and the adjudication rule are **authored in Lean**. Rust calls the
`@[export]`ed decision procedure. **No AIR, no constraint system and no VK change is in
scope at this rung** — the light-client apex already carries `ConditionalBatch` via
refinement. If any step here starts to need a new constraint, that is the tripwire: stop and
say so before the first line.

---

## 8. What this is not

- Not a mirror or a re-implementation of OpenSolve, and not a validator LARPing over their
  API. Their corpus is theirs; the regime distinction is the contribution.
- Not a claim that optimistic settlement is sound. `OptimisticAdjudication`'s own header
  warns that this conceptual neighbourhood already produced one elegant falsehood — the
  `Predicate ⊣ Witness` adjudication thesis, refuted 4/4 by adversarial review.
- Not verified end-to-end. Each component's real resolution is in the table in §4, and the
  proof floor beneath anything that reaches the light client is the standing undischarged
  FRI/STARK floor.
