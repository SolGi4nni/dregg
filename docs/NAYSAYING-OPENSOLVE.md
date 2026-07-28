# A naysaying research institute — five design laws, and what they cost

**For builders of agent-run verification systems.** This is a design note, not a pitch and not
an integration proposal. dregg is **not** something you can take as a dependency today (§7 says
plainly why). What transfers is the *shape*: five laws about refutation-based settlement, each
with a concrete implementable form, all of them backed by machine-checked theorems in
`metatheory/Metatheory/OptimisticAdjudication.lean` so you can check the reasoning rather than
take our word for it.

Written with [OpenSolve](https://open-solve.com) in mind — a live decentralized research
institute run by AI agents — because it has the exact structure these laws are about: agents
produce claims, other agents check them, and something has to decide what stands.

---

## 0. The polarity choice nobody makes on purpose

There are three ways to settle a claim, and they are genuinely three different objects:

| regime | the verdict is | what it costs |
|---|---|---|
| **validity proof** | `∃ w. Discharged` — someone exhibited a checkable certificate | the certificate must exist and be produced |
| **optimistic / naysayer** | no refutation was *observed* in a window | a liveness assumption (§3) |
| **ballot** | an aggregation of assertions | Arrow / List–Pettit — there is *no* well-behaved aggregator |

Almost every agent platform lands in the ballot regime by default — N reviewers, majority
verdict — because it's the obvious thing to build. It is also the only one of the three with an
impossibility theorem attached: the non-existence of a good aggregator on the full domain *is*
the judgment-aggregation result. More reviewers doesn't move it.

The validity regime escapes that, but only by **restricting the domain** — you adjudicate only
claims that admit a certificate. That's a real restriction, and it's why the third regime
matters.

**The optimistic regime is the underrated one, and here is the counterintuitive part: for the
claims that are hardest to audit, it is *cheaper* than what you are probably doing now.**

Look at how research tasks actually decompose. In OpenSolve's live corpus, of 623 tasks, 143
are `gap` ("what is the primary unresolved methodological barrier to X") or `best_practice`
("which WMO document specifies the SOP for Y"). Those are the tasks where a positive certificate
is hardest to produce — and they are currently audited by the *same* two-reviewer ballot as a
task asking for a number with a unit. That spends the most reviewer effort exactly where
reviewing works worst.

Optimistic settlement inverts it: publish the claim, open a challenge window, let it stand
unless someone refutes it. One challenger who finds nothing costs less than two reviewers
performing a checklist. The following five laws are what you owe if you do that.

---

## 1. Law one — the free half is genuinely free; take it

**`upheld_optimisticallyUpheld`:** if a claim genuinely holds, no sound refutation of it can
exist, so none can be observed. Optimistic settlement therefore **never wrongly rejects an
honest claim.**

This direction needs only soundness of your refutation checker. No completeness assumption, no
liveness assumption, no synchrony, no honest majority. It is axiom-free.

**What to implement:** nothing. This is the half you get for free, and it's worth knowing which
half that is — it means the risk of an optimistic pipeline is *entirely* on the
false-positive side. You will never lose a good finding this way. Everything below is about the
other direction.

---

## 2. Law two — there are THREE gaps, they are independent, and you must say which one you closed

Between *"a refutation exists"* and *"the system saw one"* there are three distinct gaps. Most
designs collapse them into one and then claim the wrong thing.

1. **Existence** — does a refutation *exist* at all? (`RefutationComplete`) This is a property
   of your refutation *vocabulary*, not of your agents. **If your refutation language cannot
   express a failure mode, that failure mode is silently promoted to unchallengeable.** If a
   challenger can only say "source unreachable" and not "the cited effect size does not appear
   in the source", the second kind of error becomes permanently invisible — and your safety
   argument will still look fine.

2. **Findability** — can someone actually *compute* the certificate? (`RefutationEffective`,
   which is `Type`-valued precisely because it is **data**, an actual function, not a bare
   existential.)

3. **Delivery** — does it arrive inside the window? (`Actuated`, §3.)

Now the result that makes this worth stating, and it is a **negative** one —
`optimistic_sound_effective`:

> **Closing findability buys you a usable challenger and buys you nothing logically.**

Give the scheme a genuine refutation *algorithm* and an unrefuted claim is *still* only
`¬¬upheld`. The reason is structural: `RefutationEffective` is a function **of** `¬ upheld X`,
and the scheme never has `¬ upheld X` — it only ever has `¬¬ upheld X`. So the algorithm can
never be *run* by the soundness argument, however constructive the algorithm is.

**What to implement, and what not to claim:** build the findability tooling — it is how
challengers actually work. A full-text retrieval endpoint that hands a challenger the source
text *is* a findability tool and it is genuinely valuable. But do not market it as soundness.
It closes gap 2 and leaves gaps 1 and 3 exactly where they were.

And note the failure mode of an unclosed gap 1: it is not a breach, it is **vacuity** — the
safety argument goes through while nobody can construct the challenge it promises. That is much
harder to notice than a breach.

---

## 3. Law three — "nobody objected" is not evidence. Show the actuation.

`Actuated` says every refutation that exists is actually observed in the window. It is the
load-bearing assumption of every optimistic system, and it is **neither cryptographic nor
epistemic** — it is a claim about scheduling and delivery in your deployment. No amount of
cryptography closes it.

And it is not removable. **`optimistic_unsound_without_actuation`** is a fully-inhabited
counterexample where the optimistic verdict **upholds a claim that does not hold** — and in
that instance the refutation certificate *exists* and *is sound*. The only thing that failed is
that nobody delivered it. Refutation-completeness holds; the floor is still false.

**What to implement:** make actuation a visible field, not an assumption.

These two states are completely different and most schemas cannot tell them apart:

```
window closed, 0 challengers assigned, 0 reports        →  no information
window closed, 3 challengers funded, 3 filed
   "checked pp. 4–6, no contradiction found"            →  real evidence
```

Both are "no refutation observed." Only the second is worth anything. So a settled claim should
carry *who was funded to attack it, what they checked, and whether they reported* — and a claim
whose window closed with nobody looking should be rendered as **unexamined**, not as verified.
That is a data-model change and a badge change, not a cryptography project.

---

## 4. Law four — fund a named challenger, not "the community"

The obligation a design doc reaches for by default is: *if the claim is false, the honest
community knows a refutation.* **That obligation is too weak, and there is a concrete
counterexample.**

`distKnows_honest_does_not_give_a_challenger` exhibits a frame where the honest group
**distributedly knows** a refutation while **no single honest agent knows it**. Distributed
knowledge is a meet over indistinguishability — it can be strictly larger than any member's
knowledge. And a challenger has to be *one party that can act*.

So the correct obligation is strictly stronger:

> `∃ i, Honest i ∧ Knows i` — some *single* honest agent knows it.

**What to implement:** assign and fund challengers **individually, per claim**. A reward pool
split across everyone who participated does not discharge this obligation — it funds
*attendance*. Concretely, contrast two payout rules:

- *pays attendance:* every reviewer attached to a claim that passes earns a flat reward,
  regardless of their own verdict. This prices being present.
- *pays challenge:* a bounty on each open claim, payable to the specific agent who produces a
  **sustained** refutation. This prices finding the error.

The second is the one that buys you a challenger. If your reward for reviewing is independent
of what the review found, you have not funded adversarial work — and the checkable parts of
your review payload will be the parts that go unfilled, because they are the only ones that
cost anything to produce.

---

## 5. Law five — the negative side cannot use untrusted search the way the positive side can

This is the asymmetry that catches people, and it's the one we'd most want a naysayer system to
get right from the start.

On the **positive** side, an untrusted prover is fine. Our `Searchable` deliberately carries
**no soundness field** so that adversarial and broken searchers remain legal instances —
consumers re-check whatever it returns and never trust it. `searched_refutation_sound_when_checked`
makes the point sharply: in that lemma the hypothesis "the searcher found it" is **unused**, and
*that is the content* — no property of the searcher is needed, because the consumer re-checks.

This is also exactly why an LLM is a *legitimate* component and not a compromise: it occupies
the untrusted-search slot. Capability is unbounded on the find side and irrelevant on the verify
side.

But the negative side is different, and the reason is one sentence:

> The positive side can afford untrusted search because the verdict **re-checks**. The negative
> side cannot, because the verdict **is** the check.

In an optimistic settlement a refutation is *acted upon* — it flips the verdict. So an unsound
refutation checker lets a naysayer grief honest work with no recourse.

**What to implement:**

1. **Refutations are certificate-bearing.** A refutation is not a verdict flag; it is a locator
   plus the content at that locator that contradicts the claim. Re-checkable by a third party
   who trusts neither the claimant nor the challenger.
2. **A refuted refutation costs the challenger.** Bond the challenge, slash on a refutation
   that fails re-check. Without this you have built a griefing vector and labelled it a safety
   mechanism.

Note the pleasing consequence: the challenger's certificate is subject to exactly the same
discipline as the claim it attacks. The asymmetry in the *logic* produces symmetry in the
*protocol*.

---

## 6. The diagnostic worth stealing

One line from that module, machine-checked, and it's the most useful sentence in it:

> A validity proof is **constructive**. An optimistic verdict is **classical reasoning,
> deployed.**

The constructive core of optimistic settlement stops at `optimistic_gives_double_negation`:
under both obligations, an unrefuted claim is `¬¬upheld`. That theorem costs **no axioms at
all**. The step from `¬¬upheld` to `upheld` is double-negation elimination — because *"nothing
refuted it, therefore it holds"* **is** DNE — and it is the single place `Classical.choice`
enters the whole module.

That is not a security claim. Nobody steals anything with Hilbert choice. It is a **diagnostic**:
where the classical step appears tells you which regime you're actually in. If you can't point
at the DNE in your own pipeline, you probably think you're in the validity regime when you're
not.

`optimistic_sound_of_decided` shows precisely what would earn the collapse back: decidability
of the claim's status. Which you don't have, for the same reason the claim needed adjudicating.

---

## 7. What dregg adds, and why you can't depend on it yet

Being honest about both halves.

**What the dregg shape adds beyond the five laws.** In dregg a turn is the exercise of a
proof-carrying token over owned state, leaving a receipt, and the constraints bite **through a
verified executor**. The practical difference:

- **The fill is the guard.** A review missing its witness doesn't get recorded-but-discounted;
  it **doesn't commit**, and the caller gets a typed refusal saying which gate said no
  (`required ⊄ held` at the capability gate, versus a kernel guarantee firing). The difference
  between a nullable column and a constraint is the difference between a rule and a gate.
- **Receipts a stranger checks without asking you.** The evidence ledger verifies from one
  aggregate root without re-running history.
- **Capability-per-call at the tool boundary.** Our MCP server exposes each affordance with its
  capability badge and shows unauthorized messages rather than hiding them — you can see what
  the kernel *would* refuse before you call, and firing it returns the real refusal.

**Why it isn't a dependency today.** Plainly:

- The proof floor beneath anything reaching our light client is an **undischarged FRI/STARK
  soundness floor**. The deployed parameter ledger is an informal reading, not a statement
  attached to the verifier algorithm.
- The pieces above are separately real but **not composed into a research-claim system** — the
  cell programs, the bonding, the attestation and the market were each built for other jobs
  (auctions, games, a solver market).
- Integration means Lean-authored cell programs, an emit step, and a running node. That is a
  substrate commitment, not a library import.

So: take the laws. They're implementable in a FastAPI/Postgres platform in an afternoon, and
they hold whether or not anything in dregg ever ships. If the receipt layer becomes interesting
later, the seam to look at is the tool boundary — every call carrying a capability the kernel
admits or refuses — because that's the one place where the guarantee stops being a convention.

---

## Sources you can check

Everything above cites real declarations. `metatheory/Metatheory/OptimisticAdjudication.lean`:

| law | declaration |
|---|---|
| §1 free half | `upheld_optimisticallyUpheld` |
| §2 three gaps | `RefutationComplete` · `RefutationEffective` · `Actuated` |
| §2 negative result | `optimistic_sound_effective` · `optimistic_dne_effective` |
| §3 floor is false | `optimistic_unsound_without_actuation` · `actuation_is_what_fails` |
| §3 floor is satisfiable | `floor_is_satisfiable_and_refutable` |
| §4 challenger | `distKnows_honest_does_not_give_a_challenger` · `knows_imp_distKnows` |
| §5 re-check discipline | `searched_refutation_sound_when_checked` · `RefutationSearchable` |
| §6 the DNE | `optimistic_gives_double_negation` · `optimistic_sound` · `optimistic_sound_of_decided` |
| regime separations | `Metatheory/ResearchRegime.lean` |

⚠ One honest warning, which that module carries in its own header: this conceptual
neighbourhood has already produced one elegant falsehood on our side — an adjudication-adjoint
thesis that a four-lens adversarial review refuted 4/4. Nothing here should be read as
"optimistic settlement is sound." The five laws are what it *costs*; the module is careful to
prove the floor false rather than assume it.
