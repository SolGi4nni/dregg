# Frustum-replay + membrane-negotiation — the three open continents, sharpened

*(2026-06-14. Advances `REHYDRATABLE-SURFACES.md` past its three residuals, against
what is now STEEL in the tree. The vision is ember's "rehydratable certified-compositor
over a witness-graph"; this doc pins the **semantics** of the two parts the prior draft
named-but-waved (the replay derivation; the negotiation continent) and states the dregg4
forward as honest CONJECTURE-vs-result. Companion Lean: `metatheory/Dregg2/Deos/ReplayMembrane.lean`.
Siblings: `REHYDRATABLE-SURFACES.md` (the model), `docs/deos/DEOS.md` (the four targets),
`Dregg2/Deos/{Rehydration,Membrane}.lean` (the proven crowns), `Dregg2/JointTurn.lean`
(the cross-cell trunk).)*

## Where the foundation actually stands (so we advance, not re-pour)

The four `DEOS.md` targets are **discharged** (`Dregg2/Deos/`, axiom-clean, `lake build
Dregg2` green, LOCAL):

| target | theorem | what it nails |
|---|---|---|
| 1 surface-as-cap | `surfaceConfersExactly`, `viewSurface_confers_no_edge` | a window confers no authority beyond its rights |
| 2 membrane non-amp | `reshare_chain_attenuates`, `reshareN_attenuates`, `reshare_refuses_amplification` | a reshare A→B→C→…→Z grants ⊆ the first holder held |
| 3 **the crown** | `replayedDeterministic_iff_confined` (+ dual, +anti-ghost, +`replayedDeterministic_replays`) | `ReplayedDeterministic` IS *exactly* the confined fragment |
| 4 affordance | `fire_authorized_iff`, `firedSurface_binds_attested_root` | an agent fires only what its caps authorize; post-state binds the root |

So the *classifier* is confinement-faithful and the *chain* is tamper-evident. What is
**still open** — the three continents this doc advances — is sharper than "negotiation UX
is wood":

- **(C1) the replay DERIVATION.** The crown proves `classify = ReplayedDeterministic ↔
  confined`. It does **not** prove that a confined context *replays to a unique state* —
  `replayedDeterministic_replays` proves **tamper-evidence** (you cannot forge a *different
  well-linked chain* with the same head), which is a strictly weaker fact than
  **determinism** (the replay map is a *function* of the witnessed trace). The honest gap:
  tamper-evidence rules out an *adversary substituting* a divergent history; determinism
  rules out the *same trace replaying two ways*. They are different theorems, and only the
  first is in the tree. **C1 closes the second**, and pins the residual it cannot close
  (agent-choice non-determinism) as an explicit, typed boundary — not a hand-wave.

- **(C2) the negotiation SEMANTICS** ("the unspecified continent"). The Rust
  `world::MembraneNegotiation` *enforces* refusals (`GranterLacksAuthority`, `GameStillLive`,
  `ReshareWouldAmplify`), but there is **no Lean** and **no statement of the algebra**: who
  proposes, who refuses, what the negotiated surface *is* as a function of the two parties'
  state, and — the part nobody has written down — why the two compositional failure modes
  (**confused-deputy**, **attenuation-drift**) cannot occur. **C2 gives the negotiation a
  semantics**: the negotiated projection is a **meet** (request ⊓ held), refusal is
  `request ⊄ held`, and the two failure modes are theorems (deputy: a granter confers no
  authority on a target whose authority it lacks; drift: the meet is order-independent so a
  re-negotiated chain cannot silently widen).

- **(C3) the dregg4 forward** — guarded comodel/lens, the single-machine n=1 collapse,
  simplicial joint turns. Stated here as **conjecture**, with a tractable lens-law fragment
  carried into Lean and the rest flagged ASPIRATIONAL (per the foundations reality-check:
  the category is a poem over the real coalgebra; dregg4 work = turning the poem into
  theorems).

---

## C1 — the replay derivation: tamper-evidence is not determinism (and the agent-choice floor)

### The conflation the prior draft made

`REHYDRATABLE-SURFACES.md` residual #2 says replay-fidelity is "bounded by witness
determinism" and the `Rehydration` type "stays honest about that gap." True, but it leaves
*determinism itself* as folklore. Two distinct claims live under "replays
deterministically":

1. **Tamper-evidence** (PROVEN, `replayedDeterministic_replays`): given the confined
   context's witnessed trace, no *other* well-linked receipt chain agreeing on the head is a
   *different* history. This is `chain_tamper_evident` under the §8 digest oracle. It defends
   against an **adversary** who proposes a forged divergent replay.

2. **Determinism** (the C1 target): the replay of a confined trace is a **function** of the
   trace — *re-running the same witnessed interactions yields the same state*, full stop, no
   adversary in the picture. This is what makes `ReplayedDeterministic` a *liveness* promise
   ("you get the same scene back") rather than only an *integrity* promise ("you can't be
   lied to about which scene").

These are independent. A system can be tamper-evident yet non-deterministic (the honest
fold is unique, but the *inputs* it folds were never fully captured — the servo
non-determinism). And it can be deterministic yet not tamper-evident (a pure function with
no integrity binding). The crown gives us #1's neighbour (the classifier) and #1 itself;
**C1 supplies #2 and locates exactly where #2 stops.**

### The derivation (precise)

A confined context's external trace is, by `confined`, a list of *witnessed* interactions,
each carrying an `AttestedRoot` that **structurally holds**. Model the replay as a **left
fold** over that trace: `replayState s₀ trace = trace.foldl stepReplay s₀`, where
`stepReplay` consumes one witnessed root and advances the reconstructed state. Then:

> **`confined_replay_deterministic` (C1 keystone).** For a confined trace, `replayState` is a
> *function* of `(s₀, trace)` — `replayState s₀ trace = replayState s₀ trace` is not the
> point; the content is that **two reconstructions from the same start and the same confined
> trace are equal**, because every step consumes only data *carried in the witness* (the
> attested root), with no free read of ambient state. The fold has no hidden input.

The load-bearing lemma is **closure under the witness**: `stepReplay` reads *only* the
`AttestedRoot` (a structurally-holding commitment) and the prior reconstructed state —
never an ambient value. That is exactly what `confined` guarantees: every interaction is
`.attested ar`, never `.ambient`. So the determinism is **derived from confinement**, not
assumed: an `.ambient` interaction is the *only* way `stepReplay` could need an input not in
the trace, and `confined` excludes it. **This is the derivation ember asked for**:
`ReplayedDeterministic`'s determinism half is *not a heuristic* — it is forced by "every
interaction was an attested turn," because an attested turn carries its own input and an
ambient one does not.

### The floor it cannot cross (the typed residual, honest)

Determinism of the *fold* does **not** make the replay equal to the original *live* run.
What the witness captures is the **attested commitment** at each step, not the *agent's
counterfactual choice* had the world differed. If the original servo run made a choice that
depended on real-time input (a keystroke at t=37ms, a race between two fetches), the witness
records *which branch was taken* (the attested root of the taken branch) but not a *generator*
that would re-take it from scratch. So:

- **Confined replay is deterministic-given-the-trace** (C1, proven): feeding the *same
  witnessed roots* yields the *same reconstruction*. This is what `ReplayedDeterministic`
  promises and is now a theorem.
- **Confined replay is faithful-to-the-original** *iff* the witness captured *every*
  choice-determining input as an attested turn — which `confined` asserts at the
  *interaction* granularity but **not** at the *intra-step timing* granularity. The residual:
  a context can be `confined` (every external fetch attested) yet its *internal scheduling*
  (which attested fetch resolved first) be un-witnessed. That residual is **exactly the line
  between `ReplayedDeterministic` and `Live`** — and it is *already typed*: a context whose
  scheduling matters and is un-witnessed is not confined at the granularity that would let
  it claim `Live`-equivalence; it claims `ReplayedDeterministic` (faithful fold) and no more.

**The sharpened honest line.** `ReplayedDeterministic` = "the fold of the witnessed trace is
a function and you will get *that* reconstruction every time" (PROVEN). It is **not**
"you will get the original live scene" — that is `Live`, reachable only when the sources are
up. The enum's *whole job* is to mark this gap, and C1 makes the `ReplayedDeterministic` rung
carry a real determinism theorem rather than a hope. The third rung,
`ReconstructedApproximate`, is where even the fold is not a function (an ambient input the
trace does not carry) — `confined = false`, and C1's hypothesis fails by construction.

**Result-vs-conjecture for C1:** the fold-determinism theorem is a **result** (Lean sketch
below, no oracle — it is a pure structural fact, unlike the tamper-evidence payoff which
genuinely needs §8). The claim that intra-step scheduling is the *only* remaining
non-determinism is a **modeling conjecture** (it depends on the servo execution model the
witness-graph captures; named, not proven).

---

## C2 — the membrane-negotiation continent: a meet, two refusals, two impossibilities

### The shape of a negotiation (who proposes, who refuses)

A membrane reacquisition has **two parties and two asymmetric roles**:

- the **granter** (G) holds a cap conferring authority `held(G)` over a surface;
- the **requester** (R) *proposes a projection* — the slice `ask(R)` of the surface it
  wants (a `keep`-set of `Auth`, or a richer projection predicate).

The prior draft's "neither side unilaterally dictates" is *correct but under-specified*. The
precise semantics: **the requester proposes the floor, the granter's holding is the ceiling,
and the negotiated surface is their meet.**

> **The negotiated projection is `ask(R) ⊓ held(G)`** (the **meet** in the rights lattice
> `Finset Auth`, = `ask ∩ held` on the conferred lists). The requester names what it wants;
> the granter's authority caps it; the result is *exactly the intersection*. Neither party
> dictates: R cannot get more than it asked (it is *its* floor), and R cannot get more than G
> holds (G's ceiling). This is **not new mathematics** — it is `attenuate (keep := ask) (cap
> := held-cap)`, the SAME per-hop projection `Membrane.hop` already names, re-read as a
> *negotiation outcome* rather than a unilateral attenuation.

This gives the two **refusal** semantics a precise home:

- **`GranterLacksAuthority`** (the no-peek refusal): R asks for an authority G does not hold
  (`ask ⊄ held`). The *meet* `ask ⊓ held` simply *omits* that authority — the membrane does
  not refuse the whole negotiation, it **silently darkens** the over-ask (this is the
  *attenuate-filters-it-out* tooth, `reshare_refuses_amplification`). The Rust
  `NegotiationError::GranterLacksAuthority` is the *strict* variant (refuse the whole grant
  if any over-ask), which is a **policy choice on top of the algebra**: strict-refuse vs.
  lenient-darken are *both* sound (both yield `⊆ held`); the algebra fixes the *ceiling*, the
  policy picks the *failure mode*. Naming this is itself progress — the prior draft treated
  "who refuses" as one undecided thing; it is two (the *algebra* never amplifies; the *policy*
  chooses strict-vs-lenient on the over-ask).
- **`GameStillLive` / `GranterPreconditionUnmet`** (the *stateful* refusal): G refuses to
  project *at all* while a state condition holds ("can't make the repo public while it has
  secrets"). This is **orthogonal to the rights meet** — it is a `TransitionGate`-style
  predicate on G's *cell state* (the `Dregg2.Deos.Reactive` machinery), gating *whether the
  negotiation opens*, not *what it confers*. So a negotiation is a **two-stage gate**: (i) a
  state precondition on G (does G *permit* projecting now?), then (ii) the rights meet (what
  does the projection *confer*?). C2 separates these; the prior draft fused them.

### Failure mode 1 — the confused deputy, as a theorem

The classic confused-deputy: a deputy holding authority over X is *tricked* into exercising
it on behalf of a requester who names a *different* target Y. In the membrane: can R get G to
confer a view of a surface G holds, but *aimed at a cell R is not entitled to*?

> **`deputy_confers_no_unheld_target` (C2).** A membrane projection by G confers authority
> *only on the target G's own cap names*. G cannot, by negotiating, mint a view of cell `c'`
> when G holds only a cap to cell `c`. Because `attenuate` preserves the cap's `target` (it
> filters *rights*, never *retargets*), and `capAuthConferred` of an `endpoint c r` is rights
> over `c` alone — **the negotiated cap is `endpoint c (r ∩ ask)`, still targeting `c`.** A
> requester naming `c'` in its ask does not retarget G's cap; the meet is taken on *rights*,
> and the target is G's. So the deputy cannot be confused into acting on a target it does not
> hold — the confused-deputy attack is **structurally absent**, by the same fact that makes
> attenuation non-amplifying, lifted to the *target* axis.

The deputy attack *survives* in ambient-authority systems precisely because the deputy's
authority is *named separately* from the request (an ACL check on the deputy's identity,
a path the requester supplies). In the cap membrane, **the authority and the designation are
the same object** (the cap names target *and* rights together) — so there is no request-supplied
target to confuse. C2 makes this a theorem rather than a slogan.

### Failure mode 2 — attenuation-drift, and why the chain cannot widen

"Attenuation-drift": across a chain of re-negotiations A→B→C, could the *accumulated*
projection silently *widen* — e.g. B negotiates `{read}` from A, then C negotiates `{read,
write}` from B, and through some compositional slip C ends with `write`?

`reshareN_attenuates` already proves C ⊆ A (the chain never exceeds the first holder).
C2 adds the **order-independence** that rules out the subtler drift — *the negotiated outcome
does not depend on the order or grouping of the re-negotiations*:

> **`negotiation_meet_assoc_comm` (C2).** The negotiated authority after a chain of asks is
> the **meet of all the asks with the original holding**, *independent of association and
> order*: `(((held ⊓ ask₁) ⊓ ask₂) ⊓ ask₃) = held ⊓ (ask₁ ⊓ ask₂ ⊓ ask₃) = held ⊓ ⨅ᵢ askᵢ`.
> Because `⊓` (set intersection on the conferred rights) is associative, commutative, and
> idempotent (`Finset Auth` is a `SemilatticeInf`). So a re-negotiated chain has **no
> path-dependence**: you cannot widen by re-grouping, re-ordering, or re-asking — the final
> authority is the meet of the *whole* ask-history with the *original* ceiling, a single
> well-defined value.

This is the precise content of "attenuation-drift cannot occur": drift would require the
outcome to depend on *how* the chain was taken (so a clever re-grouping recovers lost
authority). The semilattice laws forbid it. And `reshareN_attenuates` already bounds the
*value* (⊆ held); `negotiation_meet_assoc_comm` shows the value is *path-independent*.
Together: the chain neither exceeds nor depends-on-its-history — the two ways drift could
sneak in are both closed.

### What stays wood after C2

C2 pins the **algebra and the impossibilities**. What remains genuinely unbuilt:

- the **negotiation UX** (the GitHub-org-settings surface — the *interactive* propose/counter/
  accept loop). C2 says the *outcome* of any such loop is `held ⊓ ⨅askᵢ` gated by G's state
  precondition; it does not build the loop. (This is the same residual `REHYDRATABLE-SURFACES.md`
  #1 names, now with the outcome *pinned* so the UX is a thin shell over a known semantics.)
- **revocation timing** across a live negotiation (G revokes mid-chain). Single-machine this
  is immediate (C3's n=1 collapse); distributed it inherits the recency-floor. Named, deferred.

---

## C3 — the dregg4 forward (conjecture, with a tractable fragment)

Per the foundations reality-check (`project-dregg4-vision`): the lens/comodel/∞-category
names are *decoration over the real coalgebra* today; dregg4 work is **turning the poem into
theorems**. C3 states the three forward claims at the right honesty level.

### C3.1 — turn = guarded comodel / lens (CONJECTURE + tractable fragment)

The convergent frame: a turn is the **get/put/guard of a lens** — EFFECTS (state-transition,
the `put`) ⊕ CAVEATS (authorization, the `guard`) ⊕ ATTESTATION (the badge, the `get` of the
receipt). The strong claim — *`capExercise` IS lens composition, with the lens laws holding* —
is **aspirational** (no `νF`/comodel-morphism in the tree). But a **tractable fragment is a
result**: the *receipt projection* of a turn satisfies a **`get-put` coherence** — the
attested root read back from a fired surface (`get`) is exactly the post-state the effect
committed (`put`), which is precisely `firedSurface_root_is_new` (leg 4, PROVEN). So **one
lens law (get-after-put) already holds for the affordance turn**; C3 names it as such and
flags the *other* two laws (put-get, put-put) as the dregg4 build target. This is the
honest "poem→theorem" increment: claim only the law you can prove, name the rest.

### C3.2 — the single-machine n=1 collapse (CONJECTURE, the design rule as a typed bound)

Ember's principle: a single node is the *degenerate* distributed system (n=1,
partition-impossible, own quorum, total order) where the distributed impossibilities
**collapse** to strong-local properties. The precise form C3 proposes:

> **Bounds are parametrized by a `Topology` with `n : ℕ` participants. The distributed
> guarantees (causal-not-consistent checkpoint; blocking cross-cell commit under partition;
> revocation recency-floor) are stated as `n ≥ 2 → weak`, and at `n = 1` *instantiate* to the
> strong forms (consistent checkpoint; non-blocking synchronous commit; immediate
> revocation).** The collapse is not a new mechanism — it is the *same* theorem read at `n=1`,
> where the partition quantifier `∃ partition` is *empty* (a 1-node system has no nontrivial
> cut), so the weakness's *hypothesis* vanishes and the strong conclusion is recovered free.

The tractable fragment: the **atomicity** law. `atomicity_as_proof` already shows joint
commit ⇔ the cumulative-AND, *with no coordinator*. At `n=1` the cumulative AND is a single
conjunct, `willSucceed` is `LocalSucceeds` of the one cell, and `JointCommit` ⇔ that one
cell's success — i.e. **single-machine commit is just the cell's own step succeeding, no
binding premise needed** (the `JointBinding`/CG-5 cut is the *price of n≥2*; at n=1 the
balance is the single cell's own conservation, already in `Boundary`). So the n=1 collapse of
*atomicity* is reachable from `JointTurn`'s existing theorems by specializing `ι` to a
one-element index. C3 carries this specialization as the tractable fragment and flags the
full topology-parametrized bound suite as ASPIRATIONAL.

### C3.3 — simplicial joint turns (CONJECTURE, the price named)

The dregg4 vision: joint turns as *simplices* (a 2-cell is a pairwise turn, a 3-cell a
triple, …), with **tensor non-finality as the price**. The foundations reality-check
**corrected** the slogan: "νF₁⊗νF₂ not final" is FALSE-as-stated (product of finals *is*
final, `tensor_not_final` is about *bound* behaviours); the REAL obstruction is
`binding_is_proper` — sound joint turns are a **proper subobject** of the product, the
`JointBinding` (CG-2⊗CG-5) cut that no per-cell data supplies. C3 states the simplicial
forward *correctly*: the n-ary forest is `JointFamily`/`FamilyBinding` (BUILT,
`family_joint_sound`); the *simplicial structure* (face/degeneracy maps relating the k-cells)
is the ASPIRATIONAL layer — and the price is **not** non-finality but the **per-dimension
binding premise** (each k-simplex needs its own CG-2⊗CG-5 cut; the higher cells do not
reduce to the lower ones, exactly as `binding_is_proper` shows the 2-cell does not reduce to
the 1-cells). Naming the price *correctly* (proper-subobject binding, not tensor
non-finality) is the C3.3 contribution.

---

## The sharpened open frontier (what is now precisely open)

After this doc, the frontier is *narrower and named*:

1. **C1 residual (modeling conjecture):** that *intra-step scheduling* is the only
   non-determinism not captured by interaction-granularity confinement. To close: a servo
   execution model where scheduling is *itself* an attested turn (a "scheduling witness"),
   collapsing `ReplayedDeterministic` toward `Live`-equivalence. This is the real research
   question — *can the witness-graph capture enough that replay = resurrection?* — and it is
   now isolated from the (proven) fold-determinism.
2. **C2 residual (engineering):** the negotiation *loop* UX. The *outcome* is pinned
   (`held ⊓ ⨅askᵢ`, state-gated); the *interaction protocol* (counter-offers, timeouts,
   multi-party negotiation) is a thin shell — but a real one, and it is where the
   GitHub-org-settings framing earns its keep.
3. **C3 residuals (the dregg4 build):** the *other two lens laws* (put-get, put-put) for the
   turn; the *full topology-parametrized bound suite* (only atomicity's n=1 collapse is
   tractable today); the *simplicial face/degeneracy* structure on joint turns (per-dimension
   binding, not tensor non-finality). These are the "poem→theorem" backlog, now stated at the
   right honesty level so each can be picked up without re-deriving the framing.

The through-line: **the prior draft named three continents and called them "wood." This doc
shows two of them (C1 replay-determinism, C2 negotiation-as-meet + the two impossibilities)
are *reachable results* on the existing primitives, and the third (C3 dregg4) has a
tractable fragment per claim plus a correctly-named price. What is left is genuinely smaller:
one modeling conjecture (scheduling witnesses), one UX shell, and the dregg4 build backlog —
each isolated from the thing next to it that is already proven.**
