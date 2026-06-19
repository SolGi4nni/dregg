# THE CATEGORICAL SEMANTICS OF DISTRIBUTED TIME-TRAVEL
## What a branch *is*, who must consent, when settlement happens, and why revocation is the one place "close enough" can be subtly wrong

*A teacher's treatment. Intuition first, formalism second, dregg third. For the
reader who knows category theory and distributed systems and finds the
**categorical interpretation** of distributed time-travel mysterious — and wants
to know whether there is a principled construction to pursue or whether we
assemble what we have close enough. The honest verdict is in §6; it is "pursue a
*narrow* construction, because the pieces already realize the rest." Citations
flagged-from-memory for spot-check are gathered in §7.*

---

## 0. THE ONE-SENTENCE ANSWER (so you can read the rest knowing where it lands)

> **Distributed time-travel is navigation of the lattice of consistent
> configurations of an event structure, where forking is free (configurations are
> cheap and verifiable), forking *forward* is causal-consistent reversible
> computation (the parties whose causal cone you touch must consent), and
> settlement is a *preferred* maximal configuration selected by common-knowledge
> consensus — and the only genuinely non-monotone operation in the whole picture
> is revocation, which is authority-negation, which is why authority must be
> evaluated at the settlement tip and not at branch time.**

Every clause of that sentence is a named construction with prior art, and dregg
already instantiates most of them. The mystery dissolves into: *one* place
(revocation/settlement) where the semantics genuinely matters and "close enough"
could be wrong, and a handful of places where dregg's existing parts simply *are*
the construction and the only open work is *proving* the instance faithful.

---

## 1. THE PHENOMENON, PRECISELY

### 1.1 The picture in ember's words, made precise

"Replay fresh things out of old stuff, from that point in the ledger, with the
parties willing to entertain it — fully distributed houyhnhnm. Parties serve
historical witnesses. It's fine to do stuff on side past branches (Mina had this)
as long as settlement of stored stuff by end operators happens on some consensus
tip. But not in all cases — revocation gets involved."

Unpack into six primitives:

1. **A past witness-cursor.** A point in the recorded history — for dregg, a
   `WitnessCursor{height, receipt_head}` (`starbridge-v2/src/ui_snapshot.rs`), or
   a step index `k` into a `History` (`starbridge-v2/src/replay.rs`), or a
   causally-closed set of blocks in the blocklace.

2. **Fork at that cursor.** Reconstruct the world *as it was* at the cursor —
   verifiably (`History::replay_to(k)` re-derives the ledger from genesis and
   checks the reconstructed canonical root against the recorded tooth, fail-closed
   on `RootMismatch`). The fork is *cheap*: it is a cursor, not a deep copy. (When
   you actually want a mutable divergent copy, that is `World::fork` /
   `History::fork_at`, the throwaway ledger.)

3. **Replay fresh turns forward.** On the fork, run *new* turns — counterfactual
   ones the mainline never saw (`History::fork_at(k, alt)`,
   `starbridge-v2/src/simulate.rs::simulate`). This is the "replay fresh things out
   of old stuff" — not re-running the recorded turns, but *new* turns from an old
   state. A branch.

4. **Branches are free + verifiable.** Anyone can fork-and-explore; every landing
   is root-verified, so a branch is a first-class, checkable object, and the
   mainline is provably untouched (`fork_diverges_and_leaves_the_mainline_intact`).

5. **Parties serve historical witnesses.** To fork at a cursor you may need state
   you don't hold — past receipts, past cells. Other nodes *serve* those witness
   slices, trustlessly: the server hands you a slice and a proof that it is the
   slice the origin committed (the attested-fetch path of `DISTRIBUTED-SERVO.md`
   §1; Willow range-reconciliation over the receipt-stream Merkle tree).

6. **Settlement happens on a consensus tip.** A branch is a *possibility*. For it
   to become *stored stuff settled by end operators*, its turns must land on a
   tip the federation agrees on — the blocklace's finalized prefix. Side branches
   are fine to *entertain*; they become *real* only by settling on the tip.

And the wrinkle:

7. **Revocation complicates it.** A capability valid at the branch point may have
   been *revoked* by the time you try to settle. Replaying a turn that exercised
   that authority is only legitimate if the authority still holds *at settlement*.
   This is the one place the monotone "merge where consistent" story breaks.

### 1.2 The questions a *semantics* must answer

A semantics is not a feature list; it is a set of answers to:

- **What is a branch?** (A what, formally — a configuration? a fork object? a
  fibre?)
- **When may you fork?** (At any cursor? Only causally-closed ones? Only finalized
  ones?)
- **Who must consent?** (Nobody — branches are free? The parties in the causal
  cone you replay over? The whole federation?)
- **What is a merge?** (Set union of branches? Sheaf gluing where consistent?
  Forbidden, with serialization instead?)
- **What is settlement?** (A distinguished branch? A maximal configuration? A
  common-knowledge fixpoint?)
- **How does revocation interact?** (Is authority a fact you carry forward from
  the branch point, or a fact you re-evaluate at the tip?)

The rest of this document answers each, twice: once in the abstract (the candidate
constructions, §2) and once in dregg (§3), with revocation given its own treatment
(§4) because it is the load-bearing one.

---

## 2. THE CANDIDATE CONSTRUCTIONS, TAUGHT

Five frames. Each is *intuition first, then the formal object, then the canonical
citation, then exactly which of §1.2's questions it answers*. They are not rivals;
they are facets, and §3 shows they compose into one picture over dregg.

### 2.1 Event structures and the domain of configurations (Winskel)

**Intuition.** Forget time as a line. Think of *events* (a turn happening, a block
being created) with two relations between them: **causality** (event `a` must
happen before event `b` — `a ≤ b`) and **conflict** (events `a # b` cannot both be
in the same history — they are incompatible). A *history* is then any set of
events that is (i) **downward-closed** under causality (if `b` is in and `a ≤ b`,
then `a` is in — you can't have an effect without its cause) and (ii)
**conflict-free** (no two events in conflict). Such a set is called a
**configuration**. The set of all configurations, ordered by inclusion, is the
**domain of configurations** — and *that domain is the state space of time-travel*.

A branch is a configuration. To "fork at a cursor and replay forward" is to take a
configuration `C` and grow it by adding events not in conflict with `C` — moving
*up* in the domain. Two branches from the same cursor are two configurations
extending the same `C`; they are *compatible* (mergeable) exactly when their union
is still conflict-free, i.e. still a configuration.

**The formal object.** A **prime event structure** is `(E, ≤, #)` where `E` is a
set of events, `≤` a partial order (causality) with finite downsets (`{a : a ≤ e}`
finite — every event has finitely many causes), and `#` an irreflexive symmetric
*conflict* relation that is **inherited** along causality: `a # b ∧ b ≤ c ⟹ a # c`
(if `a` conflicts with `b`, it conflicts with everything `b` causes). A
**configuration** is a downward-closed, conflict-free `C ⊆ E`. The configurations
ordered by `⊆` form a **coherent, prime-algebraic, finitary domain** — a
particularly well-behaved complete partial order (a *dI-domain*). Event structures
form a **category** (Winskel) whose morphisms are partial functions on events
preserving causality and reflecting conflict; this category is equivalent (via the
configuration functor) to a category of these domains, and it sits in a web of
equivalences/coreflections with **Mazurkiewicz trace languages** (independence =
the absence of causal order between events) and **safe Petri nets** (the events are
transition firings; the net's structure generates the causality and conflict).

**Citation.** Glynn Winskel, *Event Structures* (1986, in the Advanced Course on
Petri Nets, LNCS 255); Nielsen–Plotkin–Winskel, *Petri Nets, Event Structures and
Domains* (TCS, 1981). The trace/Petri/domain equivalences are the "Winskel school"
of true-concurrency semantics. *[Dates from memory — confirm.]*

**Which questions it answers.** *What is a branch?* — a configuration. *When may
you fork?* — at any configuration (any downward-closed conflict-free set). *What is
a merge?* — set union, **when the union is still a configuration** (conflict-free);
otherwise the branches are in conflict and cannot merge. It does **not** by itself
say who must *consent* to a fork, nor which configuration is *settled* — those are
§2.2 and §2.4.

### 2.2 Causal-consistent reversible computation (Danos–Krivine RCCS; Lanese et al.)

**Intuition.** This is the formal theory of *"with the parties willing to entertain
it."* Ordinary forward computation is a one-way street. Reversible computation lets
you *undo* steps — but in a *concurrent, distributed* setting you cannot undo a step
in isolation: if event `b` causally depends on event `a`, you cannot undo `a` while
`b` still stands. **Causal-consistent reversibility** is exactly the discipline:
*an event may be reversed only if everything that causally depends on it has already
been reversed (or consents to being reversed too).* Undoing ripples through the
causal cone, and the parties owning the dependent events are precisely the parties
who must "be willing."

This is the time-travel discipline. Forking at a past cursor and replaying forward
is "undo back to the cursor, then redo differently." The *undo* is only legitimate
with the causal-downstream parties' consent — which is why you can't silently
rewrite shared history. It is the operational meaning of *configuration*: a
reachable state is a configuration, and the reachable configurations are *exactly*
those obtainable by causal-consistent forward-and-back moves (the Lanese–Danos
result that causal-consistent reversibility characterizes the *causal equivalence*
of computations — you can reach a state by undo/redo iff it is causally equivalent
to a forward-reachable one).

**The formal object.** RCCS (Reversible CCS) decorates each process with a
**memory** — a stack of the communications it has engaged in, so each step is
recorded and can be rolled back. The central theorem is the **causal consistency
theorem**: the equivalence on computations generated by "reverse then re-do the
same step is identity" coincides with permutation of *concurrent* (causally
independent) steps — i.e. *backtracking respects causality*. Lanese, Mezzina,
Stefani, and others generalize this to higher-order π (rho-π) and give
**controlled / causal-consistent rollback** and the crucial extension for us:
**irreversible (committed) actions** — actions marked as un-undoable, so the
reversible substrate has *islands of irreversibility*. Settlement and revocation
are exactly such committed actions (§4).

**Citation.** Vincent Danos & Jean Krivine, *Reversible Communicating Systems*
(CONCUR 2004); Danos–Krivine, *Transactions in RCCS* (CONCUR 2005, the
irreversible/commit story); Ivan Lanese, Claudio Mezzina, Jean-Bernard Stefani and
collaborators, *Reversing Higher-Order Pi* and the *causal-consistent reversible
debugging / rollback* line (CONCUR 2010–2018+). *[Attributions from memory —
confirm the irreversible-action paper in particular.]*

**Which questions it answers.** *Who must consent?* — the parties whose events lie
in the causal cone you reverse. *When may you fork?* — when you can causal-consistently
roll back to the cursor (the downstream cone consents or is empty). It supplies the
*consent membrane* the bare event-structure picture lacks. And its committed-action
extension is the seed of §4's revocation/settlement answer.

### 2.3 Sheaf / presheaf semantics — merge-where-consistent, and branching-as-presheaf

**Intuition (sheaf).** A sheaf is the mathematics of *"local data that glues into
global data exactly where it agrees."* You have a space of "observation contexts"
(here: which parties, which cells, which time-slice you can see), local data over
each context (the witnessed state there), **restriction maps** (forget down to a
smaller context), and the **gluing condition**: a family of local sections that
*agree on overlaps* glues to a unique global section. This is precisely
"merge-where-consistent": two branches that agree on the cells they share glue to
one branch; where they *disagree* (conflict), gluing **fails** — and the failure is
not a bug, it is the obstruction (a nonzero cohomology class) that *tells you a
consensus decision is required*. Goguen's sheaf semantics of concurrent interacting
objects makes each object a sheaf over a time category and interaction a limit; the
*non-existence* of a gluing is the formal shadow of a Byzantine disagreement.

**Intuition (presheaf / topos of trees).** Branching time itself has a clean
categorical home. Take the poset of "stages of knowledge" (or of time-depth) as a
category; a **presheaf** over it is a family of sets indexed by stage with
restriction maps — exactly a *tree of possible futures with a notion of "what is
known at depth n."* The **topos of trees** `Set^{ω^op}` (presheaves over the
ordinal ω) is the canonical model of **guarded recursion** and step-indexed,
branching-time reasoning: the *later* modality `▶` shifts you one step into the
future, and guarded fixpoints (recursive definitions that only ever reference
strictly-earlier stages) are well-defined *because* the topos structure makes the
shift a contraction. This is the categorical engine for "branching futures with
well-founded reference to the past" — and (the link to `STRATIFIED-FIXPOINT.md`)
the *unit-delay* that breaks a reflexive cycle is exactly the `▶` of the topos of
trees.

**The formal objects.** A **sheaf** on a site `(C, J)` is a presheaf `F : C^op →
Set` satisfying the gluing condition for every covering family in the Grothendieck
topology `J`. A **presheaf** drops the gluing condition (branches need not be
consistent). The **topos of trees** is `Set^{ω^op}` with `▶ : Set^{ω^op} →
Set^{ω^op}`, `(▶X)(0) = 1`, `(▶X)(n+1) = X(n)`, and the **Banach/guarded fixpoint**
`fix : (▶X → X) → X`.

**Citation.** Joseph Goguen, *Sheaf Semantics for Concurrent Interacting Objects*
(Math. Struct. Comp. Sci., 1992); Lars Birkedal, Rasmus Møgelberg, Jan Schwinghammer,
Kristian Støvring, *First Steps in Synthetic Guarded Domain Theory: Step-Indexing in
the Topos of Trees* (LMCS, 2012). General sheaf theory: Mac Lane–Moerdijk, *Sheaves
in Geometry and Logic*. *[Dates from memory — confirm.]*

**Which questions it answers.** *What is a merge?* — sheaf gluing: branches glue iff
they agree on overlaps; disagreement is the obstruction that forces consensus. *What
is the membrane?* — the restriction map (the attenuation/forgetting that lets you
serve a *slice* of history without the whole). *What is branching-time recursion?* —
guarded recursion in the topos of trees, with `▶` as the principled one-step delay.

### 2.4 The lattice of consistent cuts (Mattern; Chandy–Lamport)

**Intuition.** In a distributed system, a **consistent cut** (a *consistent global
snapshot*) is a choice of "how far along" each node is, such that no message is
received-before-sent across the cut — i.e. the cut is *downward-closed under the
message-causality order*. The set of all consistent cuts of a distributed execution,
ordered by "is-a-prefix-of," forms a **lattice** (Mattern): the meet of two
consistent cuts is consistent, the join is consistent, there is a least (initial)
and greatest (current) cut. **Time-travel is navigation of this lattice.** A past
witness-cursor *is* a consistent cut. Forking is descending to a past cut and
ascending differently. The Chandy–Lamport algorithm is the operational way to
*capture* one such cut without stopping the system.

**The punchline that ties it to event structures.** A consistent cut is *exactly* a
finite configuration of the event structure whose events are the local steps and
whose causality is the message-and-program order. So §2.1 and §2.4 are the **same
lattice** seen abstractly (configuration domain) and operationally (snapshot
lattice). That is not a coincidence to gloss; it is the bridge that lets dregg's
*distributed* snapshots be the *event-structure configurations* of §2.1 (§3.4).

**The formal object.** For an execution with events `E` and the
Lamport/message-causality partial order `→`, a **consistent cut** is a downward-closed
`C ⊆ E`. These form a distributive lattice (a sub-lattice of the powerset, in fact
the lattice of *antichains*/down-sets — Birkhoff duality). Mattern's *vector clocks*
compute the order; Chandy–Lamport captures a member.

**Citation.** Friedemann Mattern, *Virtual Time and Global States of Distributed
Systems* (1989); K. Mani Chandy & Leslie Lamport, *Distributed Snapshots:
Determining Global States of Distributed Systems* (ACM TOCS, 1985); the
configuration-lattice = snapshot-lattice identification is folklore in the
true-concurrency community. *[Dates from memory — confirm.]*

**Which questions it answers.** *What is a cursor / branch point?* — a consistent
cut. *When may you fork?* — at any consistent cut (any past member of the lattice).
*What is settlement?* — a *distinguished path* through the lattice to a greatest
element (the consensus tip; §2.5/§3.5). It supplies the *global-state* reading that
the local event-structure picture needs to be genuinely *distributed*.

### 2.5 (Apt, only because it's genuinely needed) Settlement as a preferred maximal configuration

Event-structure configurations and consistent cuts give you a *lattice of possible
histories*. **Settlement** is the choice of *one* maximal element as "the real one."
Two facets, both with prior art, both already in dregg:

- **Comonadic/coalgebraic history views.** "The state-as-seen-with-its-whole-past"
  is a comonad (the *non-empty-list / history comonad*, or the *causal-past*
  endofunctor); the receipt chain is its carrier, and `causal_past` (blocklace) is
  literally the comonad's `extend`/`extract` shape. This is illuminating enough to
  *name* (settlement is choosing a coalgebra-respecting maximal run) but not
  load-bearing — we don't need the full coalgebra to get the construction, so we
  flag it and move on.
- **Common-knowledge selection.** Which maximal configuration is *settled* is not a
  local fact; it is a **fixpoint** — common knowledge among the operators that *this*
  tip is the one. This is the Halpern–Moses common-knowledge object, and (per
  `project-adjunction-thesis-verdict`) it is the **limit-side / greatest-fixpoint**
  FLP-hard object, *not* the easy colimit join. Settlement is hard for exactly the
  reason consensus is hard.

I deliberately do **not** drag in HoTT paths-as-identifications here: merge-coherence
*could* be phrased as "a path between two configurations witnessing they are the same
settled history," but it adds vocabulary without changing the construction, so it is
skipped per the "only if genuinely illuminating" instruction.

---

## 3. THE MAP TO DREGG — RIGOROUSLY

Now the claim that makes the abstraction concrete: **dregg's blocklace *is* an event
structure, its consistent configurations *are* the light-client-verifiable
histories, its cap-gate *is* the RCCS consent membrane, its conservation/nullifier
machinery *is* the cryptographic conflict relation, its finality *is* the preferred
maximal configuration, and its Willow attested-fetch *is* the witness-serving.** Each
mapping is stated as a correspondence with the code that realizes it.

### 3.1 The blocklace IS a (prime) event structure

| event structure | dregg blocklace | code |
|---|---|---|
| event `e ∈ E` | a `Block{creator, sequence, predecessors, payload, signature}` | `blocklace/src/lib.rs::Block` |
| causality `a ≤ b` | `a ∈ causal_past(b)` (transitive predecessor closure) | `Blocklace::causal_past` |
| finite downsets | `causal_past` is a finite BFS over predecessors | `causal_past` |
| configuration `C` | a **causally closed** block set (insert enforces: all predecessors present) | `Blocklace::insert` causal-closure check; `InsertError::MissingPredecessors` |
| conflict `a # b` (1): equivocation | two distinct blocks at the same `(creator, sequence)` | `EquivocationProof`; `Blocklace::find_conflict`; `equivocators` |
| conflict `a # b` (2): conservation collision | two turns spending the same value / nullifier | the executor's Σδ=0 + nullifier-non-membership (below) |
| conflict inheritance `a # b ∧ b ≤ c ⟹ a # c` | a block built atop a conflicting (equivocating) creator's strand inherits the conflict; the tip is *withdrawn* | `insert` withdraws `tips[creator]` on detected equivocation |

The blocklace's own trust-model header states the structural invariants that are the
event-structure axioms in disguise: *"Blocks are inserted only if all predecessors
are present (causal closure)"* (= downward-closure), *"The topological order is a
valid linearization of the causal DAG"* (= a configuration has a consistent
linearization), and equivocation as *attributable, detectable, never-overwritten*
evidence (= the conflict relation is *recorded*, not silently resolved). The
monotone-per-creator sequence (`SeqRegression` rejects a non-extending block) is the
*prime* discipline: each creator's strand is a chain, and conflict is the fork of a
chain.

**So:** a branch in dregg is a divergent causally-closed configuration of the
blocklace. Two branches are compatible iff their union is causally closed *and*
conflict-free — no equivocation, no double-spend. That is `merge` = union-where-it-is-still-a-configuration,
and `LaceMerge.lean` proves exactly this for the *monotone* part: the merge is a
pure `Finset`-union join on block ids (`laceIds (mergeLace B Δ) = laceIds B ∪
laceIds Δ`), commutative/associative/idempotent/monotone — the configuration union of
§2.1 made executable, with `Lace.Canonical` (content-addressing) giving the
"same keyset ⟹ same state" gluing.

### 3.2 Consistent configurations = light-client-verifiable histories

A configuration is "real" to a light client only if it can *check* it. dregg's
checkability is the replay tooth: `History::replay_to(k)` re-derives the ledger from
genesis and **verifies** the reconstructed canonical root against the recorded tooth,
refusing on mismatch (`ReplayError::RootMismatch`). So the *verifiable* configurations
are exactly those whose every prefix root-checks — and that is the same
`recover = checkpoint ⊕ overlay = replay` identity proved in
`CrashRecovery.lean::recover_eq_replay`. The Merkle root of the receipt stream is
the configuration's *commitment*; serving a slice of it trustlessly (§3.6) is serving
a sub-presheaf with its restriction map.

This is where the *light-client-unfoolability* spine reappears: a forked branch is
only entertainable if its claimed history is one the origin could have committed —
`AssuranceCase.lean::unfoolability_guarantee` (`verifyBatch accept ⟹ ∃ genuine kernel
transition`) is exactly "this configuration is a real configuration of the event
structure, not a forged one." Time-travel inherits unfoolability *for free* because a
branch is checked by the same tooth.

### 3.3 A branch = a divergent configuration; the cursor = a consistent cut

`History::fork_at(k, alt)` is the operational fork: replay-verify to cut `k`, apply a
*different* turn `alt`, run forward on a throwaway ledger, and report the divergence
diff against the mainline at the same depth, **leaving the mainline's recorded roots
untouched**. In §2 vocabulary: descend the configuration lattice to the consistent cut
`k`, ascend along a different edge, and observe you are now at an incomparable
maximal-so-far configuration. `Fork::diverged` is "the two configurations are
distinct"; `simulate.rs` is the same move with the explicit *predicted root* and
*predicted receipt* — a branch whose every consequence is computed by the real
executor one step ahead, with the live world `&`-borrowed and never mutated.

Mina's "side past branches" (ember's reference) are this: a node may explore and even
*build* on a non-tip branch (Mina's archive/fork-handling), as long as what *settles*
is on the selected chain. dregg's `fork_at` / `simulate` / `World::fork` are the
exact same affordance, with the verification tooth added.

### 3.4 The consensus tip = a preferred (maximal) configuration; finality = common-knowledge selection

The blocklace's finalized prefix (`finality.rs`, supermajority `⌊2n/3⌋+1`) is the
*preferred path* through the configuration lattice. `BlocklaceFinality.lean` proves
the ordering rule `tau` deterministic; `ConsensusExec.finalized_execution_agreement`
proves all honest nodes that see the same finalized blocks execute to the same state.
In §2.5 terms: **finality is the common-knowledge selection of one maximal
configuration as settled.** And per `project-adjunction-thesis-verdict`, this is the
*limit-side / greatest-fixpoint* (binding common knowledge `C_B`), the FLP-hard
object — which is the precise, principled reason settlement *cannot* be a free local
operation and *must* be consensus. Side branches are colimit-cheap (the union join);
settlement is limit-hard (the agreed fixpoint). That asymmetry is the whole shape of
"branches are free, settlement is consensus."

### 3.5 The cap-gate = RCCS causal-consent ("parties willing to entertain")

Here is the cleanest correspondence. RCCS says: *reverse an event only with the
consent of its causal-downstream parties.* dregg's authority model says: *exercise an
effect only under a capability you hold, and you can only grant what you hold
(`granted ⊆ held`, no amplification).* When you fork at a past cursor and replay a
turn forward, the turn's effects touch cells owned by parties; the executor's
**cap-gate is the consent check** — a replayed turn that touches a party's cell
without authority is *refused at the gate* (`simulate`'s `SimOutcome::Refused`,
the over-grant/over-spend/program-violation rejections). So "with the parties willing
to entertain it" is **not** a social protocol bolted on top — it is the
no-amplification gate the executor already enforces inline. The membrane around a
branch is the c-list: a fork can only do, on a party's cell, what some held cap
permits.

This is the §2.2 consent membrane *realized as cryptographic authority* rather than as
a process-calculus side-condition. It is also why dregg's time-travel is "fully
distributed houyhnhnm" and not a free-for-all: you cannot replay-fork over authority
you don't hold.

### 3.6 Conservation / nullifier-non-membership = cryptographic conflict-detection

The event-structure *conflict* relation, in the value layer, is a **cross-branch
double-spend**. Two branches that each spend the same note are in conflict; their
union is *not* a configuration (it would violate Σδ=0 / spend a nullifier twice). The
executor's conservation law (exact Σδ=0, `reachable_total_zero`) and the
noteSpend nullifier-non-membership grow-gate are the *decidable, cryptographic*
implementation of `#`. Crucially this conflict is **non-monotone** — it is the place
`Confluence.lean` flags: `balance ≥ 0` is *not* I-confluent (two withdrawals merge to
overdraft), so the value-bearing fragment's branches *cannot* be merged
coordination-free; `nonpairwise_escalation` *constructs* the clashing pair and forces
consensus. That is the event-structure conflict relation telling you, with a witness,
that these two branches will never glue — settlement must *choose*. (This is the same
wall as §3.4, seen at the data level: the receipt is a totally-ordered `List`, not an
order-blind `Set`, *because* it carries the non-monotone Σδ — per
`project-rhizomatic-dregg-slotting`.)

### 3.7 The membrane = sheaf restriction; serving historical witnesses = Willow attested-fetch

To fork at a cursor you may lack the witness state. A serving node hands you a
*slice* — a sub-presheaf — and a proof it is the origin's committed slice. This is
the sheaf **restriction map** made trustless: `DISTRIBUTED-SERVO.md` §1 dials the
hosting node, runs a cap-gated serve-turn, and returns **attested content** whose hash
the origin's quorum-finalized state root binds (`AttestedRoot`,
`merkle_root_of_receipt_hashes`), checkable by the in-tab light client
(`verify_history`). Willow-style range-reconciliation over the receipt-stream Merkle
tree is the efficient *which-slice-do-you-need* protocol. So "parties serve historical
witnesses" = the sheaf's restriction-and-glue, with each restriction *attested* so the
glued global section is verifiable. The membrane is a cap (you serve only the slice the
requester's cap reaches), and the restriction is content-committed.

### 3.8 The I-confluent / rhizomatic fragment = the monotone merge sub-algebra

Not all of dregg needs consensus to merge branches. The **I-confluent fragment**
(grow-only sets, append-only evidence, monotone predicates — `project-rhizomatic-dregg-slotting`)
merges by pure union: two branches over I-confluent state *always* glue
(`IConfluent I := ∀ x y, I x → I y → I(x ⊔ y)`; `admits_sound`). This is the
*coordination-free* sub-domain of the configuration lattice — the part where "merge =
union" is unconditionally a configuration, no conflict possible. Rhizomatic *is* this
fragment taken globally. So dregg's time-travel has **two regimes**, and the
`ConfluenceClassifier` is the static gate that decides which: monotone branches glue
freely (sheaf gluing always succeeds, the topos-of-trees presheaf *is* a sheaf there);
non-monotone (value/authority) branches carry a conflict relation and must settle on
the tip.

---

## 4. REVOCATION — THE NON-MONOTONE HEART

Everything above is *almost* a clean construction. Revocation is where "close enough"
can be subtly, dangerously wrong, so it gets its own rigorous treatment.

### 4.1 Revocation is a retraction of authority — and authority is not I-confluent

Granting a capability is monotone (more authority, never less — a grow-only fact).
**Revoking** a capability is a *retraction*: it makes a previously-true authority fact
false. In the event-structure picture, revocation introduces a **negative dependency**
— a later event's admissibility depends on the *absence* of a revocation. In the
I-confluence picture, *authority-with-revocation is not I-confluent*: branch A
exercises cap `c`; branch B revokes `c`; their "merge" must decide whether the exercise
in A is valid, and there is no monotone answer — it depends on order. This is the exact
shape `Confluence.lean` forbids for `balance ≥ 0`, now at the authority layer. And it
is the *same non-monotonicity* as `STRATIFIED-FIXPOINT.md`'s negation: revocation is
**authority-negation**, "you may NOT, because the cap was withdrawn," the anti-monotone
face of the projector. The data fragment can be I-confluent (rhizomatic), but the
**authority fragment with revocation cannot be** — that asymmetry is the whole §4.

### 4.2 Why this forces settlement-time authority evaluation (not branch-time)

The naive (wrong) reading: "a turn was authorized at the branch point, so replaying it
forward is fine." **No.** If the cap it exercised has since been revoked, the turn is
*not* legitimately settleable, even though it was legitimate at branch time. Authority
is a fact that must be evaluated **at the settlement tip**, because revocation is a
retraction that the branch point cannot see into the future of. Concretely, dregg
already models this in `Revocation.lean`:

- A `RevEvent` is *which* credential revoked, at *which* origin node, at *which*
  logical time.
- `localRevSet T log n t` is what node `n` *locally believes* is revoked at time `t`
  — the revocations that have had time to propagate (`issuedAt + delay m n ≤ t`).
- `honors` = the per-node admissibility decision, fed the *local* (possibly stale)
  revocation set.
- `eventual_bounded_revocation`: a credential revoked at origin `m` at time `τ` is
  **not honored by any node `n` at any `t ≥ τ + delay m n`** — never after the bound.
- `immediate_revocation` (the n=1 collapse): with instantaneous propagation, revoked-at-`τ`
  ⟹ not-honored-at-any-`t ≥ τ`.

The lesson for time-travel: **a branch's authority is "honored" only relative to a
revocation set, and the *settled* answer uses the settlement tip's revocation set, not
the branch point's.** A fork that replays an exercise of cap `c` is *entertainable*
(you can explore it), but it *settles* only if `c` is still honored at the tip's
local revocation view at settlement time. Branch-time authority is necessary;
settlement-time authority is what's *sufficient*. Evaluating authority at branch time
and carrying it forward is the precise way "close enough" is *wrong*: it would settle a
turn that exercised a since-revoked capability.

### 4.3 The right frame: reversible computation with *irreversible (committed) actions*

This is the construction to pursue, and it has exact prior art. RCCS-with-transactions
(Danos–Krivine 2005) and the controlled-reversibility line (Lanese et al.) add
**irreversible / committed actions** to the reversible substrate: most of the
computation is freely reversible (you can fork and undo), but certain actions are
*marked committed* and cannot be rolled back past. **Settlement is a committed action.
Revocation is a committed action.** The substrate is reversible (branches are free,
forking is causal-consistent undo/redo), with *islands of irreversibility* at exactly
the points where the federation has taken a binding common-knowledge decision.

This is precisely `STRATIFIED-FIXPOINT.md`'s stratification, transposed: the
*settlement-gate is the stratification boundary*. Below it, the monotone data merges
freely (the I-confluent fragment, the reversible substrate). The non-monotone
authority-negation (revocation) must point *strictly downward* to an *already-settled*
stratum — you evaluate "is this cap revoked?" against the **finalized** revocation set,
which is a *constant* by the time you settle, exactly as stratified negation reads only
lower, frozen strata. The settlement tip is the frozen stratum; revocation negates
against it; the fixpoint is well-founded *because* settlement commits first. The
committed action *is* the stratum boundary that makes the negation legal.

### 4.4 The honest residual

Two things must be true for §4.3 to be *correct* and not merely plausible:

1. **Settlement must commit the revocation set it evaluated against.** The settled
   configuration must bind, in its commitment, *which* revocations were in force —
   otherwise a light client cannot check that the settled turn's authority was honored
   at the tip. (This is the same shape as `holeFill_binds_in_circuit` from
   `project-partial-turn-promises`: every late-bound fact must bind into the proof the
   light client checks. Revocation-at-settlement is a late-bound *negative* fact and
   must bind the same way.)
2. **The propagation bound must be respected at settlement.** `eventual_bounded_revocation`
   gives a node a *stale* local view; settlement on the tip must use the tip's view,
   and the finality rule must not finalize a turn whose authority was revoked-before-but-not-yet-propagated
   in a way that two honest nodes could disagree on. The n=1 collapse
   (`immediate_revocation`) makes this trivial; the n>1 case is where the
   propagation-delay bound is load-bearing and must be inside the finality gate, not
   beside it.

These are the two places to *prove*, not assume. They are the difference between a
correct distributed-time-travel semantics and a close-enough one that occasionally
settles a revoked authority.

---

## 5. THE FLOW-ALGEBRA AND HYPERDOCTRINE THREADS (where ember's categorical work attaches)

Two of ember's existing categorical results slot directly into this picture; naming the
joints is part of the teaching.

- **Right-skew flow algebra (`project-flow-algebra-right-skew`).** "Choice does not
  left-distribute over composition" because the early-branch side must commit
  branch-vs-branch *before* observing what the first step *did*, whereas the late side
  chooses *after* observing. That is **exactly** the time-travel reactive rung:
  forking-then-deciding-which-branch-to-settle is choice *after* composition (you
  observe the branch's outcome, then settle), and it genuinely cannot be simulated by
  choosing the branch up front. The right-skew is the algebraic fingerprint of "settle
  after you see what the branch did," and `FlowRefine.lean::decideRefines` gives a
  *decision procedure* for "does branch-policy A refine B" — the ARGUS "refines" bar
  for branch admissibility. Distributed time-travel is a right-skewed flow.

- **The Lawvere hyperdoctrine (`project-adjunction-thesis-verdict`).** The correct
  structure for "agreement vs. adjudication" is a hyperdoctrine: agreement = limit
  (the consensus tip, the FLP-hard greatest fixpoint = settlement, §3.4), and
  adjudication = a *separately-built graded reflector* (which branch wins is not free
  from the meet). For time-travel: **selecting the settled branch among conflicting
  ones is the reflector**, and its good-behaviour is a per-regime side-condition —
  total on the *witness* fibre (certifiable branches: the executor's verdict decides),
  refutable=Arrow on the *ballot* fibre (when settlement needs a vote). So "which
  branch settles" is the graded reflector, and the place it can fail to exist cleanly
  is the place you're forced from deterministic-executor-decides into voting. That is
  the honest boundary of automatic settlement.

---

## 6. THE VERDICT — IS THERE A CONSTRUCTION TO PURSUE, OR DO WE ASSEMBLE CLOSE-ENOUGH?

ember's actual question. The honest, concrete answer.

### 6.1 Which dregg pieces already *realize* the construction

The bulk of the construction is **not** to-be-built; it is already instantiated, and
the mapping is faithful enough to lean on:

| construction | dregg realization | status |
|---|---|---|
| event structure (events/causality/conflict) | blocklace (Block/predecessors/equivocation) | **realized**, with `LaceMerge.lean` proving the union-join |
| configuration domain / consistent-cut lattice | causally-closed block sets; replay cursors | **realized** (`causal_past`, `History`) |
| verifiable configurations | root-tooth replay, `recover = replay` | **realized** + proved (`CrashRecovery.lean`) |
| free, verifiable branches | `fork_at` / `simulate` / `World::fork` | **realized** + tested (mainline-intact, predicted-root) |
| causal-consent membrane (RCCS) | the cap-gate, `granted ⊆ held`, no-amplification | **realized** (executor inline refusal) |
| cryptographic conflict (double-spend) | Σδ=0 + nullifier-non-membership | **realized** + `nonpairwise_escalation` forces consensus |
| preferred maximal config = settlement | blocklace finality, `tau`, finalized-execution-agreement | **realized** + proved |
| sheaf restriction = witness-serving | attested-fetch, `AttestedRoot`, Willow over the receipt tree | **realized** (distributed-servo path) |
| monotone merge sub-algebra | the I-confluent / rhizomatic fragment | **realized** + `Confluence.lean` |
| topology-bounded revocation | `Revocation.lean` (eventual-bounded / immediate) | **realized** + proved |

So the answer to "is there a construction to pursue or do we assemble what we have" is
**neither extreme**: we are *far past* "assemble loosely" — the parts are coherent and
mostly proved — but there *is* a narrow, principled construction worth pursuing, and it
is not the easy 90%.

### 6.2 Where the gap is

The gap is **not** in forking, branching, witness-serving, or monotone merge — those
are done and faithful. The gap is the **revocation/settlement seam** (§4): the two
residual obligations of §4.4.

1. **Bind the settlement-time revocation set into the commitment** so a light client
   checks authority-was-honored-at-the-tip, not just authority-was-honored-at-branch.
2. **Put the propagation-delay bound inside the finality gate**, so two honest nodes
   cannot disagree about whether a since-revoked authority settled.

This is exactly the one place §0 promised: the non-monotone heart, where "close
enough" is subtly wrong. A system that evaluates branch authority at branch time and
carries it forward into settlement is *close enough* in every monotone case and *wrong*
precisely when a revocation lands between branch and settlement. That is not a corner
case to wave at; it is the whole reason ember's intuition flagged "but not in all
cases — revocation gets involved."

### 6.3 Is *proving dregg a faithful instance* worth pursuing?

**Yes, but selectively.** The valuable proof is *not* re-proving the whole
event-structure axiomatization — that would be elegant but low-marginal-value, because
the parts that are already proved (`LaceMerge`, `CrashRecovery`, `Confluence`,
`BlocklaceFinality`, `Revocation`) already discharge the load-bearing facts (union is a
join; replay is recovery; non-confluent forces consensus; finality agrees; revocation
is topology-bounded). What is worth proving, *because it is the place correctness can be
silently wrong*, is the **settlement-time-authority theorem**:

> **(Settlement Soundness, the theorem to pursue.)** If a turn `T` settles on the
> finalized tip at height `h`, then every capability `T` exercised is honored by the
> tip's finalized revocation set at `h` — and the commitment at `h` binds that
> revocation set, so a light client accepting the settled batch can verify it.

This is a genuine extension of `AssuranceCase.lean::unfoolability_guarantee` (which
already gives "accept ⟹ genuine transition") to *"accept ⟹ genuine transition whose
authority was live at settlement,"* composed from `Revocation.lean`'s bound +
`FinalizedLightClient.lean`'s commitment + the cap-bridge. It is the
`holeFill_binds_in_circuit` discipline applied to the late-bound *negative* fact of
revocation. **That** is the construction to pursue — narrow, named, and exactly the
place the existing pieces don't yet meet.

### 6.4 The recommendation (a path, not a wall)

1. **Adopt the frame explicitly:** distributed time-travel = causal-consistent
   reversible computation (RCCS) over the blocklace event structure, with **settlement
   and revocation as the irreversible/committed actions** (Danos–Krivine transactions).
   Write it down as the semantics; it is faithful to what's built.

2. **Keep branches in the reversible substrate, free and monotone-mergeable** — exactly
   what `fork_at`/`simulate`/the I-confluent fragment already give. No new construction.
   Branches are colimit-cheap; do not gate them.

3. **Make settlement the stratification boundary.** Authority (with revocation) is
   evaluated against the *finalized* revocation set at the tip — never carried forward
   from branch time. This is the one behavioral rule that prevents the subtle bug.

4. **Prove Settlement Soundness (§6.3)** and bind the settlement-time revocation set
   into the finalized commitment (§4.4.1), with the propagation-delay bound inside the
   finality gate (§4.4.2). This is the small, high-value Lean work — compose
   `Revocation.lean` + `FinalizedLightClient.lean` + the cap-bridge, don't re-derive.

5. **Leave the comonad/HoTT/full event-structure-axiom formalizations as optional
   elegance** — illuminating to *name* (they confirm the shape), not load-bearing to
   *build*. The single-machine principle (`project-dregg4-vision`) is the reason the n=1
   collapse makes 3–4 nearly trivial and the general case a *parametrized* bound, not a
   different theorem.

The bottom line ember asked for: **we are constructing correctly everywhere *except*
the revocation/settlement seam, where the correct semantics is "settlement-time
authority evaluation with the revocation set bound into the commitment," and the one
thing to actually pursue is the Settlement Soundness theorem that makes that
evaluation light-client-checkable.** Everything else, we have — and it's coherent, not
a pile.

---

## 7. HONESTY LEDGER — what I assert from code vs. cite from memory

**Solid from dregg code/docs read for this doc (read-only, at HEAD):**
`Block{creator,sequence,predecessors,payload,signature}`, causal closure on insert,
monotone per-creator sequence, equivocation as detectable-attributable evidence with
tip-withdrawal (`blocklace/src/lib.rs`); `History::replay_to` root-verified replay with
`RootMismatch` fail-closed, `fork_at` mainline-intact, `recover = checkpoint ⊕ overlay`
(`starbridge-v2/src/replay.rs`); `simulate`/`World::fork` predicted-root/predicted-receipt,
cap-gated refusals (over-grant/over-spend/program-violation) (`starbridge-v2/src/simulate.rs`);
attested-fetch + `AttestedRoot` + light-client `verify_history` (`docs/DISTRIBUTED-SERVO.md`
§1); `IConfluent`/`admits_sound`/`nonpairwise_escalation` (`metatheory/Dregg2/Confluence.lean`);
`mergeLace` as `Finset`-union join, CRDT laws, `merge_convergence_to_state`
(`LaceMerge.lean`); `localRevSet`/`honors`/`eventual_bounded_revocation`/`immediate_revocation`
(`Distributed/Revocation.lean`); finality `tau` determinism + finalized-execution-agreement
(`BlocklaceFinality.lean`, referenced); the revocation=authority-negation = stratification
identity (`docs/deos/STRATIFIED-FIXPOINT.md`); the I-confluent/rhizomatic split and the
List-vs-Set receipt (`project-rhizomatic-dregg-slotting`); the hyperdoctrine/limit=agreement
+ graded-reflector verdict (`project-adjunction-thesis-verdict`); the right-skew flow algebra +
`decideRefines` (`project-flow-algebra-right-skew`); `holeFill_binds_in_circuit` as the
late-bound-fact-binds discipline (`project-partial-turn-promises`). The
`FinalizedLightClient.lean` / `AssuranceCase.lean` names exist in-tree; the precise contents of
the latter I cite by its memory-described `unfoolability_guarantee` shape — **confirm the exact
statement before leaning on it in a proof.**

**Canonical prior art — cited from memory; confirm dates/attributions before this goes outward:**
Winskel, *Event Structures* (LNCS 255, ~1986) + Nielsen–Plotkin–Winskel, *Petri Nets, Event
Structures and Domains* (TCS, ~1981); Danos–Krivine, *Reversible Communicating Systems* (CONCUR
2004) and *Transactions in RCCS* (CONCUR 2005); Lanese–Mezzina–Stefani et al. on causal-consistent
reversibility / reversing higher-order π and controlled rollback (CONCUR 2010s); Goguen, *Sheaf
Semantics for Concurrent Interacting Objects* (MSCS ~1992); Birkedal–Møgelberg–Schwinghammer–Støvring,
*Step-Indexing in the Topos of Trees* (LMCS ~2012); Mattern, *Virtual Time and Global States* (~1989);
Chandy–Lamport, *Distributed Snapshots* (ACM TOCS 1985); Halpern–Moses common knowledge; Birkhoff
duality (down-sets ↔ distributive lattices); CALM/Hellerstein and Ameloot–Neven–Van den Bussche
(JACM 2013) for the monotone-vs-not boundary; Pradic, *Equational Theory of the Weihrauch Lattice*
(arXiv:2408.14999) for the right-skew. I am confident in the *substance* (what each result says and
why it applies); the years/venues are the spot-check.

**The one genuinely open *technical* question** (not a citation): whether dregg's finality gate
already binds the settlement-time revocation set into the finalized commitment, or whether that bind
must be *added*. If it's already bound, Settlement Soundness (§6.3) is a *composition* of existing
theorems; if not, the bind is a small descriptor/commitment change that comes *first* (a floor under
the proof). I did not verify the finality gate's commitment contents at HEAD — that is the next read,
and it decides whether §6.4 step 4 is "compose" or "extend-then-compose."

---

*( ˘▾˘ ) a closing couplet, since the past turned out to be a lattice we may walk:*

*a branch is free to wander where the causal cone consents —*
*but what gets stored gets settled, and the cap must still hold then.*
