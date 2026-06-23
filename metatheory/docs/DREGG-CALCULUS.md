# The Dregg Calculus

*What kind of computation is dregg? This document names it precisely, to the full depth the
system embodies.*

> **dregg is a *linear capability calculus* whose reduction is a witnessed, attestable, gated
> step over conserved resources — and whose terms range from a single field-write up to a
> forked world, a mergeable document, a channel send, and a desktop surface.**

A "turn" is the one reduction step of this calculus:

> **A turn is the exercise of an attenuable, proof-carrying token over owned, conserved state,
> leaving a verifiable receipt.**

Everything below unpacks that sentence. The core presentation lives in
`Dregg2/Calculus/DreggCalculus.lean` (the headline `Dregg2.Calculus.dregg_calculus`), but the
calculus is *larger* than that one file: the linear substructure, the forest of effects, the
promise sub-calculus, the fork/merge (membrane) calculus, the document calculus, the data-plane
channel calculus, and the witnessed/proven reduction are each their own landed module. This doc
is the map of all of them. Every law is a pointer to a landed theorem or a `def`/`example` that
typechecks; the proved core modules are `#assert_axioms`-clean against
`{propext, Classical.choice, Quot.sound}`.

---

## 0. The shape of the calculus, in one table

| layer | what a *term* is | what a *step* is | home |
|-------|------------------|------------------|------|
| **kernel** | a cell (located bundle of four substances) + a verb | a gated, conserved, attested write | `Exec.EffectsState`, `Substrate.VerbRegistry` |
| **guard** | a `Pred` over the pre-state (caveat / program / precondition / intent) | the precondition that must hold to step | `Exec.Program`, `Calculus.Biorthogonality` |
| **linear** | an asset = its issuer cell carrying −supply | a Σδ=0 exchange (`move`); non-duplicable | `Exec.ReachableConservation`, `Resource` |
| **turn** | a *forest* of effects with delegation edges (granted ≤ held) | the joint commit of the forest | `Substrate.VerbRegistry`, `JointTurn` |
| **promise** | a guarded hole / eventual-ref / conditional batch | a one-shot resumption = a spend | `Await`, `Exec.GuardedHole`, `Exec.ConditionalTurn` |
| **channel** | a named cap-gated inbox / topic (the Bus) | enqueue / wake / drain with receipt-identity | `captp::data_plane` |
| **fork/merge** | a membrane (cap-bounded world-fork) | branch (confined) and stitch (pushout) | `Deos.Membrane`, `Deos.BranchStitch` |
| **document** | a `DocGraph` of atoms + order edges | a patch = a merge with a singleton | `Deos.DocMerge`, `Deos.DocPatch` |
| **witness** | a state, abstractly *or* materialized | abstract progress ⊑ witnessed reduction | `turn::collapse`, `Spec.ExecRefinement` |
| **circuit** | a published commitment + STARK proof | accept ⟹ ∃ genuine kernel transition | `Circuit`, `Circuit.ClosureFinal` |
| **firmament** | one cap across distance (Local / Distributed / Surface) | the same verb at any `n`; n=1 collapses | `Firmament.CapGradation` |
| **settlement** | a finalized tip + a held authority | authority must be *live at the tip* | `Metatheory.SettlementSoundness` |
| **deos** | a room / app / session / membrane / MUD | a fired affordance = a verified turn | `Deos.Surface`, `Deos.Affordance`, `Deos.Reactive` |

The rest of the document takes these in order. The thread is one object seen at many altitudes:
a turn is a forest of conserved, gated writes; that same forest is a promise graph with holes,
a channel send, a world-fork, a document patch — and it carries a proof.

---

## 1. The syntax — a *linear* capability calculus

The term language names the live kernel types.

| calculus notion | dregg type | home |
|-----------------|------------|------|
| cell ≈ process | `Cell := CellId` | `Exec.Kernel` |
| capability ≈ name/channel | `Capability := EffectsAuthority.ECap` (real `List Auth` attenuation lattice) | `Exec.EffectsAuthority` |
| verb shapes (constructors) | `CTerm = create · gwrite · move` | `Calculus.DreggCalculus` |
| guard ≈ typing/precondition | `caveatsAdmit` (the slot-caveat gate) | `Exec.EffectsState` |

### 1.1 The four substances

A cell is a *located bundle of four substances*, and a verb is the structural rule of exactly one
substance's discipline (`Substrate.VerbRegistry.Substance`):

- **value** — *linear*: moves, never copies or vanishes (Σδ = 0, exact);
- **authority** — *non-forgeable*: authorized production, free attenuation, epoch revocation;
- **evidence** — *monotone*: once known, never unknown (the nullifier / commitment ledgers);
- **state** — *guarded-mutable*: changes only under a `Pred`, only by its owner (the frame).

This is why the calculus is *substructural*. The value substance is a linear resource: the
calculus is not a free rewriting system but a discipline of resources that cannot be duplicated or
discarded silently. §3 makes this exact.

### 1.2 The eight verbs — the complete, minimal effect basis

The kernel signature is **eight survivor verbs** (`VerbRegistry.Verb`, the seven constructors
`create · write · move · grant · revoke · shieldUnshield · lifecycle`, with `shieldUnshield`
counting as two directions — `survivorDirectionCount = 8`):

| verb | substance · polarity | the rule it carries |
|------|----------------------|---------------------|
| `create` | birth · introduce | mint a four-substance cell |
| `write` | state · neutral | guarded in-place update under the frame |
| `move` | value · neutral | the Σδ=0 exchange (fees/burn are moves to wells) |
| `grant` | authority · introduce | authorized production along ONE edge (≤ held) |
| `revoke` | authority · eliminate | epoch-narrowing that stales held authority |
| `shieldUnshield` | evidence · introduce | note-create / note-spend (the nullifier) |
| `lifecycle` | retirement · eliminate | seal / unseal / destroy / sovereign custody |

These eight are **independent and complete**:

- **Minimality** — `VerbRegistry.minimality` (`Substrate/VerbRegistry.lean:345`): `verbBehavior`
  is injective on the roster — each verb provides a `(substance, polarity)` no other verb does.
  Drop any one and its behaviour has no provider.
- **Completeness** — `classify_total`: `classify : EffectTag → Classification` is total over the
  live 27-variant `Effect` enum; the Lean compiler's exhaustiveness check *is* the completeness
  proof (a new wire variant that is not classified will not compile).
- **The land-before-kill census** — `no_live_factory_tags`: the 25 historically-deleted variants
  (escrow / obligation / queue / inbox / pubsub / bridge / caps-in-slots) are re-provided as
  verified factory-born cell programs (`FactoryPattern`), the *replication* operator of the
  calculus (`!P`); none survives as a live verb.

### 1.3 The three compressed verbs

Under the universal-map ontology (every substance a sorted-map family), the eight compress to
**three shapes** — the `CTerm` constructors `create · gwrite · move`
(`VerbCompression.compressed_kernel_three`, re-pinned as `verbs_are_three`):

- five verbs (`write / grant / revoke / shieldUnshield / lifecycle`) dissolve into the guarded
  write `gwrite` at a named guard class (`VerbCompression.cfate`);
- `move` separates by *conservation* (not a guard — `gwrite_conservation_trivializes`);
- `create` separates by *arity* (bundle birth — `create_birth_not_single_write`).

The compression is **ontology-relative** (`verb_minimality_is_ontology_relative`): `revoke` and
`lifecycle` share a compressed fate yet are distinct verbs — what survives compression is the
*guard-class stratification* that keeps each dissolved verb's proof obligations alive. So the
syntax has two honest readings: eight independent verbs (the discipline), three compressed shapes
(the executor surface). Both are theorems.

### 1.4 The guard layer — one `Pred` algebra, four polarities

A `gwrite` commits only past its guard. The guard is the typing / precondition layer, and it is
**one predicate language** wearing four hats:

- a **caveat** on a slot (what a write must satisfy);
- a **program** precondition on a cell (`g(x).P`, the input guard);
- a **precondition** demanded by an effect;
- an **intent-demand** (an existential resolver — anyone producing a fill that satisfies `want`).

The deployed atom families index a `GuardModality` — the *type* of a guard, each a pointer to its
live home:

| modality | atom family | home |
|----------|-------------|------|
| `actor` | `SimpleConstraint` (`senderIs` / `balanceGe` / …) | `Exec.Program` |
| `heap` | `HeapAtom` (`heapContains` / `heapGetEq`) + the absence atom | `Substrate.HeapKernel`, `VerbCompression.LitAtom.absent` |
| `temporal` | `TemporalAtom` (`afterHeight` / `withinWindow` / `cooledSince` / …) + UNTIL/SINCE | `Authority.TemporalAlgebra(2)` |
| `epistemic` | `Knows` (K) / `EveryoneKnows` (E) / `DistributedKnows` (D) / `CommonAt` (C) | `Authority.Epistemic` |
| `order` | the rights-order guard `new ⊆ get(k)` (non-amplification) | `VerbCompression.grantGuard` |

That a guard *is* a logical type — not just a boolean check — is a theorem (§4 below): a guard's
admission set is a biorthogonally-closed *behaviour* in Girard's sense.

---

## 2. The reduction relation — `→` *is* the gated step

Reduction is **not a new relation**. The calculus's `→` is the existing executor gate:

```
Reduces s (gwrite actor target f n) s'  ↔  stateStepGuarded s f actor target n = some s'
```

— definitionally (`reduces_iff_step`, an `Iff.rfl`). The calculus reads its operational semantics
straight off the executor; `create` and `move` have their own existing steps
(`recKCreateCell`, `VerbCompression.moveStep`).

Five properties make this reduction **gated, attested, and fail-closed**
(`Dregg2/Calculus/DreggCalculus.lean`):

- **`reduces_admits_guard`** — every reduction certifies its guard held at the pre-state
  (`stateStepGuarded_admits`). The precondition layer is enforced by the executor on each step.
- **`reduces_writes`** — read-after-reduce: after writing `n` to slot `f`, the slot reads back
  exactly `n` (`state_field_written`). The post-state is pinned.
- **`reduces_is_attested`** — **every reduction leaves a receipt.** The receipt chain grows by
  exactly one row per committed step (`state_obsadvance`). The log is a faithful, append-only,
  replay-detectable witness of the reduction sequence — this is what makes the runtime
  *attestable*.
- **`reduces_fail_closed`** — no reduction past a refused guard
  (`stateStepGuarded_caveat_violation_fails`). There is no escape hatch.

The receipt is not decoration: it is the *fourth substance's* (evidence) growth, the channel `Q`
into which observation is emitted, and the object the circuit (§10) and settlement (§11) bind.

---

## 3. The linear / substructural heart — conservation IS linear logic

The value substance makes the calculus *linear*. An **asset is its issuer cell** carrying
−supply: `AssetId := CellId` (`Exec.RecordKernel`), and the books always close.

### 3.1 Conservation is a closed invariant

- **`reachable_total_zero`** (`Exec/ReachableConservation.lean:49`) — **THE value law**: every
  *reachable* state satisfies exact conservation, `Σ_c bal c a = 0` for every asset `a`. Genesis
  is zero-sum; every committed transaction preserves it.
- **`execFullA_conserves_exact`** / **`execFullTurnA_conserves_exact`**
  (`Exec/TurnExecutorFull.lean:2788, :2795`) — every committed action and every committed
  transaction conserves every asset *exactly*. No zero-delta hypothesis is needed: the per-asset
  delta family vanishes identically (`ledgerDeltaAsset_eq_zero`). There is **no non-conserving
  verb left in the kernel**.

### 3.2 Non-duplication and the value/authority unification

At the resource-algebra (camera) tier (`Resource.lean`):

- **`excl_no_dup`** (`Resource.lean:185`) — no exclusive resource composes with itself: an NFT
  cannot be in two places at once (the substructural *contraction*-free law).
- **`conservation_is_fpu`** (`Resource.lean:296`) — conservation *is* a frame-preserving update.
- **`ConfinesAuthority`** (`Resource.lean:319`) — **authority IS conservation**: confinement of
  `held'` by `held` is literally `Fpu held' held` in the resource algebra whose elements are
  capabilities. The value law and the authority-confinement law are *one law* at the camera tier.

### 3.3 The linear logic, recovered from orthogonality

The deepest statement is that the linear face is *literally* a tensor of behaviours (Girard's
transcendental syntax, `Calculus/BiorthTensor.lean`):

- **`conservation_is_behaviour`** (`:280`) — with the composite Σδ pair observable fielded as a
  test, conservation equals its own double-orthogonal `Cons = Cons^⊥⊥`: the linear resource class
  *is* a behaviour.
- **`linearity_recovered_from_orthogonality`** (`:397`) — **THE headline**: (1) conservation is a
  behaviour; (2) it is *exactly* the closure of matched-delta tensors `Δ_k ⊙ Δ_{-k}` (the
  ⊗-decomposition is exact); (3) **no** per-component rectangular test family can carve it — the
  resource law lives *outside* every per-turn testing fragment, at the composite observable. The
  ⊗ of linear logic is recovered from orthogonality *iff* the test side may correlate the paired
  move. This is the precise sense in which the move verb's conservation is the linear ⊗.

So: the guard algebra (§4) is the *additive/multiplicative-with-units* fragment, and conservation
is the genuine linear *tensor* over composite turns. The calculus is linear logic with teeth.

---

## 4. The guard algebra is a *logic* — biorthogonal closure

Each guard's admission set is a behaviour (a biorthogonally-closed type), and the deployed gate
*is* orthogonality (`Calculus/Biorthogonality.lean`):

- **`guard_class_is_biorthogonally_closed`** (`:360`) — for every guard `g` of the literal/order
  family, `Adm(g) = Adm(g)^⊥⊥`: the admission set is its own double-orthogonal — a *type* forced
  by testing, not assembled.
- **`caveatsAdmit_is_orthogonality`** (`:496`, definitional `Iff.rfl`) — **the executor weld**:
  the fail-closed slot discharge `caveatsAdmit` *is*, term for term, membership in the orthogonal
  of the slot's caveat set. The deployed gate and Girard orthogonality are the same function.
- **`reduces_lands_in_behaviour`** (`:508`) — therefore every committed calculus reduction lands
  in a behaviour. Each step is membership in a biorthogonally-closed set.

Guard conjunction is the behaviour meet (`behaviour_meet`), and **attenuation is refutation
growth** (`attenuation_is_refutation_growth`): adding caveats grows the test set and *shrinks* the
behaviour — never amplifies. This is the logical reading of §6's non-amplification.

### 4.1 Coordination-typed modalities — the type is the consensus cost

The novel structural observation: **each guard modality carries a coordination price** — the
I-confluence classification of the invariant it installs
(`Authority.ConfluenceClassifier.guardKeepsConfluence`, named `modality_price`). The *type* of an
operation tells you what consensus it costs.

- **`modality_price_is_tier`** — the price *is* the finality tier
  (`keeps_iff_coordinationFree`): classifying a modality *is* deciding its consensus cost.
- **`modality_price_monotone`** — a **monotone (grow-only) modality runs coordination-free**
  (tier-1, partition-tolerant): the evidence-↑ and monotone-temporal atoms.
- **`modality_price_bounded`** — a **bounded (ceiling) modality forces ordering** (consensus),
  with a *constructive clashing-pair witness* (`bounded_forces_ordering`): the `balance ≥ 0` /
  budget / cardinality atoms. The system tells the app author *why* their guard is not cheap.
- **`modality_price_relational`** — a cross-slot relational modality's price is decided by the
  merge: cheap iff its relation survives the pointwise join.

This connects the guard algebra to the consensus-flex conflict relation: a coordination-free
modality's concurrent turns commute; a forcing modality's do not.

---

## 5. The turn is a *forest* of effects with delegation edges

A single `gwrite` is the workhorse step, but a *turn* is not a flat reduction — it is a **forest
of effects with delegation edges**, jointly committed. Each effect is a located verb; the forest's
edges carry delegation, and **delegation only attenuates**:

- **attenuation ≈ scope restriction with non-amplification** —
  `attenuation_is_scope_restriction` (`introduce_non_amplifying` + `amplifying_grant_rejected`): a
  conferred capability is a genuine *subset* of the held one (granted ≤ held), and the discipline
  has *teeth* — a grant conferring authority the holder lacks is **rejected**. Scope can only
  narrow as a capability flows down a delegation edge.

The joint commit of the forest is atomic and conserving (§3); the n=1 single-machine collapse
(`single_machine_commit_needs_no_binding`, `Deos/ReplayMembrane.lean`) makes a single-cell
forest's atomicity *free* — its own local step — where distributed atomicity needs a binding
premise. The process-calculus dictionary for the non-kernel roles of the forest:

| role | reading | reference |
|------|---------|-----------|
| exercise | communication (send/receive along the cap-as-channel) | `Correspondence .exercise`; `exercise_non_amplifying` |
| pipelining | asynchronous communication / promise (§7) | `Correspondence .pipelining` |
| factory | replication `!P` | `factory_is_replication` |
| program | input guard `g(x).P` (§1.4) | the guard layer, enforced by `caveatsAdmit` |
| prologue | replay-nonce freshness | `Correspondence .prologue` |
| refusal | negative outcome (proof of non-action) | `Correspondence .refusal` |
| receiptLog | observation into the attestation channel `Q` | `Correspondence .receiptLog` |

---

## 6. The promise sub-calculus — partial turns, holes, pipelining

The reduction extends to *partial* turns: effects with holes, promises, and eventual references.
The unifying insight: **a promise-hole is a nullifier; its resolution is a spend; one-shot
linearity is the double-spend non-membership the circuit already enforces.**

### 6.1 The Await algebra — one-shot continuations

`Dregg2/Await.lean` gives the turn as a Plotkin–Pretnar handler over operations `await · call ·
emit`. The key is **`OneShot`** (`Await.lean:103`): a continuation wrapped use-exactly-once, with
*no* duplicator `OneShot → OneShot × OneShot`; its sole eliminator `OneShot.resume` *consumes* it.
Linearity is a **type-level** invariant, not a runtime flag (`one_shot_is_static`) — a runtime
"resumed" boolean admits the double-spend window (`runtime_guard_is_double_spend`), but a second
`OneShot.resume` is *inexpressible*.

- **`commit_resumes_once`** — the turn-as-rollback-handler resumes the continuation exactly once
  on commit; **`rollback_discards_continuation`** uses it zero times on abort (refund). Two legal
  affine uses only.
- **`four_faces_unify`** (`Await.lean`) — `zkpromise` (resolution witnessed by a ZK proof),
  `discharge` (a gateway presenting a discharging witness), and `intent` (an existential resolver)
  all extract to one `AwaitCore p k`. The four faces are interconvertible *views* of one promise
  primitive. The spec (`Spec/Await.lean`) decomposes await orthogonally into a temporal half
  (`conditional_is_temporal_guard` — a third-party caveat deferred over a clock) and a dataflow
  half (the promise graph).

### 6.2 Guarded holes — the genuinely-new keystone

A `GuardedHole` (`Exec/GuardedHole.lean`) is a late-filled slot carrying predicate caveats: the
*shape* is fixed eagerly, the *value* arrives lazily.

- **`holeFill_binds_in_circuit`** (`GuardedHole.lean:59`) — **THE KEYSTONE**: a successful fill
  binds *both* legs into the post-state — its δ (the effect actually committed) *and* its guard
  (every promised `PredCaveat` discharged). A hole cannot be filled without committing the effect
  *and* discharging the predicate it promised.
- **`holeFill_rejects_guard_violation`** (`:67`) — the negative tooth: a value violating the
  hole's guard does not fill (fail-closed). The late witness cannot escape the eager shape.

### 6.3 Conditional batches and CapTP pipelining

- **`ConditionalBatch`** (`Exec/ConditionalTurn.lean`) — a turn batch with dependency edges, Kahn
  topologically ordered, executed all-or-nothing through the `Option` monad
  (`execConditionalTurn`): `condTurn_atomic` (failure leaves input unchanged),
  `condTurn_dependency_sound` (a consumer never reads an unresolved slot — the `EventualRef`
  model). This is the local, finite, computable case of the await algebra.
- **CapTP pipelining** (`Exec/CapTPPipeline.lean`) — queued sends drained in FIFO through the
  *verified executor*, which **re-checks authority at delivery**:
  - **`drainAll_preserves_caps`** (`:129`) — pipelining cannot grow the capability table; it is a
    pure latency win, never an authority bypass.
  - **`overAuthorized_send_rejected`** (`:172`) — the anti-ghost tooth: a forged/over-authorized
    queued send is rejected on drain. Authority is re-witnessed at execution, not queue time.
  - **`break_freezes_state`** (`:197`) — a broken promise leaves the state unchanged; no orphaned
    grant survives. (Broken promises cascade transitively in the Rust `pending` registry.)

The Rust realization (`turn/src/{eventual,conditional,pending}.rs`) carries the engineering: an
`EventualRef` keyed by `(source_turn, output_slot)`, a `ProofCondition` (hash-preimage / STARK /
receipt) with a **proof nullifier** preventing reuse (a proof can only be spent once), and a
deposit that prices griefing.

---

## 7. The channel sub-calculus — the data plane (the Bus)

The π-calculus / channel layer is the **captp data plane** (`captp/src/data_plane.rs`), one
unified `Bus` object backing real channel comms (used in production by
`node/src/channels_service.rs`):

- a **`SendCap`** is a cap-gated edge into a named inbox; **`Bus::enqueue`** admits a send *iff*
  the cap allows it — an over-attenuated or revoked send is **refused before queuing** (no
  message, no receipt — no phantom work; the non-amplification tooth at the channel layer);
- **receipt-identity**: a `Delivery` separates "queued" (a signed `CustodyReceipt`, a *promise*)
  from "handled" (a content hash in the authenticated delivered-witness log, a *witness*).
  `is_handled` reads the witness log, never the promise — the structural flip from queued to
  handled is observable end to end (the adjudicator acquits an honest relay, convicts a drop past
  deadline);
- **unforgeable wake**: a `Waker` cursor advances *only* on an admitted enqueue (`tick` is the
  sole setter); `poll` is a cursor-derived idempotent read — a subscriber cannot forge a wake;
- **pub/sub is iterated unicast**: `publish` fans a payload to each subscriber's inbox as
  independent enqueues, each with its own receipt; unauthorized subscribers are skipped.

This is the comms/concurrency face of the calculus: cells exchange messages along cap-as-channel
edges, every send gated by the same attenuation lattice, every delivery witnessed.

---

## 8. The fork/merge calculus — the membrane (branch-and-stitch)

The calculus has terms for *forking* and *merging worlds*. A **membrane** is a cap-bounded
world-fork; virtualization is branching, and the laws make it safe by construction.

### 8.1 The membrane is iterated attenuation

`Deos/Membrane.lean`: a `hop keep cap := attenuate keep cap` is a per-viewer projection; a
`reshare` is a composition A→B→C.

- **`reshareN_attenuates`** (`Membrane.lean:122`) — any chain of membrane reshares confers a
  *subset* of the original held authority (induction over hops). Confinement survives
  arbitrarily-long reacquisition chains.
- **`reshare_refuses_amplification`** (`:145`) — the negative tooth: a hop that names an authority
  a prior hop dropped cannot manufacture it. (And `negotiate_preserves_target` /
  `deputy_confers_no_unheld_target` in `ReplayMembrane.lean` make the confused-deputy attack
  *structurally absent*: authority and designation are the same object, so a request cannot
  retarget a cap.)

### 8.2 Nesting IS confinement-safety

`Deos/BranchStitch.lean`, Part A: a branch author is `BranchHonest` (capability-confined away from
the MAIN frontier `M`).

- **`branch_cannot_drain_main`** (`BranchStitch.lean:110`) — **KEYSTONE A**: a confined author
  cannot commit any turn that debits a main cell; the kernel `authorizedB` gate refuses it. All
  destructive experiments in a branch are structurally imaginary *as a cap fact*.
- **`branch_in_branch_cannot_drain`** — nesting composes: a branch-in-branch is another stratum
  down the cap-tower; the no-drain tooth holds at every level (the firmament mechanism, §9).
- **`branch_may_signal_main`** — confinement confines *draining* (integrity), not *information*:
  the residual deposit/timing channels are *named*, not laundered.

### 8.3 Stitch IS pushout-correctness, lossy drops explicit

`BranchStitch.lean`, Part B: a `Stitch m b s` holds iff `s` is the pushout (least upper bound) of
the branch graph `b` into the main graph `m`.

- **`stitch_is_pushout`** (`:241`) — **KEYSTONE B**: `merge m b` *is* the pushout — nothing main
  had is silently lost, nothing the branch found is dropped without an explicit drop, no value is
  conjured (leastness). The I-confluent part auto-merges (`stitch_iconfluent_clean`); genuine
  conflicts are forced by a constructive clashing pair (`stitch_conflict_escalates`).
- **`stitch_drop_explicit`** / **`stitch_drop_strict_loss`** — when conservation / authority /
  nullifier collisions forbid the merge, the author's drop (`restrict K`) is *explicit* and can
  only lose, never conjure (`stitch_drop_is_below`). Lossiness is opt-in (linear logic forces
  visible loss); dropping nothing recovers the clean merge.
- **`contained_branch_one_door`** (`:411`) — the integration: a branch is contained (it can do
  nothing to main) *and* the pushout is the one sound door back.

The Rust realization (`starbridge-v2/src/shared_fork.rs`, `deos-matrix/src/membrane.rs`) makes a
chat *message* a cap-bounded world-fork: a `SharedFork` graduates the publisher's authority into
EMBEDDED (full grant) / STUDYREF (read-only) / NETWORKBOUNDARY (consent-gated) tiers; a
`MembraneEnvelope` carries a frustum-culled, authority-bounded snapshot inert until rehydrated;
conflicts surface as first-class `ConflictObject`s (`ConservationCollision` / `NullifierCollision`
/ `AuthorityRevoked` / `CapAmplification`). The boundary exercise is fail-closed and one-shot
(`verify_consent_witness`: binding, one-shot nullifier, authenticity).

---

## 9. The document calculus — Pijul-shaped patches

A *document* is a `DocGraph` (atoms + order edges + fields), and its patches form the **same
event-structure object** as the turn layer. `Deos/DocMerge.lean` + `Deos/DocPatch.lean`:

- **the merge is a lattice join** — `merge_comm` / `merge_assoc` / `merge_idem` / `merge_total`:
  every fork has a merge, order- and bracket-independent, idempotent; **`merge_is_lub`**
  (`DocMerge.lean:348`) is the universal property (the colimit-by-union the pushout computes).
- **conflict is a first-class *state*, not a failure** — `ConflictAt` is a transitive antichain
  (two live atoms mutually unreachable from a shared predecessor); `merge_has_conflict`
  (`:450`) exhibits a concrete conflict that is a *well-formed* `DocGraph`; resolution is an
  additive `Connect` edge that collapses it monotonically (`resolve_collapses`).
- **patches are monotone and commute** — `addAtom_inflationary` / `addEdge_inflationary` /
  `tombstone_inflationary` (every op, even tombstone, only grows in `⊑`); independent ops commute
  (`addAtom_addAtom_comm`, …), and the disjoint boundary is precise (`addAtom_tombstone_comm`
  needs `i ≠ j`).
- **apply IS merge** — `addEdge_is_merge` (`DocPatch.lean:271`): applying a patch op *is* merging
  in a singleton graph; `addEdge_commutes_via_merge` re-derives op-commutation from `merge_assoc`
  / `merge_comm`. Patch theory is the lattice join in disguise — the same object as the membrane
  stitch (§8) and the turn forest (§5).

The Rust core (`dregg-doc/`) realizes this: a `DocGraph` of `Status::{Alive,Dead}` atoms (Dead
wins under the pointwise join), `Op::{Add,Delete,Connect,SetField}`, and a conflict-viewer that
surfaces antichains as `Segment::Conflict` for prose resolution.

---

## 10. The witnessed reduction — symbolic/collapse and the circuit

The reduction has two altitudes: the **abstract semantics** and the **witnessed materialization**.

### 10.1 Symbolic vs. full — `Exec ⊑ Abstract`

`turn/src/collapse.rs`: a `WitnessMode` is `Full` (Merkle witnesses materialized eagerly) or
`Symbolic` (witness deferred, carrying the `DEFERRED_STATE_HASH` sentinel). The abstract state
`(balanceTotal, authGraph)` is proved witness-free in `Spec/ExecRefinement.lean` (`Exec ⊑
Abstract`). Symbolic defers *only the witness*, **never a decision**: every legality gate (STARK,
conservation, authority/no-amplification, nonce/fee) runs identically in both modes. `collapse`
re-runs recorded symbolic turns through full execution to reproduce byte-identical receipts. The
reduction is the same; only the proof artifact's timing differs.

### 10.2 The circuit — every step carries a STARK proof

`Dregg2/Circuit.lean` encodes the kernel's step-invariant conjuncts as arithmetic constraints
(`cConservation` Σδ=0, `cAuthority` authorized, `cChainLink` log extends by the turn,
`cObsAdvance` receipt length +1):

- **`bridge`** (`Circuit.lean:212`) — the constraint system is sound *and* complete: satisfying
  `kernelCircuit` on an encoded `(s, t, s')` is *exactly* the verified step invariant
  `fullStepInv`.
- **`lightclient_unfoolable_circuit_sound`** (`Circuit/ClosureFinal.lean:161`) — **the headline**:
  from a STARK batch that verifies against `vkOfRegistry Rfix` (under the named crypto floors —
  `StarkSound`, `Poseidon2SpongeCR`, and a single parametric `ClosedWitness`), there *exist*
  decoded endpoints `pre post` and a **genuine kernel transition** `kstepAll pi.effect pre post`
  whose commitments match the published inputs. **verifyBatch accept ⟹ ∃ genuine kernel
  transition** — the circuit never accepts a forged turn. (`…_of_readouts` builds the witness
  floor from the genuine readout bundle, so the soundness rungs are load-bearing, not vacuous.)

This is the precise sense in which **the reduction is proven**: a light client that checks the
proof cannot be fooled into accepting a transition the kernel would not have made.

---

## 11. The firmament and settlement — one cap across distance, sound at the tip

### 11.1 The firmament — confinement as a distance-parametrized operation

`Firmament/CapGradation.lean`: one `Capability { target, rights }` over a `Target` that is `local`
(seL4 CNode slot), `distributed` (a federation cell), or `surface` (a cell as a window) — **one
semantics across three backings**. A distance `n` slides the bounds (immediate↔eventual
revocation, synchronous↔quorum commit) but **not the verbs** (`verbs_independent_of_n`); the
attenuation gate is backing-agnostic (`attenuate_decision_backing_agnostic`).

- **`distributed_collapses_at_one`** (`:379`) — at n=1, `Bounds.distributed 1 =
  Bounds.strongLocal`: immediate revocation + synchronous commit. The single-machine principle.
- **`surface_is_another_point_on_n`** (`:484`) — a desktop surface is the distributed case viewed
  through glass: same backing, gate, and bounds. A window is a cap, no more.

### 11.2 Settlement soundness — authority live at the tip

Revocation is the one non-monotone operation, so authority must be evaluated at the *settlement
coordinate*, not the stale branch view (`Metatheory/SettlementSoundness.lean`):

- **`settlement_soundness`** (`SettlementSoundness.lean:153`) — a settled authority is **live at
  the tip** (`LiveAtTip`, `:108`): held as an attenuation *and* its credential honored by the
  finalized revocation set at the tip. A cap revoked between branch and settlement forecloses the
  stitch (`revoke_before_tip_unsettleable`), fail-closed. At n=1 the propagation window vanishes
  (`revoke_unsettleable_immediate`) — settlement-time authority *is* branch-time authority.

The circuit version (`Dregg2/Circuit/SettlementSoundness.lean`) composes this with §10's genuine
transition: **accept ⟹ a genuine transition whose authority was live at the settlement tip** —
closing the distributed time-travel hole the membrane (§8) opens.

---

## 12. Flow-algebra — the reactive shadow (right-skew)

The calculus's workflow composition is a *right-skewed* Kleene algebra (`Deos/FlowAlgebra.lean`):
choice `⊔` does **not** left-distribute over compose `⋆`.

- **`flow_choice_halfdistrib`** (`FlowAlgebra.lean:339`) — the half always holds:
  `(P ⋆ R) ⊔ (Q ⋆ R) ≤ (P ⊔ Q) ⋆ R` in the online-simulation order.
- **`flow_choice_right_skewed`** (`:467`) — **the headline**: the converse *fails*. The two sides
  recognize the same trace language yet are separated by an *online step-by-step* simulation — the
  late branch (after R's move) keeps both continuations open; the early branch has already
  committed, and a simulator cannot match without lookahead. This is the algebraic shadow of the
  *reactive rung*: dregg semantics is an online simulation, not a trace language.

The payoff is **decidable flow/policy refinement** (`Deos/FlowRefine.lean`, `decideRefines`): the
right-skew is the precondition for a Büchi/simulation-game decision procedure for `A ≤ᶠ B`.

---

## 13. How deos reads in the calculus — the desktop is the calculus made interactive

deos is not a separate system layered on the calculus; **its surfaces, sessions, rooms, and
membranes are calculus terms**, and the desktop is the reduction made tangible.

| calculus | deos | reference |
|----------|------|-----------|
| cell | a room / app / document | `Deos/Surface.lean`, `DREGG-MUD.md` |
| cap (endpoint) | a surface (window) | `Surface.lean:61` |
| turn | a fired affordance / action / message | `Deos/Affordance.lean`, `Deos/Reactive.lean` |
| attenuation | a membrane reshare / projection | `Deos/Membrane.lean` |
| receipt chain | provenance / interaction log | `Deos/Rehydration.lean` |
| membrane | a chat message carrying a world-fork | `deos-matrix/src/membrane.rs` |
| session | a cap-rooted subgraph | `DREGG-MUD.md` |

- **A surface IS a capability.** `Surface cell rights := Cap.endpoint cell rights`
  (`Surface.lean:61`): a window confers *exactly* its rights and nothing more
  (`surfaceConfersExactly`) — the desktop adds zero new trust. A read-only window confers no
  connectivity edge; an interactive one does (`viewSurface_confers_no_edge` vs.
  `interactiveSurface_confers_edge`) — the distinction is real.
- **An affordance IS a cap-gated verified turn.** `fire_authorized_iff` (`Affordance.lean:167`):
  an agent fires only the affordances its caps authorize, fail-closed. A button on the surface is
  a turn you may fire iff your cap-tree authorizes it — the same authority gate the kernel proves.
- **A reactive affordance IS a turn gated by transition-shape and clock.** `fireReactive_iff`
  (`Reactive.lean:199`): a fire commits iff the cap-gate, the transition-gate (pre/post/link reads
  *both* old and new), *and* the window-gate all pass. A button that lights during a voting window
  and darkens at the deadline is a turn with a temporal guard; two viewers at equal authority but
  different witness-graph projections see distinct surfaces (`membrane_two_viewers_distinct`).
- **A session IS a cap-rooted subgraph; a room IS a cell; an item IS a cap.** (`DREGG-MUD.md`,
  `starbridge-v2/src/mud.rs`.) Login derives the identity cell and grants the initial cap set; the
  session *is* the resulting c-list — there is no player object kept in sync, only the c-list and
  the world rendered to exactly what it authorizes. Logout is `RevokeCapability` over the session
  root: the whole tree goes dark, synchronous and transitive. An exit is a cap edge; a locked door
  is the absence of a cap; the key is the cap. A MUD is a *view over the cell calculus*.
- **A rehydrated context IS a turn history.** `replayedDeterministic_iff_confined`
  (`Rehydration.lean:161`): for a non-live context, the liveness-type is *exactly* the confined
  fragment — `ReplayedDeterministic` iff every interaction stayed inside the membrane (was an
  attested turn). The honesty label *is* a proven confinement readout.

So the desktop's every window is a cap to a cell, every message a turn through the executor, every
screenshot/fork a cap-bounded membrane, every drag-into-chat a reshare (proven non-amplifying).
You cannot cheat the surface because the substrate has already proved the properties — verb
minimality, non-amplification, conservation, confinement, affordance soundness — you would have to
violate.

---

## 14. The headline, assembled

`Dregg2.Calculus.dregg_calculus` assembles the kernel core over a concrete reduction
`hr : Reduces s (gwrite …) s'`: the syntax has exactly the three compressed verbs
(`verbs_are_three`); the reduction **is** the gated step and emits exactly one receipt row
(`reduces_iff_step` + `reduces_is_attested`); and a guard modality's price is its finality tier
with both poles inhabited (a monotone modality runs free; a bounded modality forces ordering with
a constructive witness). Assembled from cited theorems — not a new axiom.

Read with the full depth above, the one-line claim is:

> **dregg is a linear capability calculus (eight independent verbs, three compressed shapes) whose
> guards are biorthogonal behaviours, whose value substance is the linear tensor, whose turn is a
> conserved forest of attenuating effects extensible to promises, channels, world-forks, and
> documents — and whose reduction is gated, attested, witnessed by a STARK proof, sound at the
> settlement tip, and made interactive as the deos desktop.**

---

## Honesty ledger — proved vs. documented-structural

This doc names the calculus to its real depth. Not every depth is at the same proof maturity; the
ledger is explicit.

**Proved, axiom-clean (assembled from cited keystones):**

- *kernel/reduction* — `reduces_iff_step`, `reduces_admits_guard`, `reduces_is_attested`,
  `reduces_writes`, `reduces_fail_closed`, `verbs_are_three`, `dregg_calculus`,
  `attenuation_is_scope_restriction`, the modality-pricing laws (`modality_price_is_tier`,
  `…_monotone`, `…_bounded`, `…_relational`).
- *verbs* — `VerbRegistry.minimality`, `classify_total`, `no_live_factory_tags`,
  `VerbCompression.compressed_kernel_three`, `verb_minimality_is_ontology_relative`.
- *linear core* — `reachable_total_zero`, `execFullA_conserves_exact`,
  `execFullTurnA_conserves_exact`, `excl_no_dup`, `conservation_is_fpu`,
  `conservation_is_behaviour`, `linearity_recovered_from_orthogonality`.
- *guard logic* — `guard_class_is_biorthogonally_closed`, `caveatsAdmit_is_orthogonality`,
  `reduces_lands_in_behaviour`, `attenuation_is_refutation_growth`.
- *promises* — `commit_resumes_once`, `rollback_discards_continuation`, `four_faces_unify`,
  `holeFill_binds_in_circuit`, `holeFill_rejects_guard_violation`, `condTurn_atomic`,
  `condTurn_dependency_sound`, `drainAll_preserves_caps`, `overAuthorized_send_rejected`,
  `break_freezes_state`.
- *fork/merge* — `reshareN_attenuates`, `reshare_refuses_amplification`,
  `branch_cannot_drain_main`, `branch_in_branch_cannot_drain`, `stitch_is_pushout`,
  `stitch_drop_explicit`, `stitch_drop_strict_loss`, `contained_branch_one_door`,
  `negotiate_preserves_target`, `deputy_confers_no_unheld_target`.
- *document* — `merge_is_lub`, `merge_has_conflict`, `addEdge_is_merge`, `tombstone_inflationary`,
  the op-commutation laws.
- *witnessed/proven* — `bridge`, `lightclient_unfoolable_circuit_sound`
  (under named crypto floors `StarkSound` / `Poseidon2SpongeCR` / `ClosedWitness`),
  `settlement_soundness`, `LiveAtTip`, `revoke_before_tip_unsettleable`.
- *firmament/flow* — `distributed_collapses_at_one`, `surface_is_another_point_on_n`,
  `verbs_independent_of_n`, `flow_choice_halfdistrib`, `flow_choice_right_skewed`.
- *deos* — `surfaceConfersExactly`, `fire_authorized_iff`, `fireReactive_iff`,
  `membrane_two_viewers_distinct`, `replayedDeterministic_iff_confined`.

**Structural `def`/`example` (typechecks; the correspondence is a naming, not a separate
theorem):** `Cell`, `Capability`, `CTerm`, `GuardModality`, the π-calculus `Correspondence` table,
`factory_is_replication`, the program-as-input-guard `example`, the §0/§13 layer tables.

**Rust realization (engineering; the *laws* are the Lean theorems above, the Rust is the deployed
mechanism):** `turn/src/{collapse,eventual,conditional,pending}.rs`, `captp/src/data_plane.rs`,
`node/src/channels_service.rs`, `dregg-doc/`, `starbridge-v2/src/{shared_fork,mud}.rs`,
`deos-matrix/src/membrane.rs`. These are cited by file (not file:line) and are the runtime image
the Lean refines, not separate proofs.

**Named crypto / out-of-band floors (terminal, by design):** `StarkSound` (the proof system's
soundness), `Poseidon2SpongeCR` (hash collision-resistance), the `ClosedWitness` parametric
floor. These are the irreducible assumptions on which §10–§11 stand; everything else reduces to
the three kernel axioms.
