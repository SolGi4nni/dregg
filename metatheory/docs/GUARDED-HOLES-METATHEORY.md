# Guarded Holes — a categorical / metalogical analysis, and a system-coherence audit

**Status: design study, not a build.** This document studies ember's "guarded hole" idea for its
bearing on dregg's existing metatheory. Every structural claim is grounded in a named file; where a
claim is a conjecture it is **labelled SPECULATION**. No code is changed by this document, and it does
not assert that any guarded-hole construct is currently proven — only what it *would* instantiate or
require.

**Verdict, up front (added after a deeper system read — see §8).** The first pass below (§§1–7) is a
*categorical/metalogical* analysis and it largely survives: the guard, the meet, the witness-discharge,
the right-skew placement are all faithfully placed against existing objects. But it answered the wrong
question. It studied a guarded hole as a **dataflow slot between fully-specified contributions** —
because that is *exactly* what dregg's existing `EventualRef`/`Slots`/`Promise` machinery is. ember's
sharper question is whether a hole can sit in a *conservation-* or *authority-bearing* position — a
**missing contribution** whose delta and authority are not yet determined. Traced through the
conservation keystone, the authority gate, the joint-turn machinery, and the light-client proof model,
the answer is: **dregg's holes are deliberately NOT of that kind, and making them so is not a small
extension — it is the move the construction was built to forbid.** §8 names this precisely. The honest
verdict is **(c): the guarded-hole idea, in its strong "missing conservation/authority contribution"
reading, EXPOSES the boundary the current construction enforces** — not a bug *in* dregg, but a
sharp statement of what dregg's all-or-nothing / fully-specified-node discipline is *for*. In its weak
"dataflow slot + late predicate" reading it is **(a): it composes cleanly and is mostly already code.**
The two readings are different constructs and the value is in keeping them apart.

## 0. The idea, restated against the code

A **partial turn with holes** already exists, two ways:

- `Dregg2.Exec.ConditionalTurn.ConditionalBatch { nodes, edges }`
  (`Dregg2/Exec/ConditionalTurn.lean:82`) — a DAG of turns plus `edges : List (Nat × Nat)` where
  `(consumer, producer)` is an `EventualRef`: a **hole** the producer fills and the consumer reads.
  The hole's fill-state is the slot environment `Slots : Nat → Bool`
  (`ConditionalTurn.lean:101`), with `Slots.fill` the producer-commit forward step and `Slots.fill_mono`
  the monotonicity of forwarding (`:113`).
- `Dregg2.Spec.Await` (`Dregg2/Spec/Await.lean`) factors the same family into
  `Conditional ⊕ Promise`: the `Promise`/`EventualRef` is the dataflow hole (`Spec/Await.lean:253`),
  the `Conditional` is a third-party guard deferred over a `Height` (`:95`), and `PromiseGraph`
  (`:266`) is the DAG of holes.

The hole-filling is `Await.Op.await` resumed exactly once by the rollback handler
(`Dregg2/Await.lean`): `commit_resumes_once` (`Await.lean:260`) and
`rollback_discards_continuation` (`Await.lean:246`), over the **one-shot / linear** continuation
`OneShot` (`Await.lean:85`). This linearity is load-bearing below.

ember's specific extension: a participant attaches a **predicate to a hole** that a future filler must
**discharge before they may fill that hole a certain way**; multiple parties may accumulate/refine the
guards over the structure's lifetime. The predicate vocabulary already exists:
`Exec.PredAlgebra.Pred` (`Dregg2/Exec/PredAlgebra.lean:127`) — a genuine Boolean algebra over the
transition `(old, new)` with decidable, fail-closed `Pred.eval` (`:190`) — and the
attenuation/caveat layer `Authority.Caveat` (`Dregg2/Authority/Caveat.lean`) with
`attenuate_narrows` (`Caveat.lean:84`).

So a **guarded hole** is the pair

> `(hole : EventualRef/slot)  +  (guard : Pred)`  such that a fill is admissible only when the guard
> is discharged on the fill.

The rest of this document asks: what is that, categorically, and what does it touch?

---

## 1. What IS a guarded hole, categorically?

I evaluate the five candidates the brief names against the actual `Slots`/`EventualRef`/`Pred` code.

### 1a. A refinement / subobject of the slot type — **best fit for the static face.**

`Pred.eval g : Value → Value → Bool` (`PredAlgebra.lean:190`) is a decidable predicate on the
transition `(old, new)`. Its extension `{ (o,n) | g.eval o n = true }` is a **subobject** of the slot's
transition type `Value × Value`. A guard *carves out the admissible fills*: filling the hole "a certain
way" = landing the `new` value inside this subobject. The executor already realizes exactly this as a
**domain restrictor that never mutates**: `predStateStepGuarded` (`PredAlgebra.lean:580`) commits
*exactly* `stateStep`'s post-state when `predCaveatsAdmit` holds and `none` otherwise
(`predStateStepGuarded_eq`, `:591`; `predStateStepGuarded_violation_fails`, `:615`). That "only
restricts the domain, never changes the post-state" property is *precisely* the categorical signature
of a **monomorphism / subobject inclusion** on the fill type, not a general morphism.

Verdict: a guarded hole's **guard** is a subobject of the slot's transition object; the **fill** is a
section that must factor through that subobject (§1b). This is the cleanest and most defensible
identification, and it is already code (`predStateStepGuarded`).

### 1b. A section of a bundle over the predicate's extension — **best fit for the dynamic face.**

The hole itself (an `EventualRef p`) is a request for a value produced later. Filling it is providing
the value; `Slots.fill i` records the production (`ConditionalTurn.lean:107`). Combine with §1a: a
*guarded* fill is a **partial section** of the slot bundle that is *defined only over the guard's
extension* — i.e. a section of the restricted bundle `slot ↾ {guard holds}`. The dependency-soundness
theorems make this faithful: `condTurn_dependency_sound` (`ConditionalTurn.lean:407`) +
`runOrder_fills` (`:333`) prove a consumer never reads an unfilled slot, so the "section" is genuinely
total over the *resolved* sub-DAG and undefined elsewhere. The producer-commit ↔ handler-commit bridge
`forward_is_handler_commit` (`ConditionalTurn.lean:602`) ties the fill to `OneShot.resume` — the
section is *installed once*.

### 1c. A metavariable-with-a-constraint (contextual modal type theory) — **best fit for the metalogic.**

This is the right reading of the *propagation* the brief emphasizes ("a predicate a future participant
must discharge"). A hole is a metavariable; its guard is a constraint that travels with the metavariable
into every future fill-context. In contextual modal type theory (Nanevski–Pfenning–Pientka, *Contextual
Modal Type Theory*, TOCL 2008) a metavariable `u :: (Ψ ⊢ A)` carries its context `Ψ`; the boxed
`□(Ψ ⊢ A)` reading is "`A` derivable in *every* extension of `Ψ`". The guard `g` on a hole is exactly a
`Ψ`-resident obligation: a filler in a future context `Ψ' ⊇ Ψ` may instantiate the metavariable only by
*also* supplying a derivation of `g`. The "discharge before you may fill" is the metavariable
substitution side-condition. See §5 for why this is the load-bearing metalogical identity, and where
the `□` modality is genuine vs. cosmetic.

### 1d. A representable functor restricted by a sieve — **partial fit, the temporal face.**

A sieve on the deadline poset models "fills allowed up to height `d`". The `Conditional`'s deadline gate
(`Spec/Await.lean:136`, `resolve` returns `Resolved` iff the gateway discharged AND `height ≤ deadline`)
is literally a sieve-style cutoff on the `Height` linear order. But this only captures the *temporal*
half of the guard, not the predicate-on-the-fill half. It is a faithful description of `Conditional`,
not of the `Pred`-guard. Use it for the deadline coordinate only.

### 1e. A comma / Kan object — **not a fit; over-reach.** Nothing in `Slots`/`Pred` supplies the
universal-property data a comma or Kan object needs (no functor pair being compared, no left/right
extension). Cataloguing it as such would be manufactured elegance. Reject.

> **Identity (the honest composite).** A guarded hole is a **constrained metavariable** (§1c, the
> metalogic) whose constraint is a **subobject of the slot's transition type** (§1a, already
> `predStateStepGuarded`) and whose fill is a **once-installed partial section** of the slot bundle over
> that subobject (§1b, already `Slots.fill` + `forward_is_handler_commit`), optionally cut by a
> **deadline sieve** (§1d, already `Conditional.resolve`). Three of the four pieces are *already code*;
> only the metavariable-propagation framing (§1c) is new vocabulary over existing objects.

---

## 2. The hyperdoctrine bearing

dregg's `Pred` algebra plausibly *are* fibres of a hyperdoctrine over contexts, and the repo already
builds the hyperdoctrine: `Dregg2.Metatheory.Lawvere` proves the full posetal triple
`∃_f ⊣ f* ⊣ ∀_f` (`Lawvere.lean:112`, `lawvere_triple`), Frobenius (`:134`), Beck–Chevalley (`:175`),
and the Byzantine relational form `∃_R ⊣ ∀_R` (`Lawvere.lean:323`). The base/`Predicate ⊣ Witness`
reading is `Metatheory.Disputation` and `Authority.Predicate` (the registry's `Verify` seam,
`Predicate.lean:99` `registry_sound`).

### 2a. Filling = the `∃ ⊣ Witness` unit at a hole. **Expressible — this one fits cleanly.**

Filling a guarded hole is "providing a witness that the guard holds". The repo's witness-discharge
seam is exactly this: `Discharged ctx w` = `registryVerify … = true` (`Predicate.lean:88`), and
`registry_sound` (`:99`) says an accepted witness *discharges* the predicate. Read through the
hyperdoctrine: the guard `g` is a fibre element (a `Pred` over the fill-context); the fill provides a
point of its extension; that point is the **counit/unit of `∃ ⊣ f*`** localized at the slot — "there
exists a fill in the guard's extension" is `∃` applied to the slot, and supplying the actual fill is
the adjunction witness. The `intent.Fires` definition is literally this existential:
`∃ w, Discharged i.want w` (`Await.lean:325`). So **"discharge before fill" = the existential side of
`Predicate ⊣ Witness` localized at a hole** — and it is already a theorem-bearing seam, not new.

### 2b. Multiparty accumulation of guards = MEET in the fibre. **Expressible — and it is the existing `⋀`.**

When several parties each attach a guard to the same hole, the hole becomes admissible only when *all*
guards hold. That is the **meet** in the predicate fibre. The repo has it two ways that *agree*:
`Token.admits = caveats.all (…)` is the conjunction `⋀` (`Caveat.lean:71`), and
`Pred.allOf` / `Pred.and` is the Boolean meet (`PredAlgebra.lean:197`, `:271`). `attenuate_narrows`
(`Caveat.lean:84`) proves appending a guard can only *shrink* the admissible set — i.e. guard
accumulation is **monotone decreasing in the fibre order**, which is exactly meet behaviour. So
multiparty guard accumulation = `⋀` of fibre elements, and `attenuate_subset` (`Caveat.lean:92`) is the
proof that more guards ⊆ fewer guards.

Is this the "agreement = limit" of the adjunction thesis? **Partially, and the distinction matters.**
The adjunction-thesis verdict (`project-adjunction-thesis-verdict.md`) established: agreement = the
meet/limit `DistKnows = ⋂ ∼_a`, and that meet is a *limit in the fibre*. Guard accumulation is a meet
**in the same fibre poset**, so it is the *same kind of object* as "agreement = limit." But it is **not
the epistemic agreement meet** — guard accumulation is parties *adding constraints to one shared
object*, whereas the epistemic meet is *intersecting agents' knowledge*. They coincide as "meet in a
Heyting/Boolean fibre"; they differ in *what is being met* (constraints-on-a-hole vs.
knowledge-of-agents). Honest statement: guard accumulation **instantiates the fibre-meet structure the
hyperdoctrine already names**, and is the *constraint-side* analogue of the *knowledge-side* "agreement
= limit." Calling them literally the same theorem would be overclaiming.

### 2c. Does it touch the graded `∃ ⊣ q* ⊣ ∀` or the adjudication reflector?

- The **graded `∀_a`** (`Lawvere.lean` Part B, `relForall`) is the box/Knows modality. A guard that says
  "*P* must hold in *all* future fill-contexts" (the `□P` of §1c/§5) is a `∀`-quantification along the
  future-context relation — i.e. it lands in the `∀_R` fibre, the right adjoint. This is the one place a
  guarded hole reaches past the existing *posetal* Set-doctrine into the **relational** Part B box.
  Crucially, Part B already proves the box is well-behaved only up to the relation's structure:
  `relForall_idem_of_preorder` (`Lawvere.lean:411`) gives S4 idempotence for a preorder, and
  `box_box_ne_box` (`:486`) shows it FAILS for a Byzantine (reflexive-non-transitive) relation. **So a
  "holds in all future contexts" guard inherits exactly Part B's caveat:** if the future-fill-context
  relation is a genuine preorder (single-machine, total-order accumulation — see §6) the `□`-guard is
  idempotent and clean; under Byzantine context-confusion it is *not* idempotent, and `□□g ≠ □g` is a
  real failure, not a cosmetic one.
- The **adjudication reflector `R`** (`Disputation.upheld`, `Disputation.lean`) is a *separately built*
  graded reflector, and the verdict warns it does **not** come free from the meet. Guard accumulation is
  meet-side (§2b); adjudicating a *dispute over a guarded fill* (two parties disagree whether a fill
  discharges a guard) would be reflector-side. The honest reading: **guard accumulation does not touch
  the reflector; resolving a contested fill does.** A guarded-hole construct that needs to *decide* a
  contested discharge inherits the reflector's per-regime existence condition — total on the
  witness/certifiable regime (`R_witness`, `Disputation.upheld`), refutable=Arrow on the ballot regime.

### 2d. Expressible vs. needs-extension — the precise line.

**Expressible in the existing posetal hyperdoctrine:** the guard as a fibre `Pred`; filling as the
existential witness (`∃ ⊣ Witness`, §2a); multiparty accumulation as the fibre meet `⋀` (§2b);
attenuation-narrowing as the Heyting residual (`attenuate_narrows`). All of these are *already proven
objects*.

**Requires extension** in two specific places:

1. **Dependent/linear fibres.** The plain Lawvere doctrine has **cartesian (duplicable)** Heyting
   fibres. But a hole-fill consumes a *one-shot* continuation (`OneShot`, `Await.lean:85`;
   `commit_resumes_once`, `:260`) — the fill is a **linear resource**, used exactly once. A guard that
   gates a *resource-bearing* fill therefore lives in a **linear/monoidal fibre**, not a cartesian one.
   The repo *already built the floor for this*: `Dregg2.Metatheory.IndexedMonoidal` welds the Lawvere
   base to **monoidal (linear) fibres** following Shulman's *Framed bicategories and monoidal
   fibrations* and Ponto–Shulman — "the SAME fibration with MONOIDAL fibres" (`IndexedMonoidal.lean`
   header), proving `∃_f ⊣ f* ⊣ ∀_f` on the base *and* each fibre monoidal. **So the extension a
   resource-guarded hole needs is named and partly built — it is the indexed *monoidal* category, the
   linear hyperdoctrine — not a fresh invention.** What is *not* yet built there: the interaction making
   the *guard* (a base/Set-fibre predicate) gate a *fill* (a monoidal-fibre resource) — only the lax
   Frobenius `⊆` half is proved (`IndexedMonoidal.lean` §4), the equality fails non-functionally, mirror
   of `Lawvere.frobenius_le` (`Lawvere.lean:656`).
2. **The future-context box.** "`P` holds in all future fill-contexts" needs the *relational* `∀_R`
   (Part B), with the S4 caveat of §2c. This is *expressible* in Part B but is genuinely the
   relational fibre, not the clean posetal triple.

> A **Dialectica** setting is *not* required by anything in the code. The brief lists it as a candidate;
> I find no obligation that forces it. Guard accumulation is a meet, not a two-player
> witness/counter-witness game, so the Dialectica double-fibration is more machinery than the structure
> pays for. **SPECULATION:** Dialectica *might* become relevant only if one models *contested* fills as
> a verifier/refuter game (the dispute reflector of §2c), where the witness/counter pairing is natural —
> but that is the reflector, already a separate object, and I would not reach for Dialectica before the
> reflector's own per-regime analysis.

---

## 3. The flow-algebra bearing

The partial turn with holes is the **reactive / online** fragment, and the repo proves that fragment is
**right-skewed**: `Dregg2.Deos.FlowAlgebra` shows choice `⊔` does *not* left-distribute over compose `⋆`
in the online simulation order — `flow_choice_halfdistrib` holds (`FlowAlgebra.lean:339`) but
`flow_choice_right_skewed` (`:467`) refutes the converse, with `flow_choice_languages_equal` (`:599`)
showing the separation is invisible to trace language and lives in the online rung (Pradic,
arXiv:2408.14999, RSKA_d⊓).

### 3a. A guarded fill IS a `⋆`-composition gated by a `⊔`-choice on the predicate.

This is the precise structural match. In `FlowAlgebra`, the `R`-atom `Flow.run ℓ f v`
(`FlowAlgebra.lean:223`) *writes a field and emits its output letter*, and the downstream branch reads
that output — "the choice reads `R`'s output" (`FlowAlgebra.lean:29-36`). A **guarded fill is exactly
this shape**: the producer fills the hole (`R` runs, emits its output = the fill value), and *whether
the fill is admissible* is a branch (`⊔`) on the guard `Pred` evaluated against that just-produced value.
The `TransitionGate` reading both `old` and `new` (`FlowAlgebra.lean` anchors) is precisely
`Pred.eval old new` (`PredAlgebra.lean:190`). So:

> guarded-fill `=` `(admit-fill ⊔ reject-fill) ⋆ produce-value`, where the `⊔`-branch reads the value
> `⋆ produce` emitted.

### 3b. Does adding guards respect or break the right-skew? **It SITS on the right-skew, and a guard's
*late binding* is exactly the right-skew's witness.**

The right-skew obstruction is: an *early* commitment (branch before `R` runs) cannot simulate a *late*
commitment (branch after `R`'s output is observed), because the early simulator must commit before it
learns which continuation is demanded — *no lookahead* (`FlowAlgebra.lean:457-466`). A guard on a hole
is **inherently late-binding**: the guard reads the *produced fill value* (`new`), which does not exist
until the producer commits. So a guarded fill is a **late** branch by construction — it lives on the
late side of the right-skew, the `(P ⊔ Q) ⋆ R` side that the early side cannot simulate.

**Consequence (honest, important):** a guarded hole **cannot be soundly compiled to an early branch.**
If an implementation tried to decide hole-admissibility *before* the producer runs (early), it would be
attempting the simulation the right-skew theorem proves *impossible* on reactive data
(`flow_choice_right_skewed`). The guard *must* be evaluated after the fill is produced. This is not a
tension with the right-skew — it is the right-skew *telling the implementation where the guard check
must go*. Guard accumulation (§2b) does not interact with left-distributivity at all: accumulating
guards is meet on the *predicate* (an offline lattice fact — `flow_meet_semilattice`,
`FlowAlgebra.lean:268`, is a genuine `SemilatticeInf`), while the right-skew is about `⊔`-over-`⋆`
*timing*. The two are orthogonal: **meet-accumulation is the `_d⊓` (distributive meet) axis; the
guarded-fill late-branch is the right-skewed `⊔`/`⋆` axis.**

### 3c. Payoff inheritance.

If the guarded-fill flow is RSKA_d⊓ (it is, by 3a/3b sitting inside the proven algebra), then "does this
guarded-flow refine that one?" inherits Pradic's decidable Büchi/SG-game characterization
(`FlowAlgebra.lean:70-77` "the payoff"). This is the ARGUS "refines" bar. **SPECULATION (degree:
plausible, unbuilt):** guard *refinement* — "guard `g'` is at least as strong as `g`" — is just fibre
order (`g' ≤ g`, i.e. `g'.eval ⟹ g.eval`), which is decidable directly (`Pred.eval` is decidable); the
*flow*-level refinement of guarded fills is the part that would route through the Büchi game. The
decidability claim for *guards alone* is immediate; for *guarded flows* it is the named follow-on, not
proved.

---

## 4. The comodel / lens bearing

The dregg4 frame (`project-dregg4-vision.md`) reads the turn as a **guarded comodel of an effect
theory**, the three faces effects/caveats/attestation as the **get/put/guard of a lens**, with
`capExercise = lens composition`. The memory is explicit that this lens/comodel framing is currently
**aspirational/decorative in Lean** (grep-confirmed not built; `project-dregg4-vision.md` "DECORATION"
and "ASPIRATIONAL" paragraphs). I treat it accordingly.

### 4a. A guarded hole = a lens position whose `put` has a precondition. **Fits the frame; not yet code.**

If turn = lens with `(get, put, guard)`, then a **guarded hole is a `put` whose domain is restricted by
its `guard`**. This is *exactly* `predStateStepGuarded` again (`PredAlgebra.lean:580`): the write (`put`
= `stateStep`) is gated by the guard (`predCaveatsAdmit`), committing the same post-state when admitted
(`predStateStepGuarded_eq`, `:591`). So the *executable shadow* of "a lens `put` with a precondition"
already exists — `predStateStepGuarded` IS a guarded `put`. What is not built is the *lens laws*
(get-put / put-put) over it; the dregg4 memory flags `lens/get-put-put` as decoration not yet in Lean.

### 4b. A partial turn = a PARTIAL lens (profunctor / Tambara module). **SPECULATION — structurally
suggestive, unproven.**

A lens with holes is a partial map; the standard categorical home for "lens-with-structure" is a
**profunctor / Tambara module** (Pickering–Gibbons–Wu; Boisseau–Gibbons; Riley, *Categories of Optics*).
A partial turn — a `ConditionalBatch` with unfilled `EventualRef`s — is a profunctor `P(s, a)` that is
only *defined* where the dependency DAG is resolved. The `Slots`/`EventualRef` machinery
(`ConditionalTurn.lean`) is the bookkeeping of *which positions are defined*, and `runOrder_fills`
(`:333`) proves the partial lens becomes total over the resolved sub-DAG. **This is a plausible and
attractive reading**, and the optic/profunctor literature is the right place to look — but **nothing in
the repo builds a profunctor or Tambara structure**, and I will not claim the identification is
established. Label: SPECULATION, well-motivated, would need a `Profunctor`/`Tambara` instance over
`ConditionalBatch` to become real.

### 4c. Multiparty accumulation = lens composition with strengthening preconditions. **Partial fit.**

Lens composition is `capExercise` in the dregg4 frame. If party A's guarded put composes with party B's
guarded put, the *preconditions conjoin* — and conjunction of guards is the meet `⋀` of §2b. So
"composition with strengthening preconditions" = lens-compose where the guard coordinate accumulates by
meet. The meet-accumulation IS code (`Token.admits`/`Pred.allOf`); the *lens composition* carrying it is
the aspirational `capExercise = lens composition`. Honest split: the **guard-meet half is built**; the
**lens-composition half is the dregg4 aspiration**, and the brief's framing is correct *as a target*,
not as a current theorem.

---

## 5. The metalogical core — the logic of guard accumulation

Guarded holes are **proof obligations that propagate to future fillers**. What logic governs the
accumulation?

### 5a. The base logic is the caveat **Heyting/Boolean algebra** — intuitionistic, fail-closed.

`Pred` is a genuine Boolean algebra (`PredAlgebra.lean`: `eval_not_not` `:266`, `deMorgan_and` `:279`,
`deMorgan_or` `:284`), and the caveat layer is the Heyting residual: `attenuate_narrows`
(`Caveat.lean:84`) is the `⇨`-narrowing the header calls "the Heyting residual" (`Caveat.lean:15, 83`).
Guard accumulation is **conjunction** in this algebra (`Pred.allOf`, `Token.admits = ⋀`). Evaluation is
**fail-closed/decidable** (`PredAlgebra.lean:190` and the typed atoms' fail-closed-on-type theorem
`:503`) — an absent or mistyped fill *rejects*. So the logic of "does this fill satisfy the accumulated
guards" is **decidable intuitionistic (in fact Boolean) propositional logic over the transition
atoms**, with the meet for accumulation and the residual for attenuation. This is fully built.

### 5b. The propagation is **contextual-modal `□`** — and the modality is *genuine* iff the future-context
relation is a preorder.

"A guard a *future* participant must discharge" is the necessitation `□g` = "`g` holds in every future
fill-context" (contextual modal type theory, §1c). The repo's box is `relForall` (`Lawvere.lean:315`),
and §2c established the load-bearing fact: `□` is **idempotent / S4-clean** exactly when the
future-context relation is a preorder (`relForall_idem_of_preorder`, `Lawvere.lean:411`) and **breaks**
(`□□g ≠ □g`) on a Byzantine reflexive-non-transitive relation (`box_box_ne_box`, `:486`). Therefore:

> **The logic of guard *propagation* is a modal `□` over the future-fill-context relation, and its
> cleanliness is conditional on that relation's structure** — S4 (a real necessity modality) under
> single-machine/total-order accumulation, sub-S4 (necessitation that does not chain) under Byzantine
> multiparty accumulation. This is not a defect to paper over; it is the same `□`-idempotence boundary
> the hyperdoctrine already proves with teeth.

### 5c. The accumulation also carries a **graded/linear modality** because of one-shot fills.

The fill is a *linear resource* (`OneShot`, used exactly once: `commit_resumes_once` `Await.lean:260` /
`rollback_discards_continuation` `:246`; `one_shot_is_static` `:111`). A guard that gates a
resource-bearing fill therefore lives in a setting where the *fill* is affine even though the *guard*
(a `Pred`) is freely duplicable/Boolean. This is the **linear hyperdoctrine** split the repo's
`IndexedMonoidal` builds: a Boolean predicate base with linear/monoidal fibres
(`IndexedMonoidal.lean` header, Shulman). So the full metalogic is **two-sorted**: a *cartesian Boolean*
guard logic (duplicable constraints, `⋀`-accumulation) gating a *linear/affine* fill logic
(use-once resources). The `Await` one-shot discipline forbids the obvious unsound move (resume-twice =
double-spend, `runtime_guard_is_double_spend` `Await.lean:178`), which is the linear side's teeth.

### 5d. Is it a sheaf/gluing condition? **Yes for the *merge* reading — and it is the I-confluence wall.**

"Partial turns glue iff their guards are compatible" is a sheaf-gluing condition. The repo's gluing /
merge axis is the I-confluent fragment (`project-rhizomatic-dregg-slotting.md`,
`Dregg2/Confluence.lean`: `IConfluent I := ∀ x y, I x → I y → I(x⊔y)`). The crucial, already-proven
caveat: **not every guard glues.** Rhizomatic's monotone (grow-only) predicates I-confluently merge;
dregg's *non-monotone* guards (a balance bound, `Σδ=0`) provably do **not** — "two withdrawals merge to
overdraft" is the keystone counterexample, forcing `nonpairwise_escalation` to consensus
(`project-rhizomatic-dregg-slotting.md`). Therefore:

> **A multiparty guard accumulation glues coordination-free (sheaf-style, merge-by-union) iff every
> accumulated guard is I-confluent (monotone).** A non-monotone guard (capacity, conservation) breaks
> the gluing and forces an ordered/consensus accumulation — which is *exactly* why the receipt chain is
> a `List` (totally ordered) and rhizomatic's delta is a `Set` (order-blind):
> `project-rhizomatic-dregg-slotting.md`'s "I-confluence wall cashed out at the data-structure level."

And this is the connection to the **reflector-failure ≅ Byzantine-non-gluing** novelty
(`project-adjunction-thesis-verdict.md`, residue (2)): a guard-accumulation that *cannot* glue (a bad
coequalizer collapsing admissible≡inadmissible) is the categorical dual of the `H¹≠0` sheaf obstruction.
So the metalogic of guard accumulation **touches the one genuinely novel theorem the adjunction-thesis
work isolated** — not as decoration, but because guard-gluing is exactly a sheaf condition and its
failure is exactly that obstruction.

---

## 6. The honest implications verdict

Mapping each piece to the brief's (a) fits-cleanly / (b) needs-named-extension / (c) reveals-tension.

### (a) Fits cleanly into existing metatheory — instantiates an existing object.

| Guarded-hole piece | Existing object it instantiates | Citation |
|---|---|---|
| Guard as subobject of the fill type | `predStateStepGuarded` (domain restrictor, never mutates) | `PredAlgebra.lean:580, 591, 615` |
| Filling = existential witness | `Predicate ⊣ Witness` seam, `intent.Fires` | `Predicate.lean:99`, `Await.lean:325` |
| Multiparty accumulation = fibre meet `⋀` | `Token.admits`, `Pred.allOf`, `attenuate_narrows` | `Caveat.lean:71,84`, `PredAlgebra.lean:197` |
| Guard logic = Boolean/Heyting, fail-closed | `Pred` Boolean-algebra laws, typed fail-closed | `PredAlgebra.lean:266,279,503` |
| Guarded `put` with precondition (lens get-put-**guard**) | `predStateStepGuarded` (the executable shadow) | `PredAlgebra.lean:580` |
| Hole dependency-soundness (no use-before-fill) | `condTurn_dependency_sound`, `runOrder_fills` | `ConditionalTurn.lean:407,333` |
| Once-installed fill (linearity) | `OneShot`, `commit_resumes_once` | `Await.lean:85,260` |

### (b) Requires a NAMED extension — and the extension is mostly already named/started.

1. **Linear/monoidal fibres for resource-bearing fills** — the *linear hyperdoctrine* / *indexed
   monoidal category* (Shulman; Ponto–Shulman). **Partly built:** `IndexedMonoidal.lean` welds Lawvere
   base + monoidal fibres and proves `∃⊣f*⊣∀` on the base with monoidal fibres. **Not built:** the
   *guard-gates-resource* interaction (only the lax Frobenius `⊆` half exists,
   `IndexedMonoidal.lean` §4 / `Lawvere.frobenius_le` `:656`); making the *guard predicate* (Set fibre)
   gate the *fill resource* (monoidal fibre) as a verified construct is genuinely new work.
2. **The future-context box `□`** — contextual modal type theory (Nanevski–Pfenning–Pientka) realized
   via the relational `∀_R` (`Lawvere.lean:315`). **Expressible in Part B already**, but it is the
   relational fibre with the S4-idempotence boundary, not the clean posetal triple. A "holds in all
   future fills" guard is a real `□`, with the proven caveat that it is S4 only under preorder
   context-accumulation.
3. **The partial-turn-as-profunctor/optic** (§4b) — SPECULATION; no `Profunctor`/`Tambara` instance
   exists. This is the dregg4 aspiration (`capExercise = lens composition`), explicitly flagged
   not-in-Lean.

### (c) Reveals a TENSION with an existing result — two, both *informative* not *blocking*.

1. **The right-skew forbids early guard-checking.** A guard reads the produced fill (`new`), so it is
   *late-binding* by construction (§3b); `flow_choice_right_skewed` (`FlowAlgebra.lean:467`) proves a
   late branch *cannot* be simulated by an early one on reactive data. **Tension:** any implementation
   that tries to decide hole-admissibility before the producer commits is attempting a provably
   impossible simulation. **Resolution:** this is the right-skew *prescribing* where the guard check
   lives (after the fill), not a contradiction — but it is a hard constraint a naive implementation
   would violate.
2. **Non-monotone guards break coordination-free gluing.** Multiparty guard accumulation glues
   sheaf-style only for I-confluent (monotone) guards; a conservation/capacity guard is non-monotone and
   forces ordered/consensus accumulation (§5d, `project-rhizomatic-dregg-slotting.md`,
   `Confluence.lean`). **Tension:** "multiple parties freely accumulate/refine guards over the
   structure's lifetime" is only *coordination-free* on the monotone fragment; the moment a guard is a
   bounded-counter/conservation predicate, accumulation must serialize (the `List`-not-`Set` receipt).
   **Resolution:** the `ConfluenceClassifier` is the existing gate that decides which guard-merges are
   coordination-free vs. must escalate — so the tension is *already diagnosed and routed* by dregg's
   monotonicity split; a guarded-hole construct must run guards through it.

### What would have to be PROVEN to make guarded holes a first-class verified construct.

1. **`guardedFill_sound`** — a guarded fill commits iff (the producer committed) ∧ (the accumulated
   guard `⋀ gᵢ` evaluates true on the produced value). This is `predStateStepGuarded`
   (`PredAlgebra.lean:580`) lifted over `EventualRef`/`Slots`: gate `runOrder`'s slot-fill
   (`ConditionalTurn.lean:171`) by the guard. **Reuses:** `predStateStepGuarded_eq` (`:591`),
   `condTurn_dependency_sound` (`:407`), `forward_is_handler_commit` (`:602`). Mostly assembly of
   existing keystones.
2. **`guardAccumulation_is_meet` + `guardAccumulation_narrows`** — accumulating guards is the fibre
   meet and can only shrink admissibility. **Reuses:** `attenuate_narrows` (`Caveat.lean:84`) and the
   `Pred.allOf` laws verbatim; this is nearly free.
3. **`guardedFill_late_binding` / right-skew placement** — the guard check must read the produced value,
   formalized as: the guarded fill is the late side `(admit ⊔ reject) ⋆ produce`, which by
   `flow_choice_right_skewed` cannot be lowered to an early branch. **Reuses:** `FlowAlgebra` verbatim;
   new content is the embedding of guarded-fill into `Proc`.
4. **`guardGluing_iff_iconfluent`** — multiparty guard accumulation glues coordination-free iff each
   guard is I-confluent; non-monotone guards force escalation. **Reuses:** `Confluence.IConfluent`,
   `nonpairwise_escalation`, `ConfluenceClassifier`. This is the *new theorem with teeth* and the one
   that touches the reflector-failure≅dual-H¹ novelty.
5. **(harder, named extension)** **`resourceGuardedFill` in the indexed-monoidal fibre** — a guard
   (Boolean base fibre) gating a linear fill (monoidal fibre), with the lax interaction law. **Reuses:**
   `IndexedMonoidal.lean`'s welded structure; new content is the guard×resource interaction beyond the
   lax `⊆` half.

---

## 7. Keystones it builds on, and the genuinely-new things it needs

**Existing keystones reused (3–5):**

1. **`predStateStepGuarded` + `_eq` + `_violation_fails`** (`PredAlgebra.lean:580,591,615`) — the
   guard as a domain-restricting `put`; this IS the guarded-fill executor, already proven to lift every
   `stateStep` keystone.
2. **`attenuate_narrows` / `Token.admits = ⋀`** (`Caveat.lean:84,71`) — guard accumulation = fibre meet
   = Heyting narrowing; the multiparty-refinement law is already a theorem.
3. **`condTurn_dependency_sound` + `runOrder_fills` + `forward_is_handler_commit`**
   (`ConditionalTurn.lean:407,333,602`) — holes never read-before-fill; fills install once via the
   one-shot handler. The partial-turn substrate is sound and computable.
4. **The Lawvere hyperdoctrine `∃⊣f*⊣∀` + the relational `∀_R` box with its S4 boundary**
   (`Lawvere.lean:112,323,411,486`) — fill = existential witness; "holds in all future contexts" = the
   `□` modality, with the proven idempotence-iff-preorder caveat.
5. **The right-skew `flow_choice_right_skewed`** (`FlowAlgebra.lean:467`) — places the guard check on
   the late (post-fill) side and inherits the decidable-refinement payoff.

**Genuinely new things needed (1–3):**

1. **`guardGluing_iff_iconfluent`** — the *one new theorem with teeth*: multiparty guard accumulation
   glues coordination-free exactly on the monotone/I-confluent fragment; non-monotone guards
   (conservation, capacity) force serialized/consensus accumulation. This is where guarded holes touch
   the novel **reflector-failure ≅ dual-H¹ Byzantine-non-gluing** result (`adjunction-thesis-verdict`
   residue 2) and the `ConfluenceClassifier` routing. Not a reassembly — genuinely new content.
2. **The resource-guarded fill in the linear/monoidal fibre** — a Boolean guard gating a one-shot
   (linear) fill, the guard×resource interaction in `IndexedMonoidal`. The *floor* is built (Shulman
   indexed-monoidal weld); the *interaction* is new, and only the lax `⊆` half is currently within
   reach.
3. **(SPECULATION, optional) the partial-turn-as-profunctor/optic** — if one wants the dregg4
   `capExercise = lens composition` to be a *theorem* rather than a slogan, a `Profunctor`/`Tambara`
   instance over `ConditionalBatch` would make "partial turn = partial lens" precise. Well-motivated by
   the optics literature; nothing in the repo builds it yet.

**One-line verdict (first pass).** A guarded hole is a *constrained metavariable* — a subobject-of-the-fill guard
(already `predStateStepGuarded`) attached to an `EventualRef`, accumulated by fibre-meet (already
`attenuate_narrows`), filled by the existential-witness seam (already `Predicate ⊣ Witness`), checked
*late* by the right-skew's mandate, and propagated by a contextual `□` that is S4-clean only under
preorder accumulation. It **fits the existing metatheory at four of five seams using objects already
proven**, **needs one named extension that is already started** (the linear/monoidal fibre,
`IndexedMonoidal`), and **reveals exactly one genuinely-new theorem worth proving**:
guard-gluing is coordination-free iff the guards are I-confluent — which is where the construct earns
its keep, touching both the conservation boundary and the reflector-failure≅dual-H¹ novelty.

*The one-line verdict above is correct but answers the weak reading. §8 re-examines against the
load-bearing turn structure and finds the sharper answer.*

---

## 8. The system-coherence audit — does a hole compose with the load-bearing turn? (elegant or flaw)

The §§1–7 analysis is sound but it silently assumed the *weak* reading of "hole": a **dataflow
slot between fully-specified contributions**. That is what dregg's machinery actually is, and against
that machinery the categorical placement is faithful. ember's sharpened question is about the *strong*
reading — a hole as a **missing contribution** whose conservation delta and authority are not yet
determined, with a predicate attached for a future party to discharge. This section traces the strong
reading through the four load-bearing structures and reaches the elegant-or-flaw verdict.

### 8.0 The one structural fact that decides everything

A `ConditionalBatch.nodes` is `List Node`, and `Node := List FullAction` (`ConditionalTurn.lean:77`).
**Every node is a fully-specified turn, present in the batch at construction time.** The "hole" is
`edges : List (Nat × Nat)` plus the `Slots : Nat → Bool` environment (`ConditionalTurn.lean:87,101`):
an edge `(consumer, producer)` says the consumer reads the producer's *output value*, which is not
known until the producer commits. So:

> **What is deferred is a producer's output VALUE. What is NOT deferred is any node's existence, its
> action list, its conservation delta, or its authority requirement.** Every one of those is fixed the
> moment the batch is built.

The same is true of the `Promise`/`EventualRef` (`Spec/Await.lean:249-256`): a `Promise` is
`{ id, fulfilled : Bool }` — a value-future, carrying no balance, no reserved budget, no partial write
(confirmed across the Rust `pipeline.rs::PipelineRegistry`, whose state is two hashmaps of *queued
serialized messages*, never a reserved resource; `break_promise` discards the queue and leaves state
literally unchanged). This is E-language CapTP semantics: **promise pipelining is a latency
optimisation, not a held-open commitment.** A dregg hole is a benign dataflow slot *by construction*.

ember's strong guarded hole asks for something categorically different: a position where the
*contribution itself* — and therefore its δ and its authority — is the thing left open. **That object
does not exist in dregg, and §§8.1–8.4 show why each load-bearing structure forbids it.**

### 8.1 Q1 — Conservation: a hole in a δ-bearing position is ill-typed until filled.

The conservation keystone is per-asset and **unconditional on a *complete* turn**:
`execFullTurnA_conserves_exact` (`TurnExecutorFull.lean:2750`) proves
`recTotalAsset s'.kernel b = recTotalAsset s.kernel b` for *every* committed turn, because every verb's
disclosed delta is identically zero (`ledgerDeltaAsset_eq_zero`, `:2232`). For the batch,
`condTurn_conserves` (`ConditionalTurn.lean:267`) has the shape

> `execConditionalTurn b s = some (s', o)` ∧ (Σ over committed nodes' deltas = 0) ⟹ `recTotal` preserved.

Read the hypothesis exactly. Conservation is a theorem about a batch that **reached `some (s', o)`** —
i.e. every node committed (the all-or-nothing `runOrder`, `:171`; `condTurn_atomic`, `:210`). **There
is no conservation predicate over a batch with an unresolved node.** If you hold one node open, the
executor never reaches `some`; the conservation theorem's hypothesis is *unsatisfiable*, not false. The
partial turn has **no defined balance** — not "a balance that might be wrong," but no `recTotal`
transition at all, because no transition has occurred.

This is the precise sense in which a hole in a conservation position is **ill-typed until completion**:
- A *dataflow* hole (the weak reading) is fine — the producer node's δ is already fixed and *known to
  be zero* (every verb conserves), so the slot defers only a value, never a balance. Conservation is
  closed for the whole batch the instant it commits, and the order of value-forwarding is irrelevant to
  it.
- A *contribution* hole (the strong reading) is the move the keystone forbids: it asks for a turn whose
  δ is *undetermined*. But "δ undetermined" has no place in a world where conservation is proven by
  every δ being *identically zero by construction* of the verb set. There is no `FullAction` with an
  open delta to put in the hole. **You cannot hold open a conservation obligation, because dregg has no
  non-zero-delta primitive to hold open in the first place** — the conservation invariant is enforced
  *per verb*, not *per turn-by-cancellation*. (This is a strength: it means there is no "I owe you, to
  be balanced by a future fill" state that could be abandoned. The system has *no* notion of an
  outstanding imbalance, so it has no hole to leak one through.)

> **Finding (Q1).** A hole is conservation-safe **iff it defers only a value, not a δ.** dregg's holes
> defer only values (and the deferred verbs all have δ=0), so they are safe — *trivially*, because
> dregg has no way to express a δ-bearing hole. The strong guarded hole is not *unsafe* here; it is
> *inexpressible*, and that inexpressibility is the conservation keystone doing its job.

### 8.2 Q2 — The joint-turn relationship: joint turns have the SAME discipline, and it is deliberate.

Is a partial-turn-with-holes just a joint turn whose contributions arrive over time? **No — and the
joint-turn machinery makes the reason explicit.** A joint turn is a **wide pullback**
(`Metatheory/Categorical.lean:549`, `IsWideJointTurn`): the mediator `lift` is given *one agreeing cone
of all views at once* (`lift {W} (views : ∀ i, W ⟶ P i) (hv : ∀ i i', …agree…)`). **There is no partial
cone.** You supply every party's contribution simultaneously or no mediator exists. The operational
realisation agrees: `MixedJoint` (`Distributed/PrivateLeg.lean:169`) carries `publicLegs` and
`privateLegs` as *complete lists*, and `MixedAdmissible` (`:178`) requires `jointApplyAll` to commit the
whole public backbone **and** *every* private proof to verify before the turn is admissible. The
soundness keystone `joint_turn_sound_with_private_legs` (`:197`) delivers conservation
(`∀ b, recTotalAsset k' b = recTotalAsset k b`) and no-cap-amplification (`k'.caps = k.caps`) **only
under `MixedAdmissible`** — i.e. only when complete.

So joint turns *appear* to be "the partial-turn idea, spatially" — private legs even *look* like holes
(a leg whose state is hidden under an existential, `PrivLegHolds`, `:90`). But the resemblance is
exactly where the discipline bites: a private leg is **not an unfilled hole — it is a fully-determined
contribution whose *witness* is a proof rather than data.** Its δ is pinned (the ZK statement asserts
`recTotalAsset kPost = recTotalAsset kPre`), its `jid` consent is pinned (CG-2 binding,
`bind.consentOf l = mj.jid`). The proof must be *present and verifying* up front; a missing or
unverified proof aborts, it does not "wait for a later fill."

> **Finding (Q2).** The existing joint-turn machinery does **not** subsume the strong guarded hole, and
> it does **not** harbour the same latent flaw — because it solves the problem the *opposite* way. It
> permits *spatial* partiality (hidden contributions, proof-not-data witnesses) while forbidding
> *temporal* partiality (an undetermined contribution filled later). The wide-pullback `lift`-takes-the-
> whole-cone and the `MixedAdmissible` all-present requirement are the *same* all-or-nothing discipline
> as the batch, lifted to multiparty. **Guarded holes do not expose a flaw in joint turns; they reveal
> that joint turns already made the design decision guarded holes would have to overturn:** a
> contribution is determined-with-deferred-witness, never undetermined-with-deferred-fill.

### 8.3 Q3 — Authority bearing, against the live off-circuit finding.

The live circuit-soundness work (`project-circuit-soundness-apex.md`,
`Circuit/RotatedKernelRefinementFacet.lean`, `Circuit/ClosureTransfer.lean`) cuts authority into two
parts, and the cut is exactly the cut a guarded hole would have to respect:

- **The cap leg is FORCED in-circuit.** `authoritySource_authorizes`
  (`RotatedKernelRefinementFacet.lean:275-290`) *derives* `authorizedFacetB fcaps .signature tr = true`
  from a witnessed depth-16 cap-membership opening — the authority conclusion is a *theorem from the
  witness*, not a carried field. `adversarial_find_cannot_forge` (`Predicate.lean:139`) makes the
  predicate-discharge gate unforgeable: the prover is universally quantified, only the in-TCB verifier
  decides.
- **The owner short-circuit is OFF-circuit by design** (`FacetAuthority.lean:229`, `actor = src`): it
  needs no witness because it is reflexive — there is nothing for an adversary to forge in "I am
  acting on my own cell."

Now place a guarded hole's predicate. A guard is *exactly* an authority-like obligation: "a fill is
admissible only when the guard is discharged" (§0). The live finding says: **an obligation a light
client must be able to trust has to be FORCED in-circuit (proof-witnessed), not carried off-circuit.**
The pipeline machinery already honours this for the *value* case — `drainAll` re-runs
`authorizedB k.caps turn` on *every* queued send at delivery (`Exec/CapTPPipeline.lean:129,147`;
`pipelining_preserves_seam`, `Exec/CapTP.lean`: delivery rewrites only the target cell, never the
guard, so a pipelined call is authorised iff its original was). So a *value*-hole's authority is already
re-forced at fill time; pipelining is not an authority bypass.

The strong guarded hole adds a *new* predicate `g` that a *future* party attaches. The question is
whether `g`'s discharge is forced in-circuit. Two cases:

1. **If `g`'s discharge enters the proof floor** (joins the `ClosedWitness` carriers), it is forced
   in-circuit and the light client is safe. This is the *good* outcome — and it is **exactly the work
   the live cap-bridge campaign is already doing for cap-authority.** A guarded-hole predicate is the
   *same shape* as a cap-leaf authority obligation: a `Pred` over the transition that must be witnessed,
   not trusted. So guarded holes do not invent a new in-circuit obligation type — they reuse the one
   being built (`registry_sound` + the cap-open descriptor).
2. **If `g` is checked only by the off-circuit executor** (the runtime evaluates `Pred.eval g old new`
   but the *circuit* does not bind it), then a light client that trusts only the proof **cannot tell
   whether the guard held.** This is the *worse* outcome, and it is the same failure mode the
   obligation table in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md` catalogues for the ~17 effects whose
   writes are not yet bound into the commitment.

> **Finding (Q3).** Guarded holes do not *create* the off-circuit-trust problem and they do not *make
> it worse on their own* — but they **sharpen it into a clean requirement**: a guarded-hole predicate
> is sound under the light-client model **iff its discharge is bound into the circuit commitment**, by
> the same mechanism (`registry_sound` forced via a descriptor) the cap-bridge campaign is landing for
> authority. The frame is therefore *forcing-positive*: it names "the guard must be proof-witnessed"
> as a first-class obligation rather than letting it hide in the executor. The danger is only realised
> if someone implements a guard as an executor-only `Pred.eval` and forgets to bind it — which is
> precisely the `CIRCUIT-FUNCTIONAL-CORRECTNESS` failure mode, now stated for predicates.

### 8.4 Q4 — Right-skew, re-examined: is late-binding a genuine obstruction to the proof model?

§3b found the guard must be checked *late* (after the producer emits the fill value), because the guard
reads `new` and `flow_choice_right_skewed` (`FlowAlgebra.lean:467`) proves a late branch cannot be
simulated by an early one. The first pass called this "the right-skew telling the implementation where
the guard goes." Re-examined against the *proof* model, the question is sharper: does late-binding mean
a guarded fill **cannot be verified at commit time without re-running the producer**?

Answer: **no, and the distinction is the whole point.** Late-binding constrains *where the check
happens in the dataflow* (after the value exists), not *whether a succinct proof of the check can be
produced after the fact*. The two are independent because dregg's proof model is **execution-trace
witnessing, not re-execution**: a STARK leaf certifies `recCexec s.pre s.turn = some s.post`
(`RecursiveAggregation.lean`, `leaf_sound`) — the verifier checks a *proof that the step ran and
satisfied its gates*, it never re-runs the producer. So "the guard reads the produced value" is
discharged by the *same* trace that produced the value: the producer's commit and the guard's
evaluation against the produced `new` are *one step's* obligations, both witnessed in that step's leaf.
The right-skew forbids *hoisting the branch earlier in the algebra*; it does **not** forbid *proving the
late branch held*. A proof is an after-the-fact object by nature.

> **Finding (Q4).** The right-skew is a *benign placement prescription*, not an obstruction to the
> proof model. It says: do not compile the guard to an early branch (provably impossible on reactive
> data). It does **not** say the guarded fill can only be verified by re-running the producer — because
> dregg verifies *traces*, not *re-executions*, and the produce-then-guard pair is a single trace step
> whose leaf witnesses both. The only thing the right-skew would break is a (wrong) implementation that
> tried to decide admissibility *before* the value exists; no correct implementation wants that.

### 8.5 Q5 — The verdict, synthesised.

Trace the strong guarded hole through all four:

| Load-bearing structure | What it does to a strong (contribution-)hole |
|---|---|
| Conservation keystone (`execFullTurnA_conserves_exact`, `condTurn_conserves`) | **Inexpressible.** No δ-bearing hole exists because every verb has δ≡0; there is no outstanding-imbalance state to defer. (§8.1) |
| Joint-turn wide pullback (`IsWideJointTurn`, `MixedAdmissible`) | **Already forbidden, deliberately.** Permits hidden/proof contributions (spatial), forbids undetermined-later contributions (temporal). (§8.2) |
| Authority gate + circuit (`authoritySource_authorizes`, `registry_sound`) | **Forces the right requirement.** Guard discharge is sound iff bound in-circuit — the same cap-bridge mechanism already being built. (§8.3) |
| Right-skew (`flow_choice_right_skewed`) | **Benign placement.** Check goes after the value; the trace-witness proof is after-the-fact regardless. (§8.4) |

**The verdict is two-valued because there are two ideas wearing one name:**

**(a) — Weak guarded hole = dataflow slot + late predicate. Elegant, composes cleanly, mostly already
code.** A guard (`Pred`, a subobject of the fill type — `predStateStepGuarded`, `PredAlgebra.lean:580`)
on an `EventualRef`, accumulated by fibre-meet (`attenuate_narrows`), discharged by the witness seam
(`registry_sound`), checked late, forced in-circuit by the same descriptor mechanism as cap-authority.
This is genuine added capability — *predicated pipelining* — and the only genuinely-new theorem it needs
is the §5d/§6 `guardGluing_iff_iconfluent`. **This reading is real and worth building.**

**(c) — Strong guarded hole = a hole in a conservation/authority position, i.e. an undetermined
contribution. EXPOSES the boundary the construction enforces.** It is not a bug *in* dregg; it is a
**clean statement of what dregg's discipline is *for*.** A complete turn is conservation-closed
(by δ≡0 per verb), authority-gated (forced in-circuit), and all-or-nothing (the `runOrder`/`MixedAdmissible`/
wide-pullback all-present requirement). A *contribution* hole asks to suspend exactly these three at
once: hold an undetermined δ, defer an unforced authority obligation, and admit a partial structure.
**dregg makes all three inexpressible, and they are inexpressible by the *same* design choice** — the
**"a contribution is fully determined at the moment it joins the structure; only its *witness* (value
or proof) may be deferred"** invariant. The wide-pullback-takes-the-whole-cone, the all-or-nothing
batch, the δ≡0-per-verb keystone, and the in-circuit authority forcing are four faces of that one
invariant.

> **The single most important system-coherence finding.** dregg already draws a bright line:
> **determination is eager; witness is lazy.** A contribution's *shape* (its actions, its δ, its
> authority demand, its joint-turn consent) is fixed when it joins the structure; only its *witness*
> (the produced value, or the discharging proof) may arrive later. Every "hole" the system has —
> `EventualRef`, `Promise`, the private-leg existential, the pipelined send awaiting authorization
> re-check — is a *lazy witness over an eager shape*. ember's **weak** guarded hole is a new lazy-
> witness obligation (a predicate) over an eager shape — it fits. ember's **strong** guarded hole asks
> for a *lazy shape* (an undetermined contribution) — and that is the one thing the whole construction
> is built to forbid, because a lazy δ is an outstanding imbalance, a lazy authority is an off-circuit
> trust, and a lazy contribution is a non-atomic turn. **The guarded hole, pushed to its strong form,
> does not break dregg — it locates dregg's load-bearing invariant and names it.**

**Is this a flaw?** Only if the strong reading is the *intended* one and the system silently fails to
support it. It does not fail silently — it fails *by inexpressibility*, which is the safe failure: there
is no `FullAction` with an open δ to construct, no wide-pullback cone with a missing leg to lift, no
admissible mixed joint with a missing proof. The danger ember was right to suspect is real **but it does
not currently exist in the code** — because the code has no constructor for it. The flaw would only
appear if a future "partial turn" feature were built that *let* a contribution be undetermined-and-
filled-later **without** re-imposing the eager-shape invariant at fill time (an in-circuit binding of the
fill's δ and authority into the commitment). **That is the thing to never build**, and §8.3's
forcing-positive frame is the guardrail: any future hole-fill must bind its δ and its guard into the
proof, exactly as the cap-bridge binds authority.

### 8.6 What this revises in §§1–7.

- §1–§4 stand as a *categorical* placement of the **weak** reading; nothing there is overturned, but
  every "fits cleanly" should be read as "fits cleanly *for a dataflow slot whose contribution shape is
  already determined*."
- §6(c)'s two "tensions" (right-skew, non-monotone gluing) are downgraded: the right-skew is benign
  (§8.4), and the non-monotone-gluing tension is *the same boundary* as the conservation keystone (a
  non-monotone guard is exactly a δ-bearing / capacity constraint, which §8.1 shows is inexpressible as
  a hole). They are not separate frictions; they are two views of the one eager-shape invariant.
- The genuinely-new theorem worth proving narrows to **two**, with priority reordered:
  1. **`holeFill_binds_in_circuit`** (the §8.3 guardrail, *new, highest value*): any guarded fill must
     bind its δ and its discharged guard into the commitment the light client verifies — the predicate
     analogue of `authoritySource_authorizes`. This is the theorem that keeps the strong reading from
     ever becoming an unsound feature.
  2. **`guardGluing_iff_iconfluent`** (the §5d theorem): multiparty guard accumulation glues
     coordination-free iff each guard is I-confluent — which §8.1 now reframes as *the conservation
     boundary itself*: a non-monotone guard is a δ/capacity constraint and forces serialisation, the
     same reason there is no δ-bearing hole.

**Closing line.** Guarded holes are **elegant and system-coherent in their weak (dataflow-slot +
late-predicate) form** — predicated pipelining, mostly already code — and in their **strong
(undetermined-contribution) form they are a precise instrument that locates dregg's deepest invariant:
*determination is eager, witness is lazy.* They do not expose a flaw in the construction; they expose
(and name) the construction's load-bearing reason for refusing exactly the thing the strong reading
asks for. The one durable obligation that falls out is the guardrail `holeFill_binds_in_circuit`: if a
partial-turn feature is ever built, every fill must bind its δ and its guard into the proof the light
client checks — never trusted off-circuit, never an outstanding imbalance.
