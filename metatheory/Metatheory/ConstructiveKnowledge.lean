/-
# Metatheory.ConstructiveKnowledge — the candidate-independent logic of constructive
# knowledge and authority.

This is the **actual metatheory** of dregg, distinct from (and underneath) the
verification of the dregg2 *system* (the `Dregg2.*` library). Per
`CONSTRUCTIVE-KNOWLEDGE.md §0–§7`: dregg is, beneath the bytes, a **metatheory of how
constructive knowledge / authority is produced, combined, attenuated, propagated and
conserved across a distributed network of mutually-untrusting knowers.** A *capability*
is not a key in a lock — it is **a proof obligation you can discharge** (`§0`).

It reuses the seams the verification already pins:
  * `Dregg2.Laws` — the `Predicate ⊣ Witness` adjunction and the `Verify`/`find` seam
    (the realizability core, `§0`, `§2`);
  * `Dregg2.Boundary` — the coinductive cell and its ▶-guarded bisimulation soundness
    (`§2`, `§4`);
  * `Dregg2.Core` — conservation as a monoid-hom and the no-free-copy law (`§4.1`).

…but it is namespaced `Metatheory` and is **candidate-independent**: every type is an
abstract parameter, never a dregg2-specific `Nat`-for-semantics. It would be the
metatheory of *any* system built this way (`§7`).

DISCIPLINE: faithful Props with real content. The PROVED keystones are pinned with
`#assert_axioms` (kernel-clean: only `propext`/`Classical.choice`/`Quot.sound`). The deep
open parts — the reachability closure of the non-forgeability invariant (`§3`) and the
abstract ZK indistinguishability (`§2`) — are honest `-- OPEN:` obligations resting on a
stated *parameter* (a hypothesis), never an `axiom`/`admit`/`sorry`-alias.
-/
import Dregg2.Laws
import Dregg2.Boundary
import Dregg2.Core
import Dregg2.Tactics
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

namespace Metatheory

open Dregg2.Laws Dregg2.Boundary

universe u v

/-! # §1. Knowledge = constructive demonstrability (the realizability core)

`CONSTRUCTIVE-KNOWLEDGE.md §0`: *"to hold a capability is to be able to exhibit a witness
that authorizes an act — never merely to assert it."* The whole edifice is organized
around the asymmetry **proof-checking is cheap and trusted; proof-search is undecidable
and untrusted** — the BHK / realizability reading of intuitionistic logic, made
operational and distributed.

We encode this directly on the `Predicate ⊣ Witness` adjunction (`Dregg2.Laws`): a
*claim* `X` carries a verifier-side `stmt X : P`, and a knower **holds** `X` iff it can
exhibit a witness `w` that `Verify`s `stmt X`. -/

/-- An abstract **claim** the knower may hold authority over / know. The only structure a
claim has, metatheoretically, is its *verifier statement* `stmt : Claim → P` — the
predicate a witness must discharge to demonstrate the claim. (`§1`: an edge of the
knowledge graph is *"a directed fact: this cell can constructively demonstrate authority
over that one"*; `stmt` is the predicate that demonstration discharges.) -/
structure Claim (P : Type u) where
  /-- The verifier-side predicate that *demonstrating* this claim must discharge. -/
  stmt : P

/-- **`Holds k X`** (the realizability core, `§0`): a claim is *held* — known
constructively — exactly when **there exists a witness that `Verify`s** its statement.
This is the BHK clause for an atomic capability: knowing `X` ≡ possessing a realizer for
`stmt X`. It is *constructive demonstrability*, not assertion: `Holds` is `∃ w,
Discharged (stmt X) w`, the existential of the **decidable, verifier-local** check.

(`§1`: there is *no global registry of who-can-do-what*; authority is established by
*exhibiting a discharging witness at the point of use, and checking it* — that is exactly
this existential over `Discharged`.) -/
def Holds {P W : Type u} [Verifiable P W] (X : Claim P) : Prop :=
  ∃ w : W, Discharged (P := P) (W := W) X.stmt w

/-- **The verify/find asymmetry, as a structure** (`§0`, `§1`). A `Knower` carries the
**trusted, decidable** side — a `Verifiable` instance (`Verify P w : Bool`, the cheap
checkable golden oracle) — but its prover/matcher (`find`) is an **untrusted, opaque,
possibly-undecidable** plugin (`Searchable`, an `Option`-valued partial function with no
completeness/termination promise). The metatheory commits ONLY to the verify side.

Bundling them in one structure is the faithful statement of the asymmetry: a knower *is*
its decidable verifier together with whatever (untrusted) search it happens to run. -/
structure Knower (P W : Type u) where
  /-- The TRUSTED side: the cheap, decidable, verifier-local check (the TCB). -/
  verify : Verifiable P W
  /-- The UNTRUSTED side: the opaque prover/matcher plugin (no completeness, no
  termination); the metatheory makes NO promise about when it returns `some`. -/
  search : Searchable P W

/-- The decidable verifier of a knower really is decidable — the trusted side is
*checkable now*, the asymmetry's "cheap" half made explicit. With the knower's
`Verifiable` instance in scope, `Discharged X.stmt w` (= `Verify X.stmt w = true`) is a
decidable proposition. -/
instance (k : Knower P W) (X : Claim P) (w : W) :
    Decidable (@Discharged P W k.verify X.stmt w) :=
  inferInstanceAs (Decidable (_ = true))

/-- **Realizability soundness of the untrusted searcher (`§0`).** The ONLY guarantee
demanded of the prover plugin: *whatever it returns must verify.* If a knower's untrusted
`find` produces a witness `w` for `X`, then `X` is genuinely `Holds` — search is sound by
verification (no completeness, no termination). This lifts `Dregg2.Laws.search_sound` to
the `Knower`/`Holds` reading: the untrusted side can only ever *establish* real knowledge,
never fake it, because its output is funnelled through the trusted `Verify`. -/
theorem find_realizes (k : Knower P W) (X : Claim P) (w : W)
    (h : Searchable.find (self := k.search) X.stmt = some w) :
    @Holds P W k.verify X :=
  ⟨w, @search_sound P W k.verify k.search X.stmt w h⟩

-- NOTE: `find_realizes` is NOT kernel-clean — it rests (correctly) on the **search
-- contract** `Dregg2.Laws.search_sound`, which is a deliberate `sorry`'d *primitive*
-- (the soundness-by-verification contract on the external, untrusted prover plugin: there
-- is no in-module data relating an opaque `Searchable.find` to `Verify`). So this is a
-- REST-ON-A-PRIMITIVE keystone, not a PROVED-clean one; deliberately NOT `#assert_axioms`'d.

/-- **Realizability closure under the verify seam — PROVED, kernel-clean.** Holding is
*closed under the `Verify` seam*: if a knower already verifies a witness `w` for `X`
(`Discharged (stmt X) w`), then it `Holds X`. Trivially the converse direction holds too,
so holding **is exactly** "a discharging witness exists." This is the load-bearing fact
that `Holds` is the realizability predicate and nothing more: knowledge = a verifiable
witness, full stop — no hidden assertion channel. -/
theorem holds_iff_discharged_witness {P W : Type u} [Verifiable P W] (X : Claim P) :
    Holds (W := W) X ↔ ∃ w : W, Discharged (P := P) (W := W) X.stmt w :=
  Iff.rfl

/-- **Monotonicity of knowledge along witness implication — PROVED, kernel-clean.** If
demonstrating `X` is *at least as hard* as demonstrating `Y` — every witness that
discharges `X` also discharges `Y` — then holding `X` confers holding `Y`. This is the
realizability reading of entailment between claims: a realizer for the stronger claim is a
realizer for the weaker. (The verify-side direction of the `Predicate ⊣ Witness` Galois
connection: `stmt X ⊢ stmt Y` lifts witnesses forward.) -/
theorem holds_mono {P W : Type u} [Verifiable P W] {X Y : Claim P}
    (himp : ∀ w : W, Discharged (P := P) (W := W) X.stmt w →
                     Discharged (P := P) (W := W) Y.stmt w) :
    Holds (W := W) X → Holds (W := W) Y := by
  rintro ⟨w, hw⟩
  exact ⟨w, himp w hw⟩

#assert_axioms holds_iff_discharged_witness
#assert_axioms holds_mono

/-! # §2. The epistemic boundary — who-knows-what (the disclosure lattice)

`CONSTRUCTIVE-KNOWLEDGE.md §5`, and the predicate-kind annotations of `§2`/`§6`. Across a
trust boundary authority becomes **epistemic**: you must *present a verifiable witness*,
because the far side shares no mediator. *Which* epistemic content the verifier learns is
graded by a **disclosure lattice**: `Cleartext-inside ⊑ Commitment-inside ⊑
Acceptance-inside ⊑ Out-of-band` — the four predicate-kinds, ordered by *how much the
verifier learns*.

The KEY law (`§6`, the ZK/epistemic-boundary property): a **witnessed (zero-knowledge)**
predicate's verifier learns only **`Acceptance`** — that the statement is true — and
**NOT the witness content**. -/

/-- **Epistemic position** — *how much a verifier learns* when a predicate of a given kind
is discharged. The four predicate-kinds of `§2`/`§6`, as an abstract partial order
(`Cleartext` reveals the most; `OutOfBand` the verifier learns nothing in-band). We keep
it as a concrete 4-element `enum` only to *name* the positions; all laws below are stated
against an abstract `Disclosure` lattice so nothing is `Nat`-for-semantics. -/
inductive EpistemicPosition where
  /-- The witness is revealed in the clear: the verifier learns the full content. -/
  | cleartext
  /-- The verifier learns a *binding commitment* to the content, not the content. -/
  | commitment
  /-- The verifier learns ONLY that the statement is **accepted** (true) — the
  zero-knowledge position: acceptance without content. -/
  | acceptance
  /-- The matter is settled **out of band**: the verifier learns nothing in-band. -/
  | outOfBand
  deriving DecidableEq, Repr

/-- **The abstract disclosure structure (`§5`, `§6`).** A `Disclosure` is a set of
epistemic positions with a partial order `learns` — `a ⊑ b` means *"a verifier at position
`a` learns no more than one at `b`"* (more disclosure is higher) — together with the two
distinguished positions the ZK law needs: `acceptancePos` (a witnessed/ZK predicate's
verifier sits here) and `contentPos` (where the witness content would be revealed), with
the **separation hypothesis** `accept_below_content : acceptancePos ⊑ contentPos` and
`accept_ne_content` that they are genuinely distinct positions.

This is candidate-independent: any concrete disclosure lattice (the 4-kind one above, a
richer differential-privacy grade, …) instantiates it. -/
structure Disclosure (E : Type u) [PartialOrder E] where
  /-- The position a witnessed (zero-knowledge) predicate's verifier occupies. -/
  acceptancePos : E
  /-- The position at which the witness *content* would be disclosed. -/
  contentPos : E
  /-- Acceptance discloses strictly less than content: `acceptance ⊑ content`. -/
  accept_le_content : acceptancePos ≤ contentPos
  /-- …and is genuinely a *different* position (the boundary is non-trivial). -/
  accept_ne_content : acceptancePos ≠ contentPos

/-- **`verifier_learns_only_acceptance` — the ZK / epistemic-boundary law (`§6`).**

A witnessed (zero-knowledge) predicate's verifier occupies the `acceptancePos`, which is
**strictly below** the `contentPos`: the verifier learns *acceptance and strictly less than
content*. Formally `acceptancePos < contentPos` — acceptance is dominated by content yet
distinct, so the verifier provably does **not** reach the content position.

This rests on the `Disclosure` separation hypothesis (a *parameter*, the abstract
indistinguishability assumption — see the OPEN note), NOT on an axiom. The honest content:
*given that acceptance and content are distinct positions with `acceptance ⊑ content`, a
verifier confined to `acceptance` is strictly below content* — i.e. the zero-knowledge
verifier never climbs to the witness content. -/
theorem verifier_learns_only_acceptance
    {E : Type u} [PartialOrder E] (D : Disclosure E) :
    D.acceptancePos < D.contentPos :=
  lt_of_le_of_ne D.accept_le_content D.accept_ne_content

/-- **The complementary reading: content is unreachable from acceptance — PROVED.** A
verifier at the acceptance position is **not** at (and not above) the content position:
`¬ contentPos ≤ acceptancePos`. This is the "learns NOT the witness content" half stated
directly: were the verifier able to reach content, antisymmetry would force
`acceptance = content`, contradicting the boundary. -/
theorem content_not_reached_from_acceptance
    {E : Type u} [PartialOrder E] (D : Disclosure E) :
    ¬ D.contentPos ≤ D.acceptancePos := by
  intro hle
  exact D.accept_ne_content (le_antisymm D.accept_le_content hle)

/-
OPEN (`§6`, the abstract ZK indistinguishability). The law above pins the *epistemic
position* faithfully — a ZK verifier sits strictly below witness content in the disclosure
order. The remaining, genuinely-cryptographic obligation is that this order *reflects an
actual indistinguishability*: that no efficient verifier can computationally distinguish a
real witness from a simulated one, so "occupies `acceptancePos`" entails "gains zero
extractable knowledge of the witness." That is a **circuit/cryptographic** obligation
(simulator existence, computational indistinguishability), explicitly NEVER merged into
this Lean law (cf. `Dregg2.Boundary` §8 caveat: `Verify` is a decidable oracle here, its
crypto-soundness is a separate circuit obligation). It enters here as the `Disclosure`
separation *parameter*, not as an axiom: the metatheory says "*if* the kinds separate the
disclosure order thus, *then* the verifier is epistemically confined," and the crypto layer
discharges the antecedent. -/

#assert_axioms verifier_learns_only_acceptance
#assert_axioms content_not_reached_from_acceptance

/-! # §3. Knowledge production — the generative/restrictive duality

`CONSTRUCTIVE-KNOWLEDGE.md §3`: *"authority/knowledge is produced, not merely spent."* A
model where every step only **narrows** (a monotone descent down a meet-semilattice) is
**wrong** — it forbids exactly the patterns that give capabilities their power (Miller's
discoveries). The real dynamics have a **generative half** (introduction, amplification,
mint/factory, endowment) and a **restrictive half** (attenuation, revocation), disciplined
by **one law: *"only connectivity begets connectivity"*** — no ambient authority.

CRUCIAL (`§3`): attenuation is the **meet-semilattice narrowing of ONE edge's rights** — a
single sub-rule — NOT the law of the whole system, and NOT a Heyting residual. We model
that faithfully below: rights live in a `SemilatticeInf` and attenuation is `⊓`-narrowing,
while production (`Confers`) is a *separate*, generative relation. -/

/-- **The authority preorder over rights (`§3`).** Rights/facets of an edge live in a
**meet-semilattice** `(R, ⊓)`: `r₁ ≤ r₂` means *`r₁` is an attenuation of `r₂`* (a subset
of acts; "narrower"). Attenuation — taking a caveat, a facet subset — is exactly `⊓`:
`attenuate r c = r ⊓ c ≤ r`. This is the ONE sub-rule that is meet-semilattice narrowing;
it governs a *single edge's rights*, and is NOT the whole authority law. -/
abbrev Rights (R : Type u) := R

/-- **Attenuation = meet-narrowing — PROVED, kernel-clean (`§3`, the restrictive half).**
Narrowing rights by a caveat `c` (`r ⊓ c`) never exceeds the original: `r ⊓ c ≤ r`. This
is the meet-semilattice "narrow-only" rule for ONE edge's rights — a sub-rule, explicitly
*not* the system law and *not* a Heyting residual `⇨` (no implication is taken; this is
the order-theoretic `inf_le_left`, the bare narrowing). -/
theorem attenuate_narrows {R : Type u} [SemilatticeInf R] (r c : R) :
    r ⊓ c ≤ r :=
  inf_le_left

/-- **`Confers`** — the *generative* conferral relation (`§3`, the generative half:
introduction / amplification). `Confers held conferred` means a knower holding rights
`held` may **produce** an edge carrying rights `conferred`, *provided the conferred rights
do not exceed the held* (`conferred ≤ held`). This is the **non-amplifying** discipline of
`apply_introduce` (`§3`: *"granted permissions exceed introducer's own: amplification
denied"*): you may confer only `≤`-held authority. It is a relation, not a monotone
descent of the whole state — production *grows* the graph (a NEW edge appears), while each
production is itself bounded by held connectivity. -/
def Confers {R : Type u} [Preorder R] (held conferred : Rights R) : Prop :=
  conferred ≤ held

/-- **Conferral is bounded by held authority — PROVED, kernel-clean (`§3`).** The
direction of the non-amplification invariant that is *provable in the meet-semilattice
fragment*: a conferred edge never carries more than the introducer holds. (`apply_introduce`
non-amplification: amplification denied.) -/
theorem confer_no_amplify {R : Type u} [Preorder R] {held conferred : Rights R}
    (h : Confers held conferred) : conferred ≤ held :=
  h

/-- **Conferral composed with attenuation stays bounded — PROVED, kernel-clean (`§3`).**
The generative and restrictive halves *compose without breaking the discipline*: if you
may confer `held`, you may confer any attenuation `held ⊓ c` of it, and the result is still
`≤ held`. This is the faithful "generative produces, restrictive narrows, the bound holds
throughout" — conferring-then-attenuating never escapes the held authority. -/
theorem confer_attenuate {R : Type u} [SemilatticeInf R] (held c : Rights R) :
    Confers held (held ⊓ c) :=
  attenuate_narrows held c

/-- **A reachable knowledge-state (`§3`, the non-forgeability invariant).** Abstractly: a
multiset/predicate of *held* rights, with a one-step `Produces` relation. `state'` is
reachable from `state` in one authorized step iff every right held in `state'` is either
already held in `state` (carried over) **or** is conferred from some right held in `state`
(`Confers`). *"only connectivity begets connectivity"*: no right appears ex nihilo. -/
def Produces {R : Type u} [Preorder R] (state state' : Rights R → Prop) : Prop :=
  ∀ r', state' r' → state r' ∨ ∃ held, state held ∧ Confers held r'

/-- **One step never forges authority — PROVED, kernel-clean (`§3`).** The single-step
core of *"only connectivity begets connectivity"*: after one authorized `Produces` step,
every newly-held right `r'` traces to held authority — either it was already held, or it is
`≤` some previously-held right (conferred, non-amplifying). No right is conjured from
nothing in a step. -/
theorem no_forge_step {R : Type u} [Preorder R] {state state' : Rights R → Prop}
    (h : Produces state state') (r' : Rights R) (hr' : state' r') :
    state r' ∨ ∃ held, state held ∧ r' ≤ held := by
  rcases h r' hr' with hc | ⟨held, hheld, hconf⟩
  · exact Or.inl hc
  · exact Or.inr ⟨held, hheld, confer_no_amplify hconf⟩

/-
OPEN (`§3`, the deep reachability closure of the non-forgeability invariant). The
single-step result `no_forge_step` is PROVED. The full invariant — *"in any state reachable
by ANY finite sequence of authorized productions from the initial knowledge, every held
authority traces back to an authorized production from the initial state"* — is the
**transitive closure** of `Produces` over arbitrary reachable states. Stating it precisely:

    ∀ (reach : ReflTransGen Produces init final), ∀ r, final r →
        ⟨ r descends, through a chain of `Confers` steps, to some `init`-held right ⟩

Its proof is an induction on the `ReflTransGen` chain whose inductive step must thread an
*amplification* account (rights-amplification — `§3` — combines a held amplifier with
another held fact to yield access neither names alone: `unsealer ⊗ box ⊢ contents`), which
needs the amplifier algebra (a `⊗` on rights) not modelled here. It is left OPEN — *not*
because the metatheory is unsure of it, but because faithfully stating the amplifier `⊗`
and the receipt-disclosure typing (`Generative` acts forced on-chain, un-strippable) is a
module of its own. The honest residue here is the *step* law `no_forge_step` plus the
`Produces` relation that the closure quantifies over. -/

#assert_axioms attenuate_narrows
#assert_axioms confer_no_amplify
#assert_axioms confer_attenuate
#assert_axioms no_forge_step

/-! # §4. The coinductive knower — knowledge over unbounded time

`CONSTRUCTIVE-KNOWLEDGE.md §2`: soundness is not a property of one step but of *"the
unbounded life of the cell"* — the cell is **codata** (`νC. µI. StepProof I × (Turn ⇒ C)`),
and *"the cell stays correct forever"* is a **▶-guarded bisimulation to a golden-oracle
reference: the knowledge never drifts from the truth it claims."* Step-completeness (each
step really attests its full invariant) is what makes the coinduction *productive* rather
than a *drifting future that type-checks while leaking*.

We reuse `Dregg2.Boundary`'s `TurnCoalg`/`Sound`/`StepComplete`/`stepComplete_preserves`
directly — that IS the formal home of this `§2` reading; here we give it its
constructive-knowledge name. A knower's *claimed knowledge* is a state-predicate
`Knows : Carrier → Prop`; **no-drift** is: if knowledge is preserved by every
step-invariant-respecting transition, it holds along the *entire* unbounded life. -/

variable {Obs AdmissibleTurn : Type u}

/-- **`knowledge_does_not_drift` — the abstract no-drift reading of coinductive soundness
(`§2`, `§4`).** Let `Knows : Impl.Carrier → Prop` be the knower's *claimed* knowledge
(what it attests to know at a state). If the knower is **step-complete** (every transition
attests the full `StepInv = Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance` — the
contractivity that defeats the drifting future) and `Knows` is **preserved by every
step-invariant-respecting transition**, then `Knows` holds at **every reachable state of
the cell's entire unbounded life** (`Boundary.Execution.Run`). The claimed knowledge never
drifts from the truth it claims.

This is `stepComplete_preserves` (the well-posed, PROVED keystone of `Dregg2.Boundary`)
read under the knowledge lens: `Good := Knows`. We re-derive it (rather than re-prove the
safety machinery) so the no-drift statement is *named and kernel-clean* in the metatheory's
own vocabulary — and so `#assert_axioms` certifies the constructive-knowledge form
inherits no `sorry`. -/
theorem knowledge_does_not_drift
    (Impl : TurnCoalg Obs AdmissibleTurn)
    (conservation authority chainLink obsAdvance :
      Impl.Carrier → AdmissibleTurn → Impl.Carrier → Prop)
    (Knows : Impl.Carrier → Prop)
    (hsc : StepComplete Impl conservation authority chainLink obsAdvance)
    (hpres : ∀ x t, Knows x →
        StepInv Impl conservation authority chainLink obsAdvance x t (Impl.next x t) →
        Knows (Impl.next x t))
    {x y : Impl.Carrier}
    (hlife : Dregg2.Execution.Run (inducedSystem Impl) x y)
    (hx : Knows x) : Knows y :=
  stepComplete_preserves Impl conservation authority chainLink obsAdvance
    Knows hsc hpres hlife hx

/-- **A knower never drifts from its own truth — PROVED, kernel-clean (`§2`, `§4`).** The
reflexive form of coinductive soundness (`Boundary.sound_refl`) read as knowledge: *every
knower is sound relative to itself* — its observed knowledge is bisimilar to the golden
oracle that is *itself*, so along the trivial bisimulation it agrees with the truth it
claims, forever. The substance of "no drift" against a genuine *external* oracle is
`knowledge_does_not_drift` (the safety form); this is the honest reflexive residue. -/
theorem knower_sound_to_itself
    (Impl : TurnCoalg Obs AdmissibleTurn) (x : Impl.Carrier) :
    Sound Impl Impl x :=
  sound_refl Impl x

#assert_axioms knowledge_does_not_drift
#assert_axioms knower_sound_to_itself

/-! # §5. No free copy — linear / substructural knowledge

`CONSTRUCTIVE-KNOWLEDGE.md §4.1`: Conservation is a **substructural / linear logic** —
*"resources cannot be copied or discarded for free."* Read epistemically: **knowledge of a
resource cannot be duplicated for free** — the substructural skeleton of constructive
knowledge. A copy map `Δ : A ⟶ A ⊗ A` realised as an *ordinary* (conserving) turn would
force `count A = count A + count A`, hence (by cancellation) `count A = 0`: only the *empty*
knowledge can be freely copied; copying anything you actually know is non-conservative (it
must MINT — a privileged, receipt-disclosed generator, not an ordinary inference).

We reuse `Dregg2.Core.withholding_no_free_copy` verbatim under its knowledge name. -/

/-- **`knowledge_no_free_copy` — the substructural law of knowledge (`§4.1`), PROVED,
kernel-clean.** In a cancellative resource monoid, a knower cannot *conservatively*
duplicate knowledge of a non-empty resource: if `copy : A ⟶ A ⊗ A` is an **ordinary**
(neither minting nor burning) turn, then `count A = 0`. Equivalently: free duplication of
non-trivial knowledge is impossible; to "copy" real authority you must mint it (a
privileged, disclosed generator — `§3`), never derive it by an ordinary inference. This is
linear/substructural logic appearing as a *security* law (no inflation of authority).

**Derived THROUGH the general no-clone**, not a verbatim renaming. The knowledge-named law
now flows `general ⇒ knowledge-concrete`: it applies `Dregg2.Core.noClone_of_invariant_tensor`
— the `Obj`-polymorphic, category-free linearity core — to the knowledge measure
(`cons.count`), the knowledge tensor (`cons.tensor`, its additivity), and the invariance
datum (an ordinary inference does not change the count, `conservation_ordinary`). The same
general lemma governs the categorical `Σ : C ⥤ Discrete M` view
(`Metatheory.Categorical.no_free_copy`) and the operational view
(`Dregg2.Core.withholding_no_free_copy`); this epistemic statement is a THIRD instantiation,
not a re-narration of either.

NOTE: like `find_realizes`, this is a REST-ON-A-PRIMITIVE keystone, not a PROVED-clean one:
the *logical* content (`count A = count A + count A ⟹ count A = 0` by cancellation +
`tensor_add`) is fully proved in the general lemma, but the invariance datum consumes the
conservation balance `Dregg2.Core.conservation_step` — a typeclass-field obligation (Law 1,
the operational model's obligation, discharged in `Exec.StepComplete`). Hence the
[`ConservesStep`] hypothesis is explicit and this is deliberately NOT `#assert_axioms`'d in
isolation. The honest reading: *given* that ordinary turns conserve, knowledge of a
non-empty resource cannot be freely copied. -/
theorem knowledge_no_free_copy
    {M : Type u} [AddCommMonoid M] [IsCancelAdd M]
    (cons : Dregg2.Core.Conservation M) [Dregg2.Core.ConservesStep cons]
    (A : Dregg2.Core.Cell)
    (copy : Dregg2.Core.Turn A (cons.tensor A A))
    (hcopy : copy.tag = Dregg2.Core.TurnTag.ordinary) :
    cons.count A = 0 :=
  Dregg2.Core.noClone_of_invariant_tensor cons.count cons.tensor cons.tensor_add A
    (Dregg2.Core.conservation_ordinary cons copy hcopy)

/-! # Coda

`CONSTRUCTIVE-KNOWLEDGE.md §7`: this module is the *logic* — what a capability/proof/turn
*is* (the demand⊣supply adjunction, `§1`); who-knows-what (the epistemic/disclosure
boundary, `§2`); the generative/restrictive authority dynamics and the non-forgeability
invariant (`§3`); coinductive soundness over unbounded time (`§4`); and the substructural
no-free-copy skeleton (`§5`). It is candidate-independent: it would be the metatheory of
*any* system built this way. The verification of dregg2 (`Dregg2.*`) discharges these
obligations against the *executable* system — a distinct, larger body of Lean. -/

end Metatheory
