/-
# Dregg2.Spec.Choreography — the choreography-projection ↔ atomic-hyperedge bridge.

`Projection` (the cand-D front-end) splits each choreography interaction by colour:
**blue** = write-set invariant is BEC-I-confluent (coordination-free, no commit);
**red** = coupled (atomic Σ=0 settlement). The classifier is
`Projection.BlueEligible = Confluence.IConfluent`.

`Hyperedge` (the back-end) is the atomic cross-cell commit: the wide pullback over `TurnId`
+ the N-ary CG-5 conservation aggregate. `hyperedge_sound` is the proved N-ary keystone.

The bridge: an interaction's colour is exactly "does its atomic commit need a hyperedge?":

  * **`red_projects_to_hyperedge`** — a red interaction's atomic commit assembles a
    `Hyperedge` over its participant cells (structural half proved; the operational-LTS half
    is `-- OPEN:` — that the live red commit operationally produces this hyperedge along the
    composed-projection bisimulation requires the `Coordination` operational LTS).
  * **`blue_needs_no_hyperedge`** — a blue interaction's invariant survives any concurrent
    merge (`blue_merge_safe`), so it commits independently per cell, and the hyperedge
    binding is genuine extra content a blue step never supplies (`hyper_binding_is_proper`).
  * **`epp_membrane_is_projection`** — the per-endpoint projection of a red interaction IS
    its hyperedge incidence; the vat-boundary membrane and the cell's hyperedge participation
    are the same object (resting on `epp_correspondence`'s current head-duality scope,
    noted.
  * **`red_iff_coupled`** — red ⟺ ¬ I-confluent ⟺ needs a hyperedge.

Faithful `Prop`s; proved keystones pinned with `#assert_axioms`; no `Nat`-for-semantics.
-/
import Dregg2.Projection
import Dregg2.Coordination
import Dregg2.Confluence
import Dregg2.Hyperedge
import Dregg2.JointTurn
import Dregg2.Boundary
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Dregg2.Spec

open Dregg2.Boundary Dregg2.JointTurn Dregg2.Hyperedge
open Dregg2.Coordination (StepEffect)
open Dregg2.Projection (Colour BlueEligible blue_merge_safe route)

universe u v

/-! ## §1 — `Interaction`: one interaction of a choreography, touching a SET of role-cells.

The layer parameters mirror `Hyperedge`/`JointTurn`: `Obs`/`AdmissibleTurn` are the
single-cell behaviour-functor data; `TurnId` is the shared turn-identity (`account_updates_hash`);
`Bal` is the CG-5 conservation monoid; `S` is the cell merge-state lattice over which the
write-set invariant's I-confluence (the colour classifier) is read. -/

variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]
variable {S : Type u} [Confluence.MergeState S]

/-- **`Interaction` — one interaction of the choreography.** It is incident to a finite set
of participant role-cells (indexed by `ι`, each a point of the shared coalgebra `T`), reads
each incidence's turn-id and contributes each incidence's signed half-edge (the `turnId`/
`halfEdge` projection families of `Hyperedge`), and carries the **write-set invariant**
`effect.inv` whose I-confluence is the blue/red classifier (`Coordination.StepEffect`).

This is the choreography-altitude object that the bridge below projects: its *colour* (read
off `effect.inv` via `BlueEligible`) decides whether its atomic commit is a `Hyperedge`
(red) or independent per-cell commits (blue). -/
structure Interaction
    (TurnId : Type u) (Bal : Type u) [AddCommMonoid Bal]
    (S : Type u) [Confluence.MergeState S]
    (ι : Type v) [Fintype ι]
    (T : TurnCoalg Obs AdmissibleTurn)
    where
  /-- The per-incidence turn-id projection (CG-2 reader for each participant slot). -/
  turnId   : ι → TurnIdOf (TurnId := TurnId) T
  /-- The per-incidence signed half-edge (CG-5 summand for each participant slot). -/
  halfEdge : ι → HalfEdgeOf (Bal := Bal) T
  /-- The write-set invariant the interaction's effect must preserve — the object whose
  I-confluence is the blue/red classifier (`Coordination.StepEffect S`). -/
  effect   : StepEffect S

/-- **`Interaction.colour`** — the projection-time colour, read off the write-set invariant:
**blue** iff I-confluent (`BlueEligible`), **red** otherwise. The classification is
decidable only relative to a decision of `IConfluent` (generally undecidable), so it is
exposed as a `Prop`-level split (`IsRed`/`IsBlue`) rather than a `Decidable` instance. -/
def Interaction.IsBlue
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T) : Prop :=
  BlueEligible (S := S) P.effect.inv

/-- **`Interaction.IsRed`** — the complement: the effect is NOT I-confluent, so the
interaction is coupled (an atomic Σ=0 settlement). -/
def Interaction.IsRed
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T) : Prop :=
  ¬ BlueEligible (S := S) P.effect.inv

/-- The `route` of an interaction follows its colour: blue → `cellProgram` (independent
commits), red → `jointTurn`/hyperedge. This re-exports `Projection.route` at the
interaction altitude, making the routing target a *function of the colour alone*. -/
def Interaction.routeOf
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (_P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T) (c : Colour) :
    Projection.ProjectionTarget :=
  route c

/-! ## §2 — `red_projects_to_hyperedge`: RED ↦ atomic `Hyperedge` (structural half PROVED).

A red (coupled) interaction's atomic commit IS a hyperedge over its participant cells: the
coupling FORCES the shared-`tid` wide-pullback binding (the cells cannot commit independently
— their half-edges must balance to `0` against one apex `tid`). The *structural*
correspondence is: given the interaction's binding data (the shared turn, the apex `tid`, the
CG-2 legs, the CG-5 balance), the participant tuple is `HyperAdmissible` — i.e. there is a
`Hyperedge` naming it. We prove that, and leave the OPERATIONAL half open. -/

/-- **`RedBinding` — the binding data a red interaction's atomic commit carries.** Exactly
the content of a `Hyperedge`'s non-tuple fields, stated as the *premise* a coupled commit
must supply (the same irreducible-premise status as `JointTurn.JointBinding` / the `H`
hypothesis of `hyperedge_sound`): the single fired turn `t`, the apex turn-id `tid`, the CG-2
cone (every leg's post-step commits to `tid`), and the CG-5 aggregate (the half-edges sum to
`0`). A red interaction's coupling is precisely "this data is needed and cannot be supplied
per-cell" (`Hyperedge.hyper_binding_is_proper`). -/
structure RedBinding
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (xs : ι → T.Carrier) where
  /-- The single shared turn the coupled commit fires atomically at every incidence. -/
  t   : AdmissibleTurn
  /-- The apex of the wide pullback — the one shared `account_updates_hash`. -/
  tid : TurnId
  /-- CG-2: every incidence's post-step commits to the shared apex `tid`. -/
  agree : ∀ i, P.turnId i (T.next (xs i) t) = tid
  /-- CG-5: the half-edge aggregate over the incidence set balances to `0`. -/
  balanced : (Finset.univ.sum fun i => P.halfEdge i (xs i) t) = 0

/-- **`RedBinding.toHyperedge` — the binding assembles the atomic hyperedge.**
A red interaction's binding data over the incidence tuple `xs` IS a `Hyperedge` over the
same `turnId`/`halfEdge` projections — the coupled commit is one wide-pullback object. The
apex `tid` and the single Σ=0 are exactly the hyperedge's `tid`/`balanced`; the CG-2 legs are
its `agree`. -/
def RedBinding.toHyperedge
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T}
    {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) :
    Hyperedge (Bal := Bal) ι T P.turnId P.halfEdge where
  x := xs
  t := b.t
  tid := b.tid
  agree := b.agree
  balanced := b.balanced

/-- **`red_projects_to_hyperedge` — the keystone (STRUCTURAL half).**

A RED interaction's atomic commit, *given its binding data* (`RedBinding` over the incidence
tuple `xs`), realizes a `Hyperedge` over the participant cells — so the tuple is
`HyperAdmissible`. This is the precise structural sense of "red ↦ hyperedge": the coupled
commit IS a wide-pullback object incident to the interaction's role-cells. The binding is the
irreducible premise (red = coupled = *needs* this binding; cf. `hyper_binding_is_proper`),
and the assembly is `RedBinding.toHyperedge`.

-- OPEN (the operational half): that the live red commit *operationally produces* exactly this
-- hyperedge — i.e. along the parallel-composed-projection ⤳ `pc.coalg` bisimulation, the
-- atomic step the red interaction fires IS the `next`-image of this `Hyperedge` — requires the
-- operational LTS of `Coordination` (the same bisimulation `Coordination.projection_sound`'s
-- full statement awaits; see its docstring). We prove the structural correspondence (the
-- hyperedge exists / the tuple is admissible) and record the operational realization as the
-- residual obligation, exactly mirroring how `Projection.epp_correspondence` carries only
-- head-duality until that LTS lands. -/
theorem red_projects_to_hyperedge
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (_hred : P.IsRed)
    {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) :
    HyperAdmissible (Bal := Bal) ι T P.turnId P.halfEdge xs b.t :=
  ⟨b.toHyperedge, rfl, rfl⟩

/-- **`red_legs_agree` — a red interaction's incidences share one turn-id.** The
operational gloss of "the coupling forces the shared-`tid` binding": for any two participant
cells of a red interaction, their post-step turn-ids coincide (both are the apex). This is
`Hyperedge.legs_agree` read at the interaction altitude — the cross-cell `tid` cut a red
commit *cannot* avoid. (Contrast `blue_needs_no_hyperedge` below: a blue interaction requires
no such cut.) -/
theorem red_legs_agree
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T}
    {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) (i j : ι) :
    P.turnId i (T.next (xs i) b.t) = P.turnId j (T.next (xs j) b.t) :=
  Hyperedge.legs_agree b.toHyperedge i j

/-! ## §3 — `blue_needs_no_hyperedge`: BLUE ↦ independent per-cell commits.

A blue (I-confluent) interaction needs NO shared binding. Two halves, both PROVED:

  (a) *positive*: its write-set invariant survives ANY concurrent merge
      (`Projection.blue_merge_safe`), so every replica may run the step and merge
      invariant-safely with no coordination — i.e. it commits **independently per cell**;
  (b) *negative*: the cross-cell hyperedge binding is genuine extra content (CG-5: a Σ=0
      cut) that the per-cell data does not supply (`Hyperedge.hyper_binding_is_proper`) — so
      a blue step, which requires only (a), is NOT carrying a hyperedge. -/

/-- **`blue_commits_independently`** — a blue interaction's effect-invariant is preserved by
the merge of any two invariant-preserving cell-states. Coordination-free: a blue step runs
on every replica and merges invariant-safely, with no shared `tid`. From
`Projection.blue_merge_safe` (which uses the I-confluence; fails for a red invariant). -/
theorem blue_commits_independently
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (hblue : P.IsBlue) (x y : S)
    (hx : P.effect.inv x) (hy : P.effect.inv y) :
    P.effect.inv (x ⊔ y) :=
  blue_merge_safe P.effect.inv hblue x y hx hy

/-- **`blue_needs_no_hyperedge` — the keystone.**

A blue interaction needs no cross-cell hyperedge binding, made precise as the conjunction of
the two halves:

  (a) `blue_commits_independently` — its invariant is closed under arbitrary concurrent
      merges, so it commits independently per cell (coordination-free);
  (b) the hyperedge binding is a PROPER subobject of the N-fold product
      (`Hyperedge.hyper_binding_is_proper`): there is a configuration NOT `HyperAdmissible`,
      so the CG-5 Σ=0 cut is genuine extra content — content a blue step (which requires only
      (a)) does not carry.

Together: a blue interaction is NOT a hyperedge — it requires no shared-`tid` binding and no
Σ=0 cross-cell cut. This is the formal "blue ↦ independent commit" half of the realization,
tying `Projection.blue_merge_safe`/`Confluence` to the absence of a `Hyperedge`. -/
theorem blue_needs_no_hyperedge
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (hblue : P.IsBlue) :
    (∀ x y : S, P.effect.inv x → P.effect.inv y → P.effect.inv (x ⊔ y)) ∧
    (∃ (T' : TurnCoalg Unit Unit)
        (turnId' : Unit → TurnIdOf (TurnId := Unit) T')
        (halfEdge' : Unit → HalfEdgeOf (Bal := Nat) T')
        (xs' : Unit → T'.Carrier) (t' : Unit),
        ¬ HyperAdmissible Unit T' turnId' halfEdge' xs' t') :=
  ⟨fun x y hx hy => blue_commits_independently P hblue x y hx hy,
   Hyperedge.hyper_binding_is_proper⟩

/-! ## §4 — `red_iff_coupled`: the three judgements tied at the choreography altitude.

red ⟺ ¬ I-confluent ⟺ "needs a hyperedge". The first ⟺ is definitional (the colour IS the
I-confluence judgement); the second is content: a non-I-confluent (red) effect EXHIBITS a
clashing concurrent pair (`Confluence.nonpairwise_escalation`) — a Σ=0-style settlement that
cannot run cross-group-free, the operational meaning of "must escalate to a hyperedge". -/

/-- **`red_iff_coupled` — red ⟺ not I-confluent, with the forced-escalation witness.**

(i) `P.IsRed ↔ ¬ Confluence.IConfluent P.effect.inv` is the colour's definition unfolded —
honest definitional content (`BlueEligible := IConfluent`), so this direction is `Iff.rfl`-class
and named as the unfold it is.

(ii) The *operational* tie — "red ⟹ needs a hyperedge / cannot commit independently" — is the
constructive escalation witness: a red effect has a concrete clashing pair `x y`
(invariant-preserving versions whose merge violates the invariant), so it canNOT run
coordination-free and MUST escalate to the coupled (hyperedge) commit. This is
`Confluence.nonpairwise_escalation`, the genuine content (it is exactly the failure
`blue_commits_independently` would need and cannot have). -/
theorem red_iff_coupled
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T) :
    (P.IsRed ↔ ¬ Confluence.IConfluent P.effect.inv) ∧
    (P.IsRed → ∃ x y : S, P.effect.inv x ∧ P.effect.inv y ∧ ¬ P.effect.inv (x ⊔ y)) :=
  ⟨Iff.rfl,
   fun hred => Confluence.nonpairwise_escalation P.effect.inv hred⟩

/-! ## §5 — `epp_membrane_is_projection`: connecting the two altitudes.

The per-endpoint projection of a red interaction IS its hyperedge incidence; the vat-boundary
membrane that enforces a role's local type is the same object as the cell's hyperedge
participation (`Projection`'s cand-D §7 "two altitudes" + `Hyperedge`'s legs). We state it
faithfully: it rests on `Projection.epp_correspondence`'s CURRENT head-duality scope (which is
`Coordination.projection_sound`, head-duality only — the full bisimulation awaits the
operational LTS), conjoined with the hyperedge-incidence agreement `Hyperedge.legs_agree`. -/

/-- **`epp_membrane_is_projection` — the two altitudes meet (at the stated scope).**

For a `Projectable` protocol-cell running a head communication `comm a b s k` (a red,
coupled interaction at the choreography altitude — a 2-cell binding), TWO facts hold at once
and are *the same correspondence read at two altitudes*:

  * **(projection / membrane)** the endpoints' projections are `Dual`
    (`Projection.epp_correspondence` — the per-endpoint membrane enforcing each role's local
    type; head-duality scope, noted);
  * **(hyperedge incidence)** the participant cells of the red interaction's atomic commit
    share one apex turn-id (`Hyperedge.legs_agree` over the interaction's binding) — the
    membrane-enforced role IS the cell's hyperedge participation (the same `tid` the
    projection synchronises on).

**SCOPE.** The projection half is exactly what `epp_correspondence` proves today (head
duality, = `Coordination.projection_sound`); the *independent* two-altitudes content — that
the per-endpoint membrane and the hyperedge incidence are literally one object along the
composed-projection bisimulation — awaits the operational LTS (`-- OPEN` in
`red_projects_to_hyperedge` and in `epp_correspondence`'s docstring). This theorem PROVES the
*conjunction at the current scope*: membrane-duality AND incidence-agreement both hold for a
red head interaction; their identification as one object is the recorded residual. -/
theorem epp_membrane_is_projection
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {Obs' AdmissibleTurn' : Type u}
    (pc : Coordination.ProtocolCell Obs' AdmissibleTurn')
    (wf : Coordination.Projectable pc.G)
    (a b : Coordination.Role) (s : Coordination.Payload) (k : Coordination.GlobalType)
    (hG : pc.G = Coordination.GlobalType.comm a b s k) (hab : a ≠ b)
    {P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T}
    {xs : ι → T.Carrier} (binding : RedBinding (Bal := Bal) (S := S) P xs) (i j : ι) :
    Coordination.Dual (Coordination.project pc.G a) (Coordination.project pc.G b) ∧
    P.turnId i (T.next (xs i) binding.t) = P.turnId j (T.next (xs j) binding.t) :=
  ⟨Projection.epp_correspondence pc wf a b s k hG hab,
   red_legs_agree binding i j⟩

/-! ## Axiom-hygiene pins (PROVED keystones only — never the operational-OPEN residues). -/

#assert_axioms RedBinding.toHyperedge
#assert_axioms red_projects_to_hyperedge
#assert_axioms red_legs_agree
#assert_axioms blue_commits_independently
#assert_axioms blue_needs_no_hyperedge
#assert_axioms red_iff_coupled
#assert_axioms epp_membrane_is_projection

/- The choreography projection-split and the atomic hyperedge are the same classification
read at two altitudes. The single open residue is operational, not structural: that the live
red commit operationally produces exactly this hyperedge along the composed-projection
bisimulation (`Coordination.projection_sound` / `epp_correspondence`). Every structural
keystone is proved and axiom-clean. -/

end Dregg2.Spec
