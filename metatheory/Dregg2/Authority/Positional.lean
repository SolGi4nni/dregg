/-
# Dregg2.Authority.Positional — the l4v integrity lift = the vat-boundary law.

This module is the **literal Lean transcription of the seL4/l4v object-integrity
theorem** (`integrity_obj_atomic`, `proof/access-control/Access.thy`), specialized to
the dregg2 vat model. The l4v case-split IS the vat-boundary law:

  * l4v `troa_lrefl`  : `l ∈ subjects ⟹ integrity_obj_atomic … ko ko'`
      "a subject can make ANY change to an object it owns — no policy edge required."
    ↦ **intra-vat**: own-it ⟹ arbitrary change, admitted by the *trivial* witness.

  * l4v `troa_ntfn`/`troa_ep`/… : a non-owner may change `ko` ONLY along an
      *authorized policy edge* `(s, auth, l) ∈ pasPolicy aag` for the specific
      `auth` that the object kind permits.
    ↦ **cross-vat**: change admitted ⟺ `Discharged P w` (a verified witness for
      an edge the policy authorizes) — the crypto substitution replaces l4v's
      positional `∃ (s,auth,l) ∈ pasPolicy` with the decidable `Verify P w = true`.

Authority confinement (`pas_refined`'s `state_objs_in_policy`) lifts to: the policy
is an *upper bound* on conferred authority — `authority ⊆ caps`, an invariant, never
growth. The `LossyMorphism` (`ρ_in`/`ρ_out`, attenuation-only) lifts structural
unforgeability to cryptographic unforgeability with loss = revocation-by-construction.

-- l4v reference statements (Access.thy / Syscall_AC.thy), transcribed verbatim in
-- the docstrings below so the template is self-contained.
-/
import Dregg2.Laws

namespace Dregg2.Authority

open Dregg2.Laws

/-! ## The capability model (lift of l4v `cap` + `cap_auth_conferred`) -/

/-- Authority kinds. Lift of l4v `auth` (the labels on policy edges:
`Receive, SyncSend, Notify, Reset, Grant, Call, Reply, Control`). -/
inductive Auth where
  | read | write | grant | call | reply | reset | control
  deriving DecidableEq, Repr

/-- Trust roots / labels. Lift of l4v `'a` (the agent-label type, ranged over by
`pasObjectAbs aag x`, `pasSubject aag`). In dregg2 these are vats. -/
abbrev Label := Nat

/-- A capability. Lift of l4v `cap`. A cap names a target object and carries rights.
The full l4v `cap` datatype is large (`NullCap`, `EndpointCap oref badge r`,
`ReplyCap`, `CNodeCap`, `ThreadCap`, `ArchObjectCap …`); we keep the rights-bearing
core that determines `cap_auth_conferred`. -/
inductive Cap where
  | null
  /-- `endpoint target rights` ~ l4v `EndpointCap oref badge r`. -/
  | endpoint (target : Label) (rights : List Auth)
  /-- `node target` ~ l4v `CNodeCap`/`ThreadCap`/`Control`-conferring caps. -/
  | node (target : Label)
  deriving DecidableEq, Repr

/-- **`cap_auth_conferred`** — the authority a cap confers. Verbatim l4v
(`Access.thy:118`):
```
cap_auth_conferred cap ≡ case cap of
    NullCap ⇒ {}
  | UntypedCap … ⇒ {Control}
  | EndpointCap oref badge r ⇒ cap_rights_to_auth r True
  | CNodeCap … | ThreadCap … | … ⇒ {Control}
``` -/
def capAuthConferred : Cap → List Auth
  | .null            => []
  | .endpoint _ r    => r
  | .node _          => [Auth.control]

/-- The set of caps held at (the slots of) a label — the cell's slot-table. -/
abbrev Caps := Label → List Cap

/-- A policy edge `(s, auth, l)`: subject `s` may exert `auth` on label `l`.
Lift of a single element of l4v `pasPolicy aag : ('a × auth × 'a) set`. -/
structure PolicyEdge where
  subject : Label
  auth    : Auth
  target  : Label
  deriving DecidableEq, Repr

/-- The authority policy graph. Lift of l4v `pasPolicy aag`. -/
abbrev Policy := List PolicyEdge

/-- `aag_subjects_have_auth_to`-style membership: is the edge in the policy? -/
def authorizedEdge (pol : Policy) (e : PolicyEdge) : Prop := e ∈ pol

/-! ## `pas_refined` invariant: authority ⊆ caps (no growth) -/

/-- **`pas_refined` (the `state_objs_in_policy` clause), lifted.** Verbatim l4v
(`Access.thy:312`) requires, among wellformedness clauses,
`auth_graph_map (pasObjectAbs aag) (state_objs_to_policy s) ⊆ pasPolicy aag`.

Here: every authority actually conferred by a held cap is *bounded above* by a
policy edge. The policy is an upper bound; runtime authority never exceeds it. -/
def PasRefined (pol : Policy) (caps : Caps) : Prop :=
  ∀ (s t : Label) (c : Cap) (a : Auth),
    c ∈ caps s → c = .endpoint t (capAuthConferred c) → a ∈ capAuthConferred c →
      authorizedEdge pol ⟨s, a, t⟩

/-! ## The integrity case-split = the vat-boundary law

State the change-relation `Integrity`, lift of l4v `integrity_obj_atomic`. -/

end Dregg2.Authority

-- The boundary relation needs the verify/find seam; reopen with the predicate
-- algebra `P`/witness `W` and an abstract cell-object state `KO` in scope.
namespace Dregg2.Authority

open Dregg2.Laws

/- A cell-object state (lift of l4v `kernel_object option`, the `ko`/`ko'`).
Kept fully abstract here; instantiated per candidate in the soundness module.
`W` is an *explicit* parameter of `Integrity` below: it appears only inside the
`cross` constructor's existential and in the `Verifiable P W` instance, never in
an index, so it cannot be inferred at use sites and must be supplied positionally. -/
variable {P : Type*} {KO : Type*}

/-- **The vat-boundary integrity relation** = lift of `integrity_obj_atomic`.

`Integrity owner subjects ko ko'` holds iff the change `ko ⟶ ko'` is admissible.
Two constructors mirror the l4v case-split exactly:

* `intra` ↦ l4v `troa_lrefl` (`l ∈ subjects`): the owning vat may make an
  ARBITRARY change to its own object — admitted by the **trivial witness**, NO
  policy edge consulted.
* `cross` ↦ l4v `troa_ntfn`/`troa_ep`/… : a non-owner change is admitted ONLY when
  a witness *discharges* the admissibility predicate `p` for the change, i.e.
  `Discharged p w` — the decidable replacement for l4v's positional
  `∃ (s,auth,l) ∈ pasPolicy aag`. -/
inductive Integrity (W : Type*) [Verifiable P W]
    (owner : Label) (subjects : List Label)
    (p : KO → KO → P) : KO → KO → Prop where
  /-- l4v `troa_lrefl`: own-it ⟹ arbitrary change, trivial witness. -/
  | intra {ko ko' : KO} (h : owner ∈ subjects) :
      Integrity W owner subjects p ko ko'
  /-- l4v authorized-edge rules: cross-vat change ⟺ a verified witness exists. -/
  | cross {ko ko' : KO} (w : W) (h : Discharged (p ko ko') w) :
      Integrity W owner subjects p ko ko'

/-- **Vat-boundary law, theorem form (lift of `integrity_subjects` / the
`call_kernel_integrity` Hoare triple).** Verbatim l4v target
(`Syscall_AC.thy:1311`):
```
⦃ pas_refined aag and einvs and … and (λs. s = st) ⦄
  call_kernel ev
⦃ λ_. integrity aag X st ⦄
```
i.e. *under `pas_refined`, every reachable post-state stands in the integrity
relation to the pre-state.* Lifted: any admissible turn respects `Integrity`. -/
theorem boundary_law
    [Verifiable P W]
    (owner : Label) (subjects : List Label) (pol : Policy) (caps : Caps)
    (p : KO → KO → P) (ko ko' : KO)
    (refined : PasRefined pol caps)
    -- The real "this is an admissible kernel transition" obligation: the l4v case-split.
    -- Either the change is *intra*-vat (owner ∈ subjects, l4v `troa_lrefl`) or it is
    -- *cross*-vat with a discharged witness for an authorized edge (l4v `troa_ntfn`/…).
    (adm : owner ∈ subjects ∨ ∃ w : W, Discharged (p ko ko') w) :
    Integrity W owner subjects p ko ko' := by
  -- Faithful integrity case-split (mirrors l4v `integrity_obj_atomic`):
  rcases adm with hmem | ⟨w, hw⟩
  · exact Integrity.intra hmem            -- l4v `troa_lrefl`: own-it ⟹ arbitrary change
  · exact Integrity.cross w hw            -- l4v authorized-edge: verified witness exists

/-- **Authority confinement (companion to the boundary law).** Lift of
`call_kernel_pas_refined`: `pas_refined` is preserved — authority never grows
beyond the policy upper bound across a turn. -/
theorem confinement_preserved
    (pol : Policy) (caps caps' : Caps)
    (refined : PasRefined pol caps)
    -- The real "caps' is the post-state of an authority-non-increasing turn" obligation:
    -- a turn never *adds* a cap to any slot (it may only drop/attenuate). This is the
    -- lift of l4v `call_kernel_pas_refined`'s monotonicity — authority never grows.
    (noGrow : ∀ s, caps' s ⊆ caps s) :
    PasRefined pol caps' := by
  -- Every cap held in caps' is held in caps, which is policy-bounded by `refined`.
  intro s t c a hc hceq ha
  exact refined s t c a (noGrow s hc) hceq ha

/-! ## LossyMorphism: structural ⟶ cryptographic unforgeability (attenuation-only) -/

/-- A boundary morphism with an *inbound* restriction `ρ_in` and an *outbound*
restriction `ρ_out`. Crossing a vat boundary may only attenuate authority (remove rights
/ narrow predicates); it can never amplify. Attenuation is part of the definition: the
structure carries `in_le`/`out_le` as fields (a non-attenuating endomap is not a
`LossyMorphism`). -/
structure LossyMorphism (P : Type*) [LE P] where
  ρ_in  : P → P
  ρ_out : P → P
  /-- The inbound restriction never amplifies. -/
  in_le  : ∀ a, ρ_in a ≤ a
  /-- The outbound restriction never amplifies. -/
  out_le : ∀ a, ρ_out a ≤ a

/-- **`lossy_attenuation_only`** — `ρ_in`/`ρ_out` are attenuation-only (their bounds are
carried as structure fields), so structural unforgeability lifts to cryptographic
unforgeability: a right not carried across the boundary is unexercisable on the far side. -/
theorem lossy_attenuation_only
    [HeytingAlgebra P] (m : LossyMorphism P) (a : P) :
    m.ρ_in a ≤ a ∧ m.ρ_out a ≤ a :=
  And.intro (m.in_le a) (m.out_le a)

end Dregg2.Authority
