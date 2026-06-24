/-
# Dregg2.Circuit.Spec.CapFamilyAbstractBinding — binding the CAP family (delegation / revocation /
refresh) to the abstract `Metatheory.Dynamics` verb meta-law, via the shared adapter.

The cap-family authority leg is the SAME `authConnects ⟹ AuthorizedProduction` law (Miller, "only
connectivity begets connectivity"), specialized to the delegation gate. Three footprint shapes, all
`delta = 0` (only `caps`/`delegations` move; value idle):

  * **GRANT** (`delegate`, `delegateAtten` — and by the same shape `grantCap`/`introduce`/`attenuate`,
    which are the unattenuated/attenuated grant): the gate
    `(caps del).any (confersEdgeTo t) = true` (the delegator HOLDS a `t`-conferring cap) is a
    connectivity gate. The delegator PRODUCES the conferred edge it already holds — an authorized,
    NON-AMPLIFYING production (`delegateAtten_spec_non_amplifying`: conferred rights ⊆ held). We feed
    the gate boolean to the shared `gate_covers_production` bridge.

  * **REVOKE** (`revoke`, `revokeDelegation`): removes edges. THE IMPEDANCE (worth naming): `RevokeSpec`'s
    guard is literally `True` (the spec carries NO authority gate — revoke is permissionless at the
    spec tier; a holder filters its OWN slot). Revocation is not a production — it REMOVES connectivity,
    producing NOTHING. So its authority leg is genuinely IDLE (produced `∅`, the honest shape via
    `idle_authorized_production`), exactly like emitEvent. It still FIRES and is governed by the
    meta-law; there is simply no authority to amplify, so the mutation tooth does not apply.

  * **REFRESH** (`refreshDelegation`): the gate `stateAuthB s.kernel.caps actor child = true ∧ …` —
    a `stateAuthB` authority over `child`, like the state-write family. The authorized production is
    over the held `stateAuthB` edge; `caps` is unchanged, `delegations` advances.

DISCIPLINE: every `*_refines_abstract_verb` `#assert_axioms`'d kernel-clean, sorry-free; the shared
mutation tooth reds for the gated grant/refresh; revoke is the idle-leg honest shape.
-/
import Dregg2.Circuit.Spec.AbstractVerbAdapter
import Dregg2.Circuit.Spec.authorityunattenuated
import Dregg2.Circuit.Spec.authorityattenuation
import Dregg2.Circuit.Spec.authorityrevocation
import Dregg2.Circuit.Spec.refreshdelegation

namespace Dregg2.Circuit.Spec.CapFamilyAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)
open Dregg2.Resource
open Metatheory.Dynamics
open Dregg2.Circuit.Spec.AbstractVerbAdapter
open scoped Dregg2.Resource.ResourceAlgebra

/-! ## The shared gated-cap verb (grant / refresh): a `delta=0` authorized production.

`capGrantVerb adm g` is the cap verb whose authority leg PRODUCES the conferred `control` edge under
the held bound the connectivity gate `g` grants. delegate/delegateAtten feed
`g := (caps del).any (confersEdgeTo t)`; refreshDelegation feeds `g := stateAuthB caps actor child`. -/

/-- The shared gated-cap verb at a boolean connectivity/authority gate `g`. -/
def capGrantVerb {P : Type} (adm : Admission P) (g : Bool) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (heldOfGate g) controlEdge

/-- **`capGrantVerb_fires`** — an accepting gate + an admitting witness fire the gated-cap verb.
Each cap effect feeds its own connectivity/authority gate fact here. NOT `rfl` — runs the bridge. -/
theorem capGrantVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (g : Bool) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) (hg : g = true) :
    Fires (W := W) (capGrantVerb adm g) w :=
  stateWriteVerb_fires adm (heldOfGate g) controlEdge w hadm (gate_covers_production g hg)

/-! ## §delegate (unattenuated grant — the grantCap/introduce shape). -/

/-- **`delegate_refines_abstract_verb`** — a committed `DelegateSpec` fires the gated-cap verb. The
authority fact is the connectivity gate `(caps del).any (confersEdgeTo t) = true` (`delegateGuard`,
`hspec.1`): the delegator holds a `t`-conferring cap, an authorized production. This is the SAME shape
`grantCap`/`introduce` inhabit (the unattenuated grant). REAL proof, runs the bridge. -/
theorem delegate_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState)
    (hspec : AuthorityUnattenuated.DelegateSpec s del rec t s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W)
      (capGrantVerb adm ((s.kernel.caps del).any (fun cap => confersEdgeTo t cap))) w :=
  capGrantVerb_fires adm _ w hadm hspec.1

theorem delegate_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (del rec t : CellId) (s' : RecChainedState)
    (hspec : AuthorityUnattenuated.DelegateSpec s del rec t s')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid
      ((capGrantVerb adm ((s.kernel.caps del).any (fun cap => confersEdgeTo t cap))).pre ⊙ fr)) :
    ResourceAlgebra.valid
      ((capGrantVerb adm ((s.kernel.caps del).any (fun cap => confersEdgeTo t cap))).post ⊙ fr) :=
  kernel_meta_law _ w (delegate_refines_abstract_verb adm w s del rec t s' hspec hadm) fr hfr

/-! ## §delegateAtten (attenuated grant — the attenuate shape). -/

/-- **`delegateAtten_refines_abstract_verb`** — a committed `DelegateAttenSpec` fires the gated-cap
verb at the SAME connectivity gate (`DelegateAttenGuard`, `hspec.1`). The conferred edge is
ATTENUATED (`delegateAtten_spec_non_amplifying`: conferred rights ⊆ held), an authorized,
non-amplifying production — exactly the abstract `AuthorizedProduction` content. REAL proof. -/
theorem delegateAtten_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (del rec t : CellId) (keep : List Auth) (s' : RecChainedState)
    (hspec : AuthorityAttenuation.DelegateAttenSpec s del rec t keep s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W)
      (capGrantVerb adm ((s.kernel.caps del).any (fun cap => confersEdgeTo t cap))) w :=
  capGrantVerb_fires adm _ w hadm hspec.1

/-! ## §refreshDelegation. -/

/-- **`refreshDelegation_refines_abstract_verb`** — a committed `RefreshDelegationSpec` fires the
gated-cap verb at the `stateAuthB` authority gate (`RefreshDelegationGuard`, `(hspec.1).1`). The
authorized production is over the held `stateAuthB` edge; `caps` is unchanged, `delegations` advances.
REAL proof, runs the bridge. -/
theorem refreshDelegation_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor child : CellId) (s' : RecChainedState)
    (hspec : RefreshDelegation.RefreshDelegationSpec s actor child s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (capGrantVerb adm (stateAuthB s.kernel.caps actor child)) w :=
  capGrantVerb_fires adm _ w hadm (hspec.1).1

/-! ## §revoke / revokeDelegation — THE IDLE-LEG IMPEDANCE (removal, no production).

`RevokeSpec`'s guard is `True`: the spec carries no authority gate (a holder filters its OWN slot).
Revocation REMOVES connectivity, producing nothing — its authority leg is genuinely IDLE
(`produced := ∅`, covered by any held bundle). The honest shape for a removal/permissionless effect.
`revokeDelegation` shares this shape (it removes a delegation edge). -/

/-- **`revokeVerb adm`** — the revoke verb: value idle, authority leg IDLE (produced `∅` — a removal
produces nothing), evidence + state idle. The pure cap-edge-removal shape. -/
def revokeVerb {P : Type} (adm : Admission P) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights)

/-- **`revoke_refines_abstract_verb`** — a committed `RevokeSpec` fires the (idle-authority) revoke
verb under any admitting witness. The authority leg is the idle production (`∅`), trivially authorized
— faithfully reflecting that revocation produces no new connectivity. The verb FIRES and is governed
by the meta-law. -/
theorem revoke_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (holder t : CellId) (st' : RecChainedState)
    (hspec : AuthorityRevocation.RevokeSpec st holder t st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (revokeVerb adm) w :=
  stateWriteVerb_fires adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights) w hadm
    (idle_authorized_production _)

theorem revoke_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (holder t : CellId) (st' : RecChainedState)
    (hspec : AuthorityRevocation.RevokeSpec st holder t st')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((revokeVerb adm).pre ⊙ fr)) :
    ResourceAlgebra.valid ((revokeVerb adm).post ⊙ fr) :=
  kernel_meta_law _ w
    (revoke_refines_abstract_verb adm w st holder t st' hspec hadm) fr hfr

#assert_axioms delegate_refines_abstract_verb
#assert_axioms delegate_preserves_product_validity
#assert_axioms delegateAtten_refines_abstract_verb
#assert_axioms refreshDelegation_refines_abstract_verb
#assert_axioms revoke_refines_abstract_verb
#assert_axioms revoke_preserves_product_validity

/-! ## §non-vacuity + the shared mutation tooth. -/

/-- A trivial-but-real verifier seam for the non-vacuity witnesses. -/
instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`capGrantVerb_fires_nonvacuous`** — the gated-cap family's refinement conclusion is inhabited:
at an accepting gate, the cap verb FIRES under the trivial-but-real admission. -/
theorem capGrantVerb_fires_nonvacuous :
    Fires (W := Unit) (capGrantVerb (P := Unit) ⟨()⟩ true) () :=
  capGrantVerb_fires (P := Unit) (W := Unit) ⟨()⟩ true () rfl rfl

/-- **`capGrant_refines_needs_authorized_production` — the shared mutation tooth, PROVED.** Were a
cap grant's authority leg an UNAUTHORIZED amplification (conferring `write` under a held bound of only
`read` — the amplifying delegation the non-amplification keystone forbids), it would NOT be `Fpu` — so
the verb could NOT `Fires`. The gated cap-family's authority is load-bearing. (Revoke is exempt — its
leg is idle, there is no authority to amplify.) -/
theorem capGrant_refines_needs_authorized_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  gateProduction_not_fpu

#assert_axioms capGrantVerb_fires_nonvacuous
#assert_axioms capGrant_refines_needs_authorized_production

/-! ## §Coda.

The cap family is bound as governed instances of `Metatheory.Verb`: delegate/delegateAtten (and the
grantCap/introduce/attenuate grant shapes they share) discharge `Fires (capGrantVerb …)` from their
connectivity gate `(caps del).any (confersEdgeTo t)` via the shared `gate_covers_production` bridge —
the conferred edge an authorized, non-amplifying production (`delegateAtten_spec_non_amplifying`:
conferred ⊆ held); refreshDelegation via its `stateAuthB` gate. Revoke (and revokeDelegation) is the
IDLE-LEG honest shape — a removal produces no connectivity, so its authority leg is idle (`produced
:= ∅`). The shared mutation tooth shows the gated-grant authority is load-bearing; the value leg is
idle throughout (`delta = 0`: cap operations move authority, not value).
-/

end Dregg2.Circuit.Spec.CapFamilyAbstractBinding
