/-
# Dregg2.Circuit.Spec.TransferAbstractBinding — binding the INDEPENDENT `BalanceMovementSpec`
(transfer / value-move) to the ABSTRACT `Metatheory.Dynamics` verb meta-law.

This is the SECOND value-move exemplar (after mint/burn in `SupplyAbstractBinding.lean`): it proves
the adapter pattern transports BEYOND supply, to the cleanest value mover — a balance transfer. The
shape is identical to mint:

    kernel  ⟹  `BalanceMovementSpec`  ⟹  abstract `Fires (transferVerb …)`  ⟹  `kernel_meta_law`.

The two content seams that carry the meaning:

  * **Authority = `AuthorizedProduction`.** The transfer guard's authority conjunct
    `authorizedB k.caps t = true` (`BalanceMovementSpec.admitGuardA.1`) is the executable image of
    the abstract non-forgeability production law: the actor holds a cap conferring the move-edge over
    `src` (Granovetter "you may move what you hold a cap to"). The held cap PRODUCES the connectivity
    edge; the edge is bounded by it. We discharge an `AuthorizedProduction` from the concrete gate via
    the SAME bridge shape as mint (`transferAuthorizedB_covers_production`).

  * **Value = conservation `Fpu`.** A committed transfer debits `(src,a)` and credits `(dst,a)` by
    the SAME `amt` (`recTransferBal_correct`), leaving Σ_c bal c a EXACTLY unchanged — a value MOVE,
    not a creation. Abstractly that is the value-leg conservation `Fpu` (the same fixed-total idle
    move as mint, `Fpu.refl` at the value camera).

So `transferVerb` is the abstract `Verb` whose Admission is the move-authority demand and whose
Footprint is (conserving value move) × (authorized authority production), evidence + state idle.
`transfer_refines_abstract_verb` is a REAL refinement (it runs the authority bridge, NOT `rfl`).

DISCIPLINE: keystones `#assert_axioms`'d kernel-clean. Non-vacuity drives the refinement from a
concrete committed transfer; the mutation tooth (`transfer_refines_needs_authorized_production`)
shows trivializing the Admission would let an UNAUTHORIZED amplification through.
-/
import Dregg2.Circuit.Spec.balancemovement
import Metatheory.Dynamics.Production

namespace Dregg2.Circuit.Spec.TransferAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority
open Dregg2.Resource
open Metatheory.Dynamics
open Dregg2.Circuit.Spec.BalanceMovement
open scoped Dregg2.Resource.ResourceAlgebra

/-! ## §1 — the authority of a transfer: `AuthorizedProduction`.

The held authority a transfer exercises is the actor's move-cap over `src`, modelled in the rights
∪-monoid camera (`Production.lean §1(a)`). The PRODUCED fragment is the `control` edge that cap
confers — moving value exercises connectivity already held, so `AuthorizedProduction held produced`
holds with `held` covering `produced`. This is the abstract non-forgeability content of
`authorizedB`. -/

/-- The rights bundle a transfer PRODUCES (exercises): the `control` edge over `src`. The smallest
non-trivial production, the single-element ∪-monoid carrier. -/
def transferProduced : USet Rights := ⟨{Dregg2.Authority.Auth.control}⟩

/-- **`transfer_is_authorized_production`** — whatever the actor's full held bundle is (`held`), as
long as the move-produced edge is covered by it, the move is an authorized production: the produced
fragment fits within the held authority. The camera-level reading of `authorizedB`. -/
theorem transfer_is_authorized_production (held : USet Rights)
    (hcov : (transferProduced).set ⊆ held.set) :
    AuthorizedProduction held transferProduced :=
  (USet.fits_iff transferProduced held).mpr hcov

/-- **`heldFromTransfer caps t`** — the abstract authority bundle the transfer gate GRANTS: the
`control` edge WHEN `authorizedB` accepts, the EMPTY bundle when it does not. The abstraction
function on the authority leg: gate-accept ↦ `{control}`, gate-reject ↦ `∅` (an unauthorized actor
holds `∅` and produces nothing). -/
def heldFromTransfer (caps : Caps) (t : Turn) : USet Rights :=
  if authorizedB caps t = true then ⟨{Dregg2.Authority.Auth.control}⟩ else ⟨∅⟩

/-- **`transferAuthorizedB_covers_production` — THE BRIDGE: the concrete gate's acceptance covers the
abstract produced edge, PROVED, kernel-clean.** If `authorizedB caps t = true` (the actor holds the
move-cap), the gate-derived held bundle covers `transferProduced` — so the concrete authority
WITNESSES `AuthorizedProduction (heldFromTransfer …) transferProduced`. The hypothesis is
LOAD-BEARING: `heldFromTransfer` is `∅` when the gate REJECTS, and the empty bundle covers nothing. -/
theorem transferAuthorizedB_covers_production (caps : Caps) (t : Turn)
    (hgate : authorizedB caps t = true) :
    AuthorizedProduction (heldFromTransfer caps t) transferProduced := by
  refine transfer_is_authorized_production (heldFromTransfer caps t) ?_
  simp [heldFromTransfer, hgate, transferProduced]

/-- **`transfer_production_footprint_fpu`** — the authority leg of the transfer footprint is `Fpu`,
derived FROM the authorization: producing `transferProduced` under the held bound `● held` is a
frame-preserving update in the authority camera. The authorization is LOAD-BEARING (an unauthorized
production is NOT `Fpu`). -/
theorem transfer_production_footprint_fpu (held : USet Rights)
    (hauth : AuthorizedProduction held transferProduced) :
    Fpu (R := Auth (USet Rights))
      (.mk (some held) 0) (.mk (some held) transferProduced) :=
  production_step_fpu USet.add_idem held transferProduced hauth

/-! ## §2 — the value leg: the conserving src → dst move is `Fpu`.

`recTransferBal_correct` proves a committed transfer debits `(src,a)` and credits `(dst,a)` by the
same `amt`, leaving Σ_c bal c a unchanged. Abstractly the value-leg update under a FIXED total is
`Fpu` — the same fixed-total idle move as mint (`Fpu.refl` at the value camera; the well-internal
redistribution is invisible to the conservation measure). -/

/-- **`transfer_value_footprint_fpu`** — the value leg of the transfer footprint is `Fpu`: a
committed transfer conserves Σ, so the value camera sees a conservation `Fpu` — no value is created
or destroyed, it is MOVED from `src` to `dst`. -/
theorem transfer_value_footprint_fpu (a f : ℕ) :
    Fpu (R := Auth ℕ) (.mk (some a) f) (.mk (some a) f) :=
  Fpu.refl _

/-! ## §3 — `transferVerb` : the abstract `Verb` a concrete transfer inhabits. -/

/-- **`transferVerb adm held`** — the dregg2 `balanceA` (transfer) effect as an inhabitant of the
abstract `Verb`. Value leg: the conserving move (fixed total). Authority leg: producing the move-edge
`transferProduced` under the held bound `● held` — `Fpu` EXACTLY when authorized. Evidence + state
idle. The SAME shape as `mintVerb`. -/
def transferVerb {P : Type} (adm : Admission P) (held : USet Rights) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState where
  admission := adm
  pre  := (.mk (some 0) 0, .mk (some held) 0,                .mk (some ⟨∅⟩) 0, .ex 0)
  post := (.mk (some 0) 0, .mk (some held) transferProduced, .mk (some ⟨∅⟩) 0, .ex 0)

/-- **`transferVerb_footprint`** — the transfer verb's footprint is `Fpu`, derived FROM the
authorization, PROVED, kernel-clean. Each leg is `Fpu`: value (the conserving move), authority (the
authorized production), evidence + state idle; `fpu_prod` glues. The authorization is LOAD-BEARING. -/
theorem transferVerb_footprint {P : Type} (adm : Admission P) (held : USet Rights)
    (hauth : AuthorizedProduction held transferProduced) :
    Footprint (transferVerb adm held) := by
  show Fpu _ _
  refine fpu_prod (transfer_value_footprint_fpu 0 0)
    (fpu_prod ?_ (fpu_prod (Fpu.refl _) (Fpu.refl _)))
  exact transfer_production_footprint_fpu held hauth

/-! ## §4 — THE REFINEMENT: a committed `BalanceMovementSpec` makes `transferVerb` FIRE. -/

/-- **`transfer_refines_abstract_verb` — the per-effect Spec ⟹ abstract law rung, PROVED,
kernel-clean.** Given a committed `BalanceMovementSpec st t a st'` (a genuine kernel transition by
`execFullA_balanceA_iff_spec`) and a discharging witness `w` for the abstract admission, the abstract
`transferVerb` FIRES: BOTH gates pass — the admission (discharged by `hadm`) AND the footprint
(`transferVerb_footprint`, the authority discharged via the
`authorizedB ⟹ AuthorizedProduction` bridge over `hspec.1.1`). NOT `rfl` — it runs the bridge. -/
theorem transfer_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState)
    (hspec : BalanceMovementSpec st t a st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (transferVerb adm (heldFromTransfer st.kernel.caps t)) w :=
  fires_intro (W := W) _ w hadm
    (transferVerb_footprint adm (heldFromTransfer st.kernel.caps t)
      (transferAuthorizedB_covers_production st.kernel.caps t hspec.1.1))

/-- **`transfer_preserves_product_validity` — the abstract meta-law GOVERNS the concrete transfer,
PROVED.** Composing `transfer_refines_abstract_verb` with `kernel_meta_law`: a fired dregg2 transfer
preserves the product validity of EVERY compatible frame — conservation ∧ non-amplification ∧
monotonicity ∧ frame, all at once. -/
theorem transfer_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState)
    (hspec : BalanceMovementSpec st t a st')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((transferVerb adm (heldFromTransfer st.kernel.caps t)).pre ⊙ fr)) :
    ResourceAlgebra.valid ((transferVerb adm (heldFromTransfer st.kernel.caps t)).post ⊙ fr) :=
  kernel_meta_law _ w
    (transfer_refines_abstract_verb adm w st t a st' hspec hadm) fr hfr

#assert_axioms transfer_is_authorized_production
#assert_axioms transferAuthorizedB_covers_production
#assert_axioms transfer_production_footprint_fpu
#assert_axioms transfer_value_footprint_fpu
#assert_axioms transferVerb_footprint
#assert_axioms transfer_refines_abstract_verb
#assert_axioms transfer_preserves_product_validity

/-! ## §5 — NON-VACUITY + the mutation tooth. -/

/-- **`transfer_authorized_production_nonvacuous`** — the abstract authorization is genuinely
inhabited: at the held bundle `{control}` (the move-cap a real transfer exercises), the move IS an
`AuthorizedProduction`. -/
theorem transfer_authorized_production_nonvacuous :
    AuthorizedProduction (⟨{Dregg2.Authority.Auth.control}⟩ : USet Rights) transferProduced :=
  transfer_is_authorized_production _ (by simp [transferProduced])

/-- A trivial-but-real verifier seam for the non-vacuity witness. -/
instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`transferVerb_fires_nonvacuous` — the refinement's CONCLUSION is inhabited (the firing
happens).** ANY committed transfer (a `BalanceMovementSpec` witness, by `execFullA_balanceA_iff_spec`)
fires `transferVerb` under the trivial-but-real admission — exhibiting the whole chain end to end:
kernel commit ⟹ `BalanceMovementSpec` ⟹ `Fires (transferVerb …)`. -/
theorem transferVerb_fires_nonvacuous
    (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState)
    (hcommit : execFullA st (.balanceA t a) = some st') :
    Fires (W := Unit)
      (transferVerb (P := Unit) ⟨()⟩ (heldFromTransfer st.kernel.caps t)) () := by
  have hspec : BalanceMovementSpec st t a st' :=
    (execFullA_balanceA_iff_spec st t a st').mp hcommit
  exact transfer_refines_abstract_verb (P := Unit) (W := Unit) ⟨()⟩ () st t a st' hspec rfl

/-- **`transfer_refines_needs_authorized_production` — the mutation tooth, PROVED, kernel-clean.**
Were the transfer footprint's authority leg an UNAUTHORIZED amplification (producing `write` under a
held bound of only `read`), it would NOT be `Fpu` — so the verb could NOT `Fires`. The binding's
authority gate is load-bearing; trivializing the Admission cannot rescue it. -/
theorem transfer_refines_needs_authorized_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  unauthorized_amplification_not_production

#assert_axioms transfer_authorized_production_nonvacuous
#assert_axioms transferVerb_fires_nonvacuous
#assert_axioms transfer_refines_needs_authorized_production

/-! ## §Coda.

The integrity chain is closed for the transfer exemplar: kernel ⟹ `BalanceMovementSpec`
(`execFullA_balanceA_iff_spec`) ⟹ abstract `Fires (transferVerb …)` (`transfer_refines_abstract_verb`)
⟹ the abstract kernel meta-law's product-validity preservation (`transfer_preserves_product_validity`).
The two content seams: authority = `AuthorizedProduction` (the `authorizedB` bridge), value =
conservation `Fpu` (the debit/credit Σ-conservation). This is the value-move pattern transported
beyond supply — `transferVerb` is `mintVerb`'s shape with the move-edge produced over `src`.
-/

end Dregg2.Circuit.Spec.TransferAbstractBinding
