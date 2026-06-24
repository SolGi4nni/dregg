/-
# Dregg2.Circuit.Spec.StateWriteAbstractBinding — binding the STATE-WRITE family (`delta = 0`
field writes) to the abstract `Metatheory.Dynamics` verb meta-law, via the shared adapter.

The state-write effects share ONE footprint shape: NO value move (the value leg idle), the authority
leg the gate's authorized production over `cell`, evidence + state idle. `AbstractVerbAdapter`
factors that shape; here each effect's binding is a THIN instantiation — its concrete spec yields the
authority gate fact (`stateAuthB s.kernel.caps actor cell = true`), the shared
`gate_covers_production` bridge turns it into an `AuthorizedProduction`, and `stateWriteVerb_fires`
glues it to the admission. Each `*_refines_abstract_verb` is a REAL proof (it runs the bridge over
the spec's authority projection), with the shared mutation tooth `gateProduction_not_fpu`.

Bound here:
  * `setField`         (`SetFieldSpec`,         auth `(hspec.2.1).2.1`)
  * `setVK`            (`SetVKSpec`,            auth `(hspec.1).1`)
  * `setPermissions`   (`SetPermissionsSpec`,   auth `(hspec.1).1`)
  * `setProgram`       (`SetProgramSpec`,       auth `(hspec.1).1`)
  * `incrementNonce`   (`IncrementNonceSpec`,   auth `(hspec.1).2.1`)
  * `makeSovereign`    (`MakeSovereignSpec`,    auth `(hspec.1).1`)
  * `refusal`          (`RefusalSpec`,          auth `(hspec.1).1`)
  * `receiptArchive`   (`ReceiptArchiveSpec`,   auth `(hspec.1).1`)
  * `emitEvent`        (`EmitEventSpec`,  NO authority gate — idle authority leg, `idle_authorized_production`)

The `emitEvent` IMPEDANCE (worth naming): dregg1's `apply_emit_event` runs NO authority check (anyone
may post an observation on a live cell). So its authority leg is genuinely IDLE — produced = `∅` — a
value-and-authority-idle, pure log-advance verb. It still inhabits `stateWriteVerb` (with `produced :=
∅`), and its footprint is `Fpu` by the idle-production lemma; the mutation tooth does NOT apply to it
(there is no authority to amplify). This is the honest shape: not every effect is a production; the
no-authority ones are idle legs, which the adapter expresses faithfully.

DISCIPLINE: every `*_refines_abstract_verb` `#assert_axioms`'d kernel-clean, sorry-free, the shared
tooth reds. Non-vacuity is the shared `authorized_production` witness.
-/
import Dregg2.Circuit.Spec.AbstractVerbAdapter
import Dregg2.Circuit.Spec.cellstatefield
import Dregg2.Circuit.Spec.cellstatevk
import Dregg2.Circuit.Spec.cellstatepermissions
import Dregg2.Circuit.Spec.cellstateprogram
import Dregg2.Circuit.Spec.cellstatemonotone
import Dregg2.Circuit.Spec.cellstateaudit
import Dregg2.Circuit.Spec.cellstatelog
import Dregg2.Circuit.Spec.sovereigncommitment

namespace Dregg2.Circuit.Spec.StateWriteAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority
open Dregg2.Resource
open Metatheory.Dynamics
open Dregg2.Circuit.Spec.AbstractVerbAdapter
open scoped Dregg2.Resource.ResourceAlgebra

/-! ## The shared state-write verb, gate-driven.

`stateWriteEffectVerb adm g` is the state-write verb whose authority leg PRODUCES the `control` edge
under the held bound the gate `g` grants (`{control}` on accept, `∅` on reject). Every authority-gated
field write inhabits it with `g := stateAuthB st.kernel.caps actor cell`. -/

/-- The shared state-write verb at a boolean authority gate `g`. -/
def stateWriteEffectVerb {P : Type} (adm : Admission P) (g : Bool) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (heldOfGate g) controlEdge

/-- **`stateWriteEffectVerb_fires`** — the shared firing lemma for an authority-gated state write:
an accepting gate (`g = true`) + an admitting witness make the verb FIRE. Each effect feeds its own
spec's `stateAuthB … = true` here. NOT `rfl` — it runs `gate_covers_production`. -/
theorem stateWriteEffectVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (g : Bool) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) (hg : g = true) :
    Fires (W := W) (stateWriteEffectVerb adm g) w :=
  stateWriteVerb_fires adm (heldOfGate g) controlEdge w hadm (gate_covers_production g hg)

/-! ## §setField. -/

/-- **`setField_refines_abstract_verb`** — a committed `SetFieldSpec` fires the state-write verb at
its authority gate. The authority fact is read off `(hspec.2.1).2.1` (the `stateAuthB` conjunct of
`SetFieldGuard`, inside `reservedField ∧ SetFieldGuard ∧ …`). REAL proof, runs the bridge. -/
theorem setField_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hspec : CellStateField.SetFieldSpec s actor cell f v s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W)
      (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.2.1).2.1

theorem setField_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState)
    (hspec : CellStateField.SetFieldSpec s actor cell f v s')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid
      ((stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)).pre ⊙ fr)) :
    ResourceAlgebra.valid
      ((stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)).post ⊙ fr) :=
  kernel_meta_law _ w (setField_refines_abstract_verb adm w s actor cell f v s' hspec hadm) fr hfr

/-! ## §setVK. -/

theorem setVK_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (vk : Int) (s' : RecChainedState)
    (hspec : CellStateVK.SetVKSpec s actor cell vk s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §setPermissions. -/

theorem setPermissions_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (p : Int) (s' : RecChainedState)
    (hspec : CellStatePermissions.SetPermissionsSpec s actor cell p s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §setProgram. -/

theorem setProgram_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (prog : Int) (s' : RecChainedState)
    (hspec : CellStateProgram.SetProgramSpec s actor cell prog s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §incrementNonce. -/

theorem incrementNonce_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (n : Int) (s' : RecChainedState)
    (hspec : CellStateMonotone.IncrementNonceSpec s actor cell n s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).2.1

/-! ## §makeSovereign. -/

theorem makeSovereign_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : SovereignCommitment.MakeSovereignSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §refusal. -/

theorem refusal_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : CellStateAudit.RefusalSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §receiptArchive. -/

theorem receiptArchive_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : CellStateAudit.ReceiptArchiveSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (stateWriteEffectVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  stateWriteEffectVerb_fires adm _ w hadm (hspec.1).1

/-! ## §emitEvent — THE NO-AUTHORITY IMPEDANCE (idle authority leg).

dregg1's `apply_emit_event` runs no authority check — anyone may post an observation on a live cell.
So `emitEvent`'s authority leg is genuinely IDLE: the produced edge is `∅`, an idle authority leg
covered by ANY held bundle (`idle_authorized_production`). It inhabits the shared `stateWriteVerb`
with `produced := ∅` — a value-and-authority-idle, pure log-advance verb. NOT a production: the
honest shape for a permissionless effect. -/

/-- **`emitEventVerb adm`** — the emitEvent verb: value idle, authority leg IDLE (produced `∅`),
evidence + state idle. The pure log-advance shape (no authority gate). -/
def emitEventVerb {P : Type} (adm : Admission P) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights)

/-- **`emitEvent_refines_abstract_verb`** — a committed `EmitEventSpec` fires the (idle-authority)
emitEvent verb under any admitting witness. The authority leg is the idle production (`∅`), trivially
authorized — no gate fact needed, faithfully reflecting that emitEvent demands no authority. The verb
still FIRES and is governed by the meta-law; its footprint is `Fpu` with an idle authority leg. -/
theorem emitEvent_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor cell : CellId) (topic data : Int) (st' : RecChainedState)
    (hspec : CellStateLog.EmitEventSpec st actor cell topic data st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (emitEventVerb adm) w :=
  stateWriteVerb_fires adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights) w hadm
    (idle_authorized_production _)

theorem emitEvent_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor cell : CellId) (topic data : Int) (st' : RecChainedState)
    (hspec : CellStateLog.EmitEventSpec st actor cell topic data st')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid ((emitEventVerb adm).pre ⊙ fr)) :
    ResourceAlgebra.valid ((emitEventVerb adm).post ⊙ fr) :=
  kernel_meta_law _ w
    (emitEvent_refines_abstract_verb adm w st actor cell topic data st' hspec hadm) fr hfr

#assert_axioms setField_refines_abstract_verb
#assert_axioms setField_preserves_product_validity
#assert_axioms setVK_refines_abstract_verb
#assert_axioms setPermissions_refines_abstract_verb
#assert_axioms setProgram_refines_abstract_verb
#assert_axioms incrementNonce_refines_abstract_verb
#assert_axioms makeSovereign_refines_abstract_verb
#assert_axioms refusal_refines_abstract_verb
#assert_axioms receiptArchive_refines_abstract_verb
#assert_axioms emitEvent_refines_abstract_verb
#assert_axioms emitEvent_preserves_product_validity

/-! ## §non-vacuity + the shared mutation tooth. -/

/-- A trivial-but-real verifier seam for the non-vacuity witnesses. -/
instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`stateWrite_authorized_production_nonvacuous`** — the abstract authorization is genuinely
inhabited at the `{control}` held bundle (the cap an authorized write exercises): producing the
`control` edge IS an `AuthorizedProduction`. The shared non-vacuity for the whole family. -/
theorem stateWrite_authorized_production_nonvacuous :
    AuthorizedProduction (controlEdge) controlEdge :=
  (USet.fits_iff controlEdge controlEdge).mpr (by simp)

/-- **`stateWriteVerb_fires_nonvacuous`** — the family's refinement conclusion is inhabited: at an
accepting gate, the state-write verb FIRES under the trivial-but-real admission. -/
theorem stateWriteVerb_fires_nonvacuous :
    Fires (W := Unit) (stateWriteEffectVerb (P := Unit) ⟨()⟩ true) () :=
  stateWriteEffectVerb_fires (P := Unit) (W := Unit) ⟨()⟩ true () rfl rfl

/-- **`stateWrite_refines_needs_authorized_production` — the shared mutation tooth, PROVED.** Were
any state-write binding's authority leg an UNAUTHORIZED amplification (producing `write` under a held
bound of only `read`), it would NOT be `Fpu` — so the verb could NOT `Fires`. The whole family's
authority gate is load-bearing; this is the shared adapter tooth `gateProduction_not_fpu`. -/
theorem stateWrite_refines_needs_authorized_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  gateProduction_not_fpu

#assert_axioms stateWrite_authorized_production_nonvacuous
#assert_axioms stateWriteVerb_fires_nonvacuous
#assert_axioms stateWrite_refines_needs_authorized_production

/-! ## §Coda.

Nine state-write effects bound as GOVERNED INSTANCES of `Metatheory.Verb` through the shared adapter:
the eight authority-gated writes (setField/setVK/setPermissions/setProgram/incrementNonce/
makeSovereign/refusal/receiptArchive) each discharge `Fires (stateWriteEffectVerb …)` from their
spec's `stateAuthB` projection via the `gate_covers_production` bridge; emitEvent — the no-authority
impedance — inhabits the SAME verb with an IDLE authority leg (`produced := ∅`, the honest shape for
a permissionless effect). The shared mutation tooth (`gateProduction_not_fpu`) shows the authority
gate is load-bearing for the gated eight. The value leg is idle throughout (`delta = 0`): these are
pure state writes, not value movers — the adapter's `stateWriteVerb` expresses that faithfully.
-/

end Dregg2.Circuit.Spec.StateWriteAbstractBinding
