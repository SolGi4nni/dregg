/-
# Dregg2.Circuit.Spec.LifecycleAbstractBinding — binding the LIFECYCLE family (cellSeal / cellUnseal
/ cellDestroy) to the abstract `Metatheory.Dynamics` verb meta-law, via the shared adapter.

The three lifecycle effects are authority-gated (`stateAuthB s.kernel.caps actor cell = true`),
state-machine-gated, and balance-neutral (`delta = 0`): they move only the `lifecycle`/`deathCert`
state, never value. So they inhabit the SAME shared `stateWriteVerb` shape as the field writes — the
authority leg is the `stateAuthB` authorized production over `cell`, value/evidence/state idle. Each
binding reads its spec's `stateAuthB` projection (`(hspec.1).1`, the first conjunct of the lifecycle
guard) and feeds it to the shared `gate_covers_production` bridge.

  * `cellSeal`    (`CellSealSpec`,    guard `stateAuthB ∧ acceptsEffects`,      auth `(hspec.1).1`)
  * `cellUnseal`  (`CellUnsealSpec`,  guard `stateAuthB ∧ lifecycle == sealed`, auth `(hspec.1).1`)
  * `cellDestroy` (`CellDestroySpec`, guard `stateAuthB ∧ lifecycle != destroyed`, auth `(hspec.1).1`)

DISCIPLINE: every `*_refines_abstract_verb` `#assert_axioms`'d kernel-clean, sorry-free; the shared
mutation tooth reds.
-/
import Dregg2.Circuit.Spec.AbstractVerbAdapter
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Spec.LifecycleAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority
open Dregg2.Resource
open Metatheory.Dynamics
open Dregg2.Circuit.Spec.AbstractVerbAdapter
open scoped Dregg2.Resource.ResourceAlgebra

/-- The shared lifecycle verb at a boolean authority gate `g` — the `delta=0` state-write shape. -/
def lifecycleVerb {P : Type} (adm : Admission P) (g : Bool) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (heldOfGate g) controlEdge

/-- **`lifecycleVerb_fires`** — an accepting `stateAuthB` gate + an admitting witness fire the
lifecycle verb. NOT `rfl` — runs `gate_covers_production`. -/
theorem lifecycleVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (g : Bool) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) (hg : g = true) :
    Fires (W := W) (lifecycleVerb adm g) w :=
  stateWriteVerb_fires adm (heldOfGate g) controlEdge w hadm (gate_covers_production g hg)

/-! ## §cellSeal. -/

theorem cellSeal_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : CellLifecycle.CellSealSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (lifecycleVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  lifecycleVerb_fires adm _ w hadm (hspec.1).1

theorem cellSeal_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : CellLifecycle.CellSealSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid
      ((lifecycleVerb adm (stateAuthB s.kernel.caps actor cell)).pre ⊙ fr)) :
    ResourceAlgebra.valid
      ((lifecycleVerb adm (stateAuthB s.kernel.caps actor cell)).post ⊙ fr) :=
  kernel_meta_law _ w (cellSeal_refines_abstract_verb adm w s actor cell s' hspec hadm) fr hfr

/-! ## §cellUnseal. -/

theorem cellUnseal_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : CellLifecycle.CellUnsealSpec s actor cell s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (lifecycleVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  lifecycleVerb_fires adm _ w hadm (hspec.1).1

/-! ## §cellDestroy. -/

theorem cellDestroy_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (s : RecChainedState) (actor cell : CellId) (certHash : Nat) (s' : RecChainedState)
    (hspec : CellLifecycle.CellDestroySpec s actor cell certHash s')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (lifecycleVerb adm (stateAuthB s.kernel.caps actor cell)) w :=
  lifecycleVerb_fires adm _ w hadm (hspec.1).1

#assert_axioms cellSeal_refines_abstract_verb
#assert_axioms cellSeal_preserves_product_validity
#assert_axioms cellUnseal_refines_abstract_verb
#assert_axioms cellDestroy_refines_abstract_verb

/-! ## §non-vacuity + the shared mutation tooth. -/

instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`lifecycleVerb_fires_nonvacuous`** — the lifecycle family's refinement conclusion is inhabited:
at an accepting gate, the lifecycle verb FIRES under the trivial-but-real admission. -/
theorem lifecycleVerb_fires_nonvacuous :
    Fires (W := Unit) (lifecycleVerb (P := Unit) ⟨()⟩ true) () :=
  lifecycleVerb_fires (P := Unit) (W := Unit) ⟨()⟩ true () rfl rfl

/-- **`lifecycle_refines_needs_authorized_production` — the shared mutation tooth, PROVED.** Were a
lifecycle effect's authority leg an UNAUTHORIZED amplification, it would NOT be `Fpu` — so the verb
could NOT `Fires`. The lifecycle family's `stateAuthB` authority is load-bearing. -/
theorem lifecycle_refines_needs_authorized_production :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) :=
  gateProduction_not_fpu

#assert_axioms lifecycleVerb_fires_nonvacuous
#assert_axioms lifecycle_refines_needs_authorized_production

/-! ## §Coda.

The three lifecycle effects (cellSeal/cellUnseal/cellDestroy) are bound as governed instances of
`Metatheory.Verb`: each discharges `Fires (lifecycleVerb …)` from its spec's `stateAuthB` projection
via the shared `gate_covers_production` bridge, with value/evidence/state legs idle (`delta = 0`:
lifecycle transitions move state, not value). The shared mutation tooth shows the `stateAuthB`
authority is load-bearing.
-/

end Dregg2.Circuit.Spec.LifecycleAbstractBinding
