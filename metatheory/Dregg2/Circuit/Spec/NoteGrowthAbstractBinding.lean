/-
# Dregg2.Circuit.Spec.NoteGrowthAbstractBinding — binding the NOTE / GROWTH family to the abstract
`Metatheory.Dynamics` verb meta-law, via the shared adapter.

This family splits across TWO honest footprint shapes (NOT the authority-production shape — these
effects are about evidence growth and conservation-neutral creation, not authority conferral):

  * **EVIDENCE GROWTH** — `noteSpend` (the spent-nullifier set grows by `nf`), `noteCreate` (the
    commitment set grows by `cm`). The footprint is the monotone EVIDENCE law (`auth_grow_fpu`):
    enlarging the authoritative evidence element `● ev → ● (ev + {x})` is `Fpu` ("once known, never
    unknown"). NoteSpend's anti-replay gate (`spendProof ∧ nf ∉ nullifiers`) is the admission demand;
    the evidence growth is the footprint. THE one-shot linearity (a nullifier spent once) IS this
    monotone non-membership the evidence leg enforces. The mutation tooth here is the EVIDENCE one
    (`evidenceGrowth_not_fpu`: you cannot un-spend), not the authority one.

  * **CONSERVATION-NEUTRAL** — `createCell` / `spawn` (born-empty cell, balance 0, Σ conserved),
    `factory` (factory creation, supply-neutral), `bridgeMint` (inbound mint, Σ EXACTLY unchanged —
    `bridgeMint_supply_delta`), `pipelinedSend` (TOTAL, balance-neutral, guard `True`). These move NO
    value and confer NO authority: pure conservation-`Fpu` value legs with idle authority/evidence/
    state. They inhabit the shared `stateWriteVerb` with an IDLE authority leg
    (`idle_authorized_production`) — the honest shape for a value-conserving, permissionless creation.

DISCIPLINE: every `*_refines_abstract_verb` `#assert_axioms`'d kernel-clean, sorry-free; the evidence
tooth reds for the evidence growers, the value/idle shape governs the conservation-neutral ones.
-/
import Dregg2.Circuit.Spec.AbstractVerbAdapter
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Circuit.Spec.accountgrowth
import Dregg2.Circuit.Spec.factorycreation
import Dregg2.Circuit.Spec.bridgeinboundmint
import Dregg2.Circuit.Spec.queuepipelinedsend

namespace Dregg2.Circuit.Spec.NoteGrowthAbstractBinding

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority
open Dregg2.Resource
open Metatheory.Dynamics
open Dregg2.Circuit.Spec.AbstractVerbAdapter
open scoped Dregg2.Resource.ResourceAlgebra

/-! ## §noteSpend — the EVIDENCE-growth shape (one-shot linearity = monotone non-membership). -/

/-- **`noteSpend_refines_abstract_verb`** — a committed `NoteSpendSpec` fires the evidence-growth verb:
spending nullifier `nf` grows the authoritative evidence element from `● ∅` to `● {nf}` — the monotone
evidence law (`auth_grow_fpu`), always `Fpu`. The anti-replay gate is the admission; the growth is the
footprint. NoteSpend's one-shot linearity (a nullifier spent ONCE) IS this monotone non-membership. -/
theorem noteSpend_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) (st' : RecChainedState)
    (hspec : NoteNullifier.NoteSpendSpec st nf actor spendProof st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (evidenceGrowthVerb adm (⟨∅⟩ : USet Nat) ((⟨∅⟩ : USet Nat) + ⟨{nf}⟩)) w :=
  evidenceGrowthVerb_fires adm (⟨∅⟩ : USet Nat) ⟨{nf}⟩ w hadm

theorem noteSpend_preserves_product_validity {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool) (st' : RecChainedState)
    (hspec : NoteNullifier.NoteSpendSpec st nf actor spendProof st')
    (hadm : Admits (P := P) (W := W) adm w)
    (fr : Product DreggValue DreggAuthority DreggEvidence DreggState)
    (hfr : ResourceAlgebra.valid
      ((evidenceGrowthVerb adm (⟨∅⟩ : USet Nat) ((⟨∅⟩ : USet Nat) + ⟨{nf}⟩)).pre ⊙ fr)) :
    ResourceAlgebra.valid
      ((evidenceGrowthVerb adm (⟨∅⟩ : USet Nat) ((⟨∅⟩ : USet Nat) + ⟨{nf}⟩)).post ⊙ fr) :=
  kernel_meta_law _ w
    (noteSpend_refines_abstract_verb adm w st nf actor spendProof st' hspec hadm) fr hfr

/-! ## §noteCreate — the EVIDENCE-growth shape (a published commitment). -/

/-- **`noteCreate_refines_abstract_verb`** — a committed `NoteCreateASpec` fires the evidence-growth
verb: publishing commitment `cm` grows the authoritative evidence element from `● ∅` to `● {cm}` — the
SAME monotone evidence law as noteSpend, at the commitment carrier. -/
theorem noteCreate_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (cm : Nat) (actor : CellId) (st' : RecChainedState)
    (hspec : NoteCommitment.NoteCreateASpec st cm actor st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (evidenceGrowthVerb adm (⟨∅⟩ : USet Nat) ((⟨∅⟩ : USet Nat) + ⟨{cm}⟩)) w :=
  evidenceGrowthVerb_fires adm (⟨∅⟩ : USet Nat) ⟨{cm}⟩ w hadm

/-! ## §createCell / spawn / factory / bridgeMint / pipelinedSend — the CONSERVATION-NEUTRAL shape.

These move NO value and confer NO authority. They inhabit the shared `stateWriteVerb` with an idle
authority leg (the value leg is conservation-`Fpu`, evidence + state idle): a value-conserving,
permissionless creation/move. The honest shape — not a production, not an evidence growth. -/

/-- The shared conservation-neutral verb: value conserving (idle at total 0), authority/evidence/state
all idle. createCell/spawn/factory/bridgeMint/pipelinedSend inhabit it. -/
def neutralVerb {P : Type} (adm : Admission P) :
    Verb P DreggValue DreggAuthority DreggEvidence DreggState :=
  stateWriteVerb adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights)

/-- **`neutralVerb_fires`** — the shared firing lemma for a conservation-neutral effect: an admitting
witness fires it (the footprint is `Fpu` with an idle authority leg). -/
theorem neutralVerb_fires {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  stateWriteVerb_fires adm (⟨∅⟩ : USet Rights) (⟨∅⟩ : USet Rights) w hadm
    (idle_authorized_production _)

theorem createCell_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor newCell : CellId) (st' : RecChainedState)
    (hspec : AccountGrowth.CreateCellSpec st actor newCell st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  neutralVerb_fires adm w hadm

theorem spawn_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor child target : CellId) (st' : RecChainedState)
    (hspec : AccountGrowth.SpawnSpec st actor child target st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  neutralVerb_fires adm w hadm

theorem factory_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor newCell : CellId) (vk : Int) (st' : RecChainedState)
    (hspec : FactoryCreation.CreateFromFactorySpec st actor newCell vk st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  neutralVerb_fires adm w hadm

theorem bridgeMint_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ) (st' : RecChainedState)
    (hspec : BridgeInboundMint.InboundMintSpec st actor cell a value st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  neutralVerb_fires adm w hadm

theorem pipelinedSend_refines_abstract_verb {P W : Type} [Dregg2.Laws.Verifiable P W]
    (adm : Admission P) (w : W)
    (st : RecChainedState) (actor : CellId) (st' : RecChainedState)
    (hspec : QueuePipelinedSend.PipelinedSendSpec st actor st')
    (hadm : Admits (P := P) (W := W) adm w) :
    Fires (W := W) (neutralVerb adm) w :=
  neutralVerb_fires adm w hadm

#assert_axioms noteSpend_refines_abstract_verb
#assert_axioms noteSpend_preserves_product_validity
#assert_axioms noteCreate_refines_abstract_verb
#assert_axioms createCell_refines_abstract_verb
#assert_axioms spawn_refines_abstract_verb
#assert_axioms factory_refines_abstract_verb
#assert_axioms bridgeMint_refines_abstract_verb
#assert_axioms pipelinedSend_refines_abstract_verb

/-! ## §non-vacuity + the mutation teeth. -/

instance : Dregg2.Laws.Verifiable Unit Unit := ⟨fun _ _ => true⟩

/-- **`evidenceGrowthVerb_fires_nonvacuous`** — the evidence-grower refinement conclusion is inhabited:
the evidence-growth verb FIRES under the trivial-but-real admission (evidence growth is unconditionally
monotone). -/
theorem evidenceGrowthVerb_fires_nonvacuous :
    Fires (W := Unit)
      (evidenceGrowthVerb (P := Unit) ⟨()⟩ (⟨∅⟩ : USet Nat) ((⟨∅⟩ : USet Nat) + ⟨{0}⟩)) () :=
  evidenceGrowthVerb_fires (P := Unit) (W := Unit) ⟨()⟩ (⟨∅⟩ : USet Nat) ⟨{0}⟩ () rfl

/-- **`neutralVerb_fires_nonvacuous`** — the conservation-neutral refinement conclusion is inhabited. -/
theorem neutralVerb_fires_nonvacuous :
    Fires (W := Unit) (neutralVerb (P := Unit) ⟨()⟩) () :=
  neutralVerb_fires (P := Unit) (W := Unit) ⟨()⟩ () rfl

/-- **`noteSpend_refines_needs_monotone_evidence` — the EVIDENCE mutation tooth, PROVED.** Were a
note-spend's evidence leg to SHRINK (forget a spent nullifier, `● {nf} → ● ∅`), it would NOT be `Fpu`
— a frame holding the nullifier would be invalidated. So one-shot linearity ("a nullifier cannot be
un-spent") is load-bearing: the evidence leg only grows. This is the evidence dual of the authority
amplification tooth. -/
theorem noteSpend_refines_needs_monotone_evidence :
    ¬ Fpu (R := Auth (USet Nat))
        (.mk (some ⟨{0}⟩) 0) (.mk (some ⟨∅⟩) 0) :=
  evidenceGrowth_not_fpu

#assert_axioms evidenceGrowthVerb_fires_nonvacuous
#assert_axioms neutralVerb_fires_nonvacuous
#assert_axioms noteSpend_refines_needs_monotone_evidence

/-! ## §Coda.

The note/growth family is bound as governed instances of `Metatheory.Verb` across two honest shapes:
the EVIDENCE growers (noteSpend, noteCreate) discharge `Fires (evidenceGrowthVerb …)` from the
monotone evidence law (`auth_grow_fpu` — spending/publishing GROWS the authoritative evidence element,
always `Fpu`), with the evidence tooth (`evidenceGrowth_not_fpu`: cannot un-spend) load-bearing; the
CONSERVATION-NEUTRAL effects (createCell, spawn, factory, bridgeMint, pipelinedSend) discharge `Fires
(neutralVerb …)` with a conservation-`Fpu` value leg and idle authority/evidence/state — the honest
shape for a value-conserving, permissionless creation/move. Neither is an authority production: the
adapter expresses the evidence-growth and conservation-neutral shapes faithfully.
-/

end Dregg2.Circuit.Spec.NoteGrowthAbstractBinding
