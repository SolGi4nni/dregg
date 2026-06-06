/-
# Dregg2.Circuit.CircuitOpenFronts — explicit open-front registry (Waves 3–7).

POLICY: **no lurking holes**. Every unfinished circuit/refinement front is named here with an
explicit `sorry` theorem (or a tracked `HoleStatus`). Silent spec-fallback (`exact h` pretending
circuit = spec) is forbidden — use these portals instead.

Run `#eval countOpenHoles` after each wave to watch the frontier shrink.
-/
import Dregg2.Circuit.TurnEffectRefinement
import Dregg2.Circuit.ActionDispatch
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.CircuitOpenFronts

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.ActionDispatch (fullActionStep)
open Dregg2.Exec.TurnExecutorFull (FullActionA)

/-! ## §0 — front metadata. -/

inductive HoleWave
  | w3_diamond
  | w4_poseidon
  | w5_turn_admission
  | w6_inter_vat
  | w7_exercise_r4
  deriving Repr, DecidableEq

structure OpenFront where
  id       : String
  wave     : HoleWave
  action?  : Option String
  note     : String
  deriving Repr

/-! ## §1 — inventory (every named gap; shrink this list). -/

def openFronts : List OpenFront := [
  -- Wave 3: per-effect circuit ⊑ spec (TurnEffectRefinement dispatch)
  ⟨"emitEventA_circuit", .w3_diamond, some "emitEventA", "v1 Inst + EffectRefinement diamond"⟩
  , ⟨"incrementNonceA_circuit", .w3_diamond, some "incrementNonceA", "v1 Inst diamond"⟩
  , ⟨"setPermissionsA_circuit", .w3_diamond, some "setPermissionsA", "v1 Inst diamond"⟩
  , ⟨"setVKA_circuit", .w3_diamond, some "setVKA", "v1 Inst diamond"⟩
  , ⟨"delegateAttenA_circuit", .w3_diamond, some "delegateAttenA", "v2 Inst diamond"⟩
  , ⟨"attenuateA_circuit", .w3_diamond, some "attenuateA", "v2 Inst diamond"⟩
  , ⟨"exerciseA_composite_circuit", .w3_diamond, some "exerciseA", "hold + inner turn fold"⟩
  , ⟨"createCellFromFactoryA_circuit", .w3_diamond, some "createCellFromFactoryA", "v2 quint diamond"⟩
  , ⟨"createObligationA_circuit", .w3_diamond, some "createObligationA", "no Inst yet"⟩
  , ⟨"createCommittedEscrowA_circuit", .w3_diamond, some "createCommittedEscrowA", "v2 dual diamond"⟩
  , ⟨"releaseCommittedEscrowA_circuit", .w3_diamond, some "releaseCommittedEscrowA", "alias Inst TBD"⟩
  , ⟨"refundCommittedEscrowA_circuit", .w3_diamond, some "refundCommittedEscrowA", "alias Inst TBD"⟩
  , ⟨"bridgeFinalizeA_circuit", .w3_diamond, some "bridgeFinalizeA", "v2 Inst diamond"⟩
  , ⟨"bridgeCancelA_circuit", .w3_diamond, some "bridgeCancelA", "v2 dual diamond"⟩
  , ⟨"unsealA_circuit", .w3_diamond, some "unsealA", "v2 Inst diamond"⟩
  , ⟨"createSealPairA_circuit", .w3_diamond, some "createSealPairA", "v2 Inst diamond"⟩
  , ⟨"makeSovereignA_circuit", .w3_diamond, some "makeSovereignA", "v1 Inst diamond"⟩
  , ⟨"refusalA_circuit", .w3_diamond, some "refusalA", "v1 Inst diamond"⟩
  , ⟨"receiptArchiveA_circuit", .w3_diamond, some "receiptArchiveA", "v1 Inst diamond"⟩
  , ⟨"queueAllocateA_circuit", .w3_diamond, some "queueAllocateA", "v2 Inst diamond"⟩
  , ⟨"queueDequeueA_circuit", .w3_diamond, some "queueDequeueA", "v2 triple diamond"⟩
  , ⟨"queueResizeA_circuit", .w3_diamond, some "queueResizeA", "v2 Inst diamond"⟩
  , ⟨"queueAtomicTxA_circuit", .w3_diamond, some "queueAtomicTxA", "v2 triple diamond"⟩
  , ⟨"queuePipelineStepA_circuit", .w3_diamond, some "queuePipelineStepA", "v2 Inst diamond"⟩
  , ⟨"pipelinedSendA_circuit", .w3_diamond, some "pipelinedSendA", "v1 hold-gate diamond"⟩
  , ⟨"exportSturdyRefA_circuit", .w3_diamond, some "exportSturdyRefA", "swiss export diamond"⟩
  , ⟨"enlivenRefA_circuit", .w3_diamond, some "enlivenRefA", "v2 Inst diamond"⟩
  , ⟨"swissHandoffA_circuit", .w3_diamond, some "swissHandoffA", "v2 Inst diamond"⟩
  , ⟨"swissDropA_circuit", .w3_diamond, some "swissDropA", "v2 Inst diamond"⟩
  , ⟨"cellSealA_circuit", .w3_diamond, some "cellSealA", "v2 Inst diamond"⟩
  , ⟨"cellUnsealA_circuit", .w3_diamond, some "cellUnsealA", "v2 Inst diamond"⟩
  , ⟨"cellDestroyA_circuit", .w3_diamond, some "cellDestroyA", "v2 dual diamond"⟩
  , ⟨"refreshDelegationA_circuit", .w3_diamond, some "refreshDelegationA", "v2 Inst diamond"⟩
  -- Wave 3: emitted ⊑ spec (EffectEmittedRefinement batch-2)
  , ⟨"emitted_batch2_remaining", .w3_diamond, none, "~35 Inst effects lack *_emitted_refines_spec"⟩
  -- Wave 3: turn emit per-step (TurnEmit fallback arm)
  , ⟨"turn_emit_per_step_remaining", .w3_diamond, none, "step_emitted_refines_fullActionStep fa' fallback"⟩
  -- Wave 4: crypto
  , ⟨"poseidon2_in_circuit", .w4_poseidon, none, "replace abstract D with arithmetized Poseidon2 sponge"⟩
  , ⟨"digest_injective_to_cr", .w4_poseidon, none, "RestHashIffFrame / cellLeafInjective → Poseidon2 CR portal"⟩
  -- Wave 5: whole-turn
  , ⟨"turn_circuit_composition", .w5_turn_admission, none, "turnCircuitStep = fold per-step emitted AIRs"⟩
  , ⟨"turn_macaroon_caveats", .w5_turn_admission, none, "auth chain + hidden caveat columns"⟩
  , ⟨"rust_proof_required_at_commit", .w5_turn_admission, none, "executor admission gate"⟩
  -- Wave 6: inter-vat
  , ⟨"coordinated_covenant_in_poly", .w6_inter_vat, none, "covenant φ as polynomial guard"⟩
  , ⟨"record_kernel_state_lift", .w6_inter_vat, none, "CoordinatedForestGLift at RecordKernelState"⟩
  , ⟨"privacy_voting_token", .w6_inter_vat, none, "pv_token_good_commits regression"⟩
  -- Wave 7: exercise
  , ⟨"exercise_inner_turn_witness", .w7_exercise_r4, some "exerciseA", "arithmetize inner List FullActionA"⟩
  , ⟨"exercise_r4_facet_mask", .w7_exercise_r4, some "exerciseA", "handler facetedOf alignment"⟩
  , ⟨"handler_makeSovereign", .w7_exercise_r4, some "makeSovereignA", "field alignment lemma"⟩
  , ⟨"handler_receiptArchive", .w7_exercise_r4, some "receiptArchiveA", "field alignment lemma"⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — explicit sorry portals (Wave 3 circuit ⊑ spec holes).
    Canonical definitions live in `TurnEffectRefinement.HolePortals`; re-exported here for the registry. -/

/-! Wave-3 circuit ⊑ spec hole theorems: see `TurnEffectRefinement.HolePortals` (34 per-action + fallback). -/

/-! ## §3 — Wave 4–7 fronts: tracked declaratively in `openFronts`, no vacuous portals.

    These four fronts have NO standalone `: True := by sorry` placeholder (those were doubly-vacuous:
    a `True` statement AND a `sorry` body, asserting nothing). Each is registered as a plain
    `OpenFront` entry above instead:
    * W4 arithmetized Poseidon2 sponge / digest CR → `poseidon2_in_circuit`, `digest_injective_to_cr`
    * W5 whole-turn = folded per-step emitted descriptors → `turn_circuit_composition`
    * W6 coordinated covenant φ in the polynomial system → `coordinated_covenant_in_poly`
    * W7 exercise inner turn arithmetized → `exercise_inner_turn_witness` -/

#guard countOpenFronts == openFronts.length

end Dregg2.Circuit.CircuitOpenFronts