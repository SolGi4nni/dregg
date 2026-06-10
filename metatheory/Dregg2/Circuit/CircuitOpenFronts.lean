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
  -- exerciseA_composite_circuit: CLOSED — `fullActionCircuitStep`'s exerciseA arm is now a REAL
  -- composite (hold-gate ∘ inner-turn CIRCUIT fold), proven ⊑ `turnSpec` by mutual structural recursion
  -- (`exerciseInnerFold_refines_turnSpec` / `fullAction_circuit_refines_spec`).
  -- createCellFromFactoryA_circuit: CLOSED — `createCellFromFactoryA_emitted_refines_spec` discharged
  -- via `createCellFromFactoryA_full_sound` + the born-empty-authority bridge.
  -- createObligationA / releaseCommittedEscrowA / refundCommittedEscrowA: CLOSED — dispatch-aliased to
  -- the escrow-create / dual-release / dual-refund circuit steps (TurnEffectRefinement), real emitted
  -- spec content (EscrowHoldingCreate / Release / Refund) bridged to their committed `fullActionStep`.
  -- (F1a/F1b) createCommittedEscrowA / bridgeFinalizeA / bridgeCancelA fronts REMOVED: the
  -- constructors are gone (the families re-landed as verified factory cells).
  , ⟨"unsealA_circuit", .w3_diamond, some "unsealA", "v2 Inst diamond"⟩
  , ⟨"createSealPairA_circuit", .w3_diamond, some "createSealPairA", "v2 Inst diamond"⟩
  , ⟨"makeSovereignA_circuit", .w3_diamond, some "makeSovereignA", "v1 Inst diamond"⟩
  , ⟨"refusalA_circuit", .w3_diamond, some "refusalA", "v1 Inst diamond"⟩
  , ⟨"receiptArchiveA_circuit", .w3_diamond, some "receiptArchiveA", "v1 Inst diamond"⟩
  -- (F2a) the queue-family fronts (allocate/enqueue/dequeue/resize/atomicTx/pipelineStep)
  -- REMOVED: the family dissolved into the verified `Dregg2/Apps/QueueFactory` et al
  -- (VerbRegistry `.factory .queue`); (F2b) the kernel constructors are now GONE too.
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
  -- Wave 4: crypto — CLOSED. `poseidon2_in_circuit` + `digest_injective_to_cr` are grounded on the
  -- single named `Poseidon2Binding.Poseidon2SpongeCR` assumption: `Poseidon2Emit.state_commit_sponge_binding`
  -- / `log_hash_sponge_binding` and `DigestPortal.{cellLeafInjective,compressNInjective,logHashInjective}_*`
  -- discharge the abstract injectivity portals from real Poseidon2 CR (no double-assumed hash).
  -- Wave 5: whole-turn — ALL THREE CLOSED:
  --   * turn_circuit_composition: `TurnCircuitCompose.turnCircuitOfEmitted` folds per-step emitted AIRs;
  --     `turn_emitted_refines_exec_direct` is now the COMPLETE stack (executor commit + authentic root +
  --     bound macaroon chain `macaroonChainBinds` + aligned wires `multiStepGlueAligned`).
  --   * turn_macaroon_caveats: `macaroonChainBinds` binds `authChain` to the caveat fold (TOOTH:
  --     `macaroon_chain_teeth` rejects a forged auth digest). No longer a free column.
  --   * rust_proof_required_at_commit: `TurnAdmission.rust_proof_admits_commit` is a real proof —
  --     the per-step STARK refinement + emitted chain ⇒ `execFullTurnA` commits (no silent admission).
  -- Wave 6: inter-vat — TWO CLOSED:
  --   * coordinated_covenant_in_poly: the `vCovenantGuard` polynomial column IS the φ guard;
  --     `CoordinatedTurnEmit.covenantGuard_of_emitted` EXTRACTS `φ = true` from any satisfying witness
  --     (TOOTH: `covenantGuard_emitted_teeth` — a `φ = false` step has NO satisfying witness).
  --   * record_kernel_state_lift: `CoordinatedTurnEmit.coordinated_emitted_refines_execCoordinatedForestG`
  --     lifts emitted satisfaction to `execCoordinatedForestG` (the `RecordKernelState` step).
  , ⟨"privacy_voting_token", .w6_inter_vat, none, "pv_token_good_commits regression"⟩
  -- Wave 7: exercise — `exercise_inner_turn_witness` CLOSED: the inner emitted chain refines `turnSpec`
  -- (`ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec` via `TurnEmit.turn_emitted_refines_turnSpec`).
  -- `exercise_r4_facet_mask` REMAINS: handler `facetedOf Auth.control` masking vs bare
  -- `execFullA` inner path is a genuine executor-semantics alignment obligation (needs a facet-bridge
  -- lemma), NOT a circuit soundness hole.
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
    * W4 arithmetized Poseidon2 sponge / digest CR → CLOSED (`poseidon2_in_circuit`, `digest_injective_to_cr`)
    * W5 whole-turn = folded per-step emitted descriptors → CLOSED (`TurnCircuitCompose.turn_emitted_refines_exec_direct`)
    * W6 coordinated covenant φ in the polynomial system → CLOSED (`CoordinatedTurnEmit.covenantGuard_of_emitted`)
    * W7 exercise inner turn arithmetized → CLOSED (`TurnWitness.inner_turn_witness_refines_spec`) -/

#guard countOpenFronts == openFronts.length

end Dregg2.Circuit.CircuitOpenFronts