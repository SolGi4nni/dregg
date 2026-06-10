/-
# Dregg2.Circuit.CircuitOpenFronts — explicit open-front registry (Waves 3–7).

POLICY: **no lurking holes**. Every unfinished circuit/refinement front is named here with an
explicit `sorry` theorem (or a tracked `HoleStatus`). Silent spec-fallback (`exact h` pretending
circuit = spec) is forbidden — use these portals instead.

Run `#eval countOpenFronts` after each wave to watch the frontier shrink.
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

/-! ## §1 — inventory (every named gap; shrink this list).

CLOSED fronts (verified by the closing theorem's existence; entries removed):

* **Wave 3, per-effect circuit ⊑ spec — ALL 20 Inst-diamond fronts CLOSED.** Every listed
  action (emitEventA, incrementNonceA, setPermissionsA, setVKA, delegateAttenA, attenuateA,
  unsealA, createSealPairA, makeSovereignA, refusalA, receiptArchiveA, pipelinedSendA,
  exportSturdyRefA→swissExport, enlivenRefA→enliven, swissHandoffA, swissDropA, cellSealA,
  cellUnsealA, cellDestroyA, refreshDelegationA) has a real per-effect
  `*_circuit_refines_spec` theorem (`EffectRefinementBatch2.lean`, composed through the Inst
  `*_full_sound` diamonds) and a matching `*_emitted_refines_spec`
  (`EffectEmittedRefinement.lean`). No `fullActionCircuitStep` arm routes through
  `hole_circuit_step` any more (the portal survives only as a re-export; see §0).
* exerciseA_composite_circuit: CLOSED — `fullActionCircuitStep`'s exerciseA arm is a REAL
  composite (hold-gate ∘ inner-turn CIRCUIT fold), proven ⊑ `turnSpec` by mutual structural
  recursion (`exerciseInnerFold_refines_turnSpec` / `fullAction_circuit_refines_spec`).
* createCellFromFactoryA_circuit: CLOSED — `createCellFromFactoryA_emitted_refines_spec`
  discharged via `createCellFromFactoryA_full_sound` + the born-empty-authority bridge.
* createObligationA / releaseCommittedEscrowA / refundCommittedEscrowA: CLOSED —
  dispatch-aliased to the escrow-create / dual-release / dual-refund circuit steps.
* (F1a/F1b) createCommittedEscrowA / bridgeFinalizeA / bridgeCancelA fronts REMOVED: the
  constructors are gone (the families re-landed as verified factory cells).
* (F2a/F2b) the queue-family fronts REMOVED: the family dissolved into the verified
  `Dregg2/Apps/QueueFactory` et al (VerbRegistry `.factory .queue`); kernel constructors gone.
* emitted_batch2_remaining: CLOSED — 39 distinct `*_emitted_refines_spec` theorems exist
  (every surviving Inst effect covered); zero `sorry` in `EffectEmittedRefinement.lean`.
* turn_emit_per_step_remaining: CLOSED — `TurnEmit.step_emitted_refines_fullActionStep`
  dispatches every arm to a real emitted (or circuit-dispatch) discharge; "no declarative
  fallback remains" (TurnEmit §5b).
* Wave 4 crypto: CLOSED — `poseidon2_in_circuit` + `digest_injective_to_cr` grounded on the
  single named `Poseidon2Binding.Poseidon2SpongeCR` assumption (no double-assumed hash).
* Wave 5 whole-turn: ALL THREE CLOSED — `TurnCircuitCompose.turn_emitted_refines_exec_direct`
  (complete stack), `macaroonChainBinds` (+ `macaroon_chain_teeth`), and
  `TurnAdmission.rust_proof_admits_commit`.
* Wave 6 inter-vat: BOTH CLOSED — `CoordinatedTurnEmit.covenantGuard_of_emitted`
  (+ `covenantGuard_emitted_teeth`) and
  `CoordinatedTurnEmit.coordinated_emitted_refines_execCoordinatedForestG`.
* privacy_voting_token: CLOSED — `pv_token_good_commits` PROVED + `#assert_axioms`-pinned
  (`Apps/PrivacyVotingGated.lean`).
* Wave 7 exercise: `exercise_inner_turn_witness` CLOSED
  (`ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec`); `exercise_r4_facet_mask`
  CLOSED (P2 canonical-semantics: `execFullA` enforces the R4 facet mask via
  `innerFacetsAdmittedA`; `ExerciseInnerTurn.exercise_r4_facet_mask`); `handler_makeSovereign`
  / `handler_receiptArchive` CLOSED (handler aligned; genuine proofs in `HandlerExecutor`).
  See `Dregg2/Exec/HandlerOpenFronts.lean` — the handler lane's surviving front
  (`spawn_factory_metadata`) is tracked THERE, not here.

What genuinely remains in the circuit lane: -/

def openFronts : List OpenFront := [
  -- §5c TurnEmit: the adversarial-witness EXTRACTOR (no dead whole-trace `hEnc`) is generic
  -- (`WitnessExtract.effect2_extract*`) but instantiated per-effect only for mint
  -- (`mintA_extract` / `mintA_extract_emitted` / `mintA_extract_rejects_wrong_supply`, the
  -- validated reference). Lifting the PI-bound extraction to every v2 effect arm is open.
  ⟨"per_effect_adversarial_extractors", .w5_turn_admission, none,
    "WitnessExtract effect2_extract instantiated for mintA only; lift to all v2 effects"⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — sorry portals: NONE remain.
    `TurnEffectRefinement.HolePortals` now contains only the generic
    `hole_fullAction_circuit_refines_spec_fallback` (a REAL proof kept for the
    `hole_circuit_step` re-export); the 34 per-action `sorry` hole theorems are gone —
    every dispatch arm has a genuine per-effect refinement (see the CLOSED ledger in §1). -/

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