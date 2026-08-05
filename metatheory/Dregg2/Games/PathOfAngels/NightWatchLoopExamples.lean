/-
# NightWatchLoopExamples — public, authority-free contract examples

Closed end-to-end journeys and hostile authority-carrier mutations live beside
the private fixture in `NightWatchLoop`; this imported file deliberately cannot
mint a Policy, content-membership admission, signed-handoff admission, or
next-watch admission.  It records public finite-table and tradeoff contracts
without weakening those constructor boundaries.
-/
import Dregg2.Games.PathOfAngels.NightWatchLoopRuntime
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.NightWatchLoopExamples

open Dregg2.Games.PathOfAngels
open Dregg2.Games.PathOfAngels.NightWatchLoop

set_option autoImplicit false

def allAuthoredOutcomes : List AuthoredOutcomeId :=
  [.maintenanceReturn, .maintenanceDeep, .signalReturn,
   .signalDeep, .sealedReturn, .sealedDeep]

def allMechanicalDraftOutcomes : List MechanicalDraftOutcomeId :=
  [.maintenanceReturnInjured, .maintenanceWithdrawn,
   .signalReturnPartial, .signalCorridorLost, .sealedReturnClosed]

def allTerminals : List TerminalId :=
  allAuthoredOutcomes.map TerminalId.authored ++
    allMechanicalDraftOutcomes.map TerminalId.mechanicalDraft

def allChoices : List ChoiceId :=
  [ .markMovingClearance, .observeSecondMovement, .ignoreMovingClearance
  , .braceObservedRhythm, .overdriveTruss, .withdrawAtTruss
  , .replaySharedIntervals, .commitPrivateIntervals, .misventRelief
  , .triangulateFullSequence, .preserveRawTrace, .moveBeforeRepeat
  , .screenCorridor, .waitMovementCycle, .abandonShoal
  , .performTwoRoleHandoff, .recordClosedThreshold, .withdrawFromThreshold
  , .exchangeCalibrationBlock, .photographCradle, .leaveCavityUntouched ]

def allServingChoices : List ServingChoiceId :=
  [ .steadyBowl, .watchCup, .softReturn, .liftPacket
  , .quietBroth, .saltFold, .sharedHeel, .sealedFlask
  , .amberMash, .lampTea, .watchCrust, .returnSling
  , .filterCake, .brightPickle, .drySleeve, .sealedCrumb
  , .witnessStew, .intervalCoffee, .recoveryPair, .chalkPacket
  , .coolGrain, .trenchSalt, .wrappedFruit, .heatShieldTin
  , .homePot, .awakeSlice, .blueTray, .secondWindowKit
  , .ordinaryBowl, .scratchTonic, .offWatchPudding, .plainReturnKit ]

def allEventIds : List EventId :=
  [ .servingAllocated, .maintenancePerformed, .briefingDelivered
  , .handoffRecorded, .routeCommitted, .choiceResolved, .extractionResolved
  , .injuryRecorded, .recoveryServingRecorded, .recoveryCalibrationCompleted
  , .nextWatchEnrolled, .draftSettlementActivated, .debriefIssued ]

theorem stable_ids_are_pairwise_distinct :
    (allChoices.map ChoiceId.code).Nodup ∧
    (allServingChoices.map ServingChoiceId.code).Nodup ∧
    (allEventIds.map EventId.code).Nodup := by
  native_decide

theorem exactly_six_pack_rows_and_five_unactivated_mechanical_drafts :
    allAuthoredOutcomes.length = 6 ∧
    allMechanicalDraftOutcomes.length = 5 ∧
    (allTerminals.map TerminalId.code).Nodup := by
  native_decide

theorem authored_rows_have_exact_pack_costs :
    allAuthoredOutcomes.map AuthoredOutcomeId.operationalCost = [2, 5, 3, 7, 11, 12] := by
  decide

theorem every_terminal_validates_but_only_authored_rows_have_pack_cost_identity :
    allTerminals.all (fun terminal => (outcomeReceipt? terminal).isSome) = true ∧
    allAuthoredOutcomes.all (fun outcome =>
      (TerminalId.authored outcome).authoredOperationalCost?.isSome) = true ∧
    allMechanicalDraftOutcomes.all (fun outcome =>
      (TerminalId.mechanicalDraft outcome).authoredOperationalCost?.isNone) = true := by
  native_decide

theorem every_choice_delta_is_locally_bounded :
    allChoices.all (fun choice =>
      choice.delta.turnCost ≤ TURN_BUDGET &&
      choice.delta.operationalCost ≤ OPERATIONAL_BUDGET &&
      choice.delta.supplyCost ≤ SUPPLY_SPEND_LIMIT &&
      decide (choice.delta.artifacts ⊆ allowedArtifacts)) = true := by
  native_decide

/- The formerly dominated pairs now expose real time/information tradeoffs. -/
theorem choice_pairs_have_nontrivial_tradeoffs :
    ChoiceId.replaySharedIntervals.delta.turnCost <
      ChoiceId.commitPrivateIntervals.delta.turnCost ∧
    ChoiceId.replaySharedIntervals.delta.clueIntel <
      ChoiceId.commitPrivateIntervals.delta.clueIntel ∧
    ChoiceId.screenCorridor.delta.turnCost < ChoiceId.waitMovementCycle.delta.turnCost ∧
    ChoiceId.screenCorridor.delta.clueIntel < ChoiceId.waitMovementCycle.delta.clueIntel ∧
    ChoiceId.leaveCavityUntouched.delta.operationalCost <
      ChoiceId.photographCradle.delta.operationalCost ∧
    ChoiceId.leaveCavityUntouched.delta.clueIntel <
      ChoiceId.photographCradle.delta.clueIntel := by
  decide

theorem portable_relics_are_exact_and_witness_is_environmental :
    allowedCarriedRelics = {relicSilentBearing, relicIndexFilm, relicThresholdWedge} ∧
    relicWitnessThread ∉ allowedCarriedRelics := by
  decide

theorem maintenance_world_intent_is_not_an_expedition_terminal :
    NightWatchLoopRuntime.WorldContributionIntent.maintenance maintenanceContribution ≠
      .expedition (.authored .maintenanceReturn) maintenanceContribution
        artifactMaintenanceLoadTrace (debriefFor (.authored .maintenanceReturn)) 2 := by
  decide

#assert_compiled stable_ids_are_pairwise_distinct
#assert_compiled exactly_six_pack_rows_and_five_unactivated_mechanical_drafts
#assert_axioms authored_rows_have_exact_pack_costs
#assert_compiled every_terminal_validates_but_only_authored_rows_have_pack_cost_identity
#assert_compiled every_choice_delta_is_locally_bounded
#assert_axioms choice_pairs_have_nontrivial_tradeoffs
#assert_axioms portable_relics_are_exact_and_witness_is_environmental
#assert_axioms maintenance_world_intent_is_not_an_expedition_terminal

end Dregg2.Games.PathOfAngels.NightWatchLoopExamples
