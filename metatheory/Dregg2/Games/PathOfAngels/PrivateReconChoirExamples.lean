/-
# Private Recon Choir — honest and hostile multiplayer workbook

All ingress fixtures below are metadata.  The honest path proves that checked
metadata admissions and the real Shamir preflight reach the explicit Tier-0
blocker; it does not claim authenticated ciphertext ingress or construct an
aggregate authorization.
-/
import Dregg2.Games.PathOfAngels.PrivateReconChoir

namespace Dregg2.Games.PathOfAngels.PrivateReconChoir.Examples

open Dregg2.Games.PathOfAngels
open Dregg2.Distributed.ThresholdDecrypt
open Dregg2.Games.PathOfAngels.PrivateReconChoir

set_option autoImplicit false

def digest (value : Nat) : Digest32 where
  bytes := List.replicate 32 ⟨value % 256, Nat.mod_lt _ (by omega)⟩
  length_eq := by simp

def roundIdentity : RoundIdentity where
  federationId := digest 1
  contentRoot := digest 2
  activationDigest := digest 3
  contentSession := digest 4
  contentEpoch := ⟨17⟩
  missionId := ⟨447⟩
  roundId := digest 5
  anomalyDigest := digest 6
  ciphertextDomain := digest 7

def previousCounter : PlayerCounter := ⟨40, by native_decide⟩
def nextCounter : PlayerCounter := ⟨41, by native_decide⟩

def participantRoster (slot : Fin PLAYER_COUNT) : Digest32 := digest (20 + slot.val)
def committeeRoster (slot : Fin COMMITTEE_COUNT) : Digest32 := digest (40 + slot.val)

theorem participantRoster_injective : Function.Injective participantRoster := by
  intro left right same
  fin_cases left <;> fin_cases right <;> simp [participantRoster, digest] at same ⊢

theorem committeeRoster_injective : Function.Injective committeeRoster := by
  intro left right same
  fin_cases left <;> fin_cases right <;> simp [committeeRoster, digest] at same ⊢

def context : RoundContext where
  identity := roundIdentity
  participantRoster
  expectedPreviousCounter := fun _ => previousCounter
  committeeRoster
  decryptContext := digest 51
  participantRoster_injective := participantRoster_injective
  committeeRoster_injective := committeeRoster_injective

def metadata (slot : Fin PLAYER_COUNT) : ClassificationMetadata where
  round := roundIdentity
  slot
  playerKey := context.participantRoster slot
  previousCounter
  nextCounter
  nullifier := digest (80 + slot.val)
  ciphertextCommitment := digest (100 + slot.val)
  ciphertextBytes := ⟨2048 + slot.val, by
    have hslot := slot.isLt
    change 2048 + slot.val < 65536 + 1
    change slot.val < 4 at hslot
    omega⟩
  ciphertext_nonempty := by
    change 0 < 2048 + slot.val
    omega

def releaseMetadata (slot : Fin COMMITTEE_COUNT) : CommitteeReleaseMetadata where
  round := roundIdentity
  decryptContext := context.decryptContext
  slot
  memberKey := context.committeeRoster slot
  share := ⟨slot.val + 1, 160 + slot.val⟩
  transcriptDigest := digest (140 + slot.val)

def advancePlayer {context : RoundContext} (state : State context)
    (submitted : ClassificationMetadata) : State context :=
  match submitPlayer state submitted with
  | .ok after => after
  | .error _ => state

def advanceCommittee {context : RoundContext} (state : State context)
    (submitted : CommitteeReleaseMetadata) : State context :=
  match submitCommittee state submitted with
  | .ok after => after
  | .error _ => state

def s0 : State context := beginLocalCollection context
def s1 : State context := advancePlayer s0 (metadata 0)
def s2 : State context := advancePlayer s1 (metadata 1)
def s3 : State context := advancePlayer s2 (metadata 2)
def playersReady : State context := advancePlayer s3 (metadata 3)

def q1 : State context := advanceCommittee playersReady (releaseMetadata 0)
def q2 : State context := advanceCommittee q1 (releaseMetadata 1)
def honestReady : State context := advanceCommittee q2 (releaseMetadata 2)

def playerAccepted {context : RoundContext} : Except PlayerRefusal (State context) → Bool
  | .ok _ => true
  | .error _ => false

def playerRefusedAs {context : RoundContext} (expected : PlayerRefusal) :
    Except PlayerRefusal (State context) → Bool
  | .ok _ => false
  | .error actual => actual == expected

def closeRefusedAs {context : RoundContext} (expected : CloseRefusal) :
    CloseResult context → Bool
  | .refused _ actual => actual == expected
  | .awaitingTierZero _ _ _ => false

theorem player_zero_metadata_is_structurally_admitted :
    playerAccepted (submitPlayer s0 (metadata 0)) = true := by native_decide

theorem all_four_checked_admissions_are_present :
    playersCompleteB playersReady = true := by native_decide

theorem honest_three_of_four_shamir_preflight :
    thresholdPreflight honestReady = true := by native_decide

theorem honest_multiplayer_reaches_typed_tier_zero_boundary :
    (close honestReady).isAwaitingTierZero = true := by native_decide

theorem honest_close_is_locally_one_shot :
    closeRefusedAs .alreadyLocallyClosed
      (close (close honestReady).closedState) = true := by native_decide

/-! ## Hostile admission and replay paths -/

theorem byte_identical_replay_is_refused_in_one_collector :
    playerRefusedAs .duplicateNullifier (submitPlayer s1 (metadata 0)) = true := by
  native_decide

def duplicateNullifier : ClassificationMetadata :=
  { metadata 1 with nullifier := (metadata 0).nullifier }

theorem duplicate_nullifier_on_another_slot_is_refused :
    playerRefusedAs .duplicateNullifier (submitPlayer s1 duplicateNullifier) = true := by
  native_decide

def wrongRound : ClassificationMetadata :=
  { metadata 0 with round := { roundIdentity with roundId := digest 199 } }

theorem wrong_round_is_refused :
    playerRefusedAs .wrongRoundIdentity (submitPlayer s0 wrongRound) = true := by
  native_decide

def substitutedCiphertext : ClassificationMetadata :=
  { metadata 0 with
    nullifier := digest 198
    ciphertextCommitment := digest 197 }

theorem changed_ciphertext_cannot_replace_occupied_slot :
    playerRefusedAs .occupiedPlayerSlot (submitPlayer s1 substitutedCiphertext) = true := by
  native_decide

theorem under_threshold_close_is_refused :
    closeRefusedAs .insufficientOrMalformedCommitteeShares (close q2) = true := by
  native_decide

/-! ## Authority-hardening hostiles -/

def repeatedParticipantRoster (_ : Fin PLAYER_COUNT) : Digest32 := digest 77

theorem repeated_identity_cannot_discharge_roster_obligation :
    ¬ Function.Injective repeatedParticipantRoster := by
  intro injective
  have impossible : (0 : Fin PLAYER_COUNT) = 1 :=
    injective (by rfl)
  have impossibleNat := congrArg Fin.val impossible
  norm_num at impossibleNat

theorem same_participant_key_cannot_occupy_two_context_slots
    {left right : Fin PLAYER_COUNT}
    (same : context.participantRoster left = context.participantRoster right) :
    left = right :=
  participant_key_names_one_slot context same

theorem committee_commitment_is_internal_and_canonical :
    context.committeeRosterRoot.orderedMembers = List.ofFn context.committeeRoster := rfl

def syntheticBypass : SyntheticStateAttempt where
  playerMetadata := fun slot => some (metadata slot)
  committeeMetadata := fun slot => some (releaseMetadata slot)
  claimedNullifiers := ∅

theorem synthesized_state_bypass_never_becomes_a_state :
    inspectSyntheticState syntheticBypass = .stateCapabilityRequired := rfl

/-- A brand-new local collector can accept old metadata because it has no durable
database authority.  This is why settlement remains blocked on the explicit
atomic-global-consumption tooth below. -/
def staleFreshCollector : State context := beginLocalCollection context

theorem fresh_state_replay_is_a_named_global_residual :
    playerAccepted (submitPlayer staleFreshCollector (metadata 0)) = true ∧
    TierZeroUpgrade.atomicGlobalRoundNullifierCounterConsumption ∈
      requiredTierZeroUpgrades := by native_decide

theorem unauthenticated_reward_construction_is_blocked :
    (close honestReady).exposesReward = false ∧
    TierZeroUpgrade.authenticatedEncryptedOneHotIngressCertificate ∈
      requiredTierZeroUpgrades := by native_decide

def histogramA : Histogram where
  dormant := 1
  useful := 1
  containment := 2
  predatory := 0
  total_exact := by decide

def histogramB : Histogram where
  dormant := 0
  useful := 1
  containment := 2
  predatory := 1
  total_exact := by decide

theorem histograms_differ : histogramA ≠ histogramB := by
  intro same
  have counts := congrArg (fun histogram => histogram.dormant.val) same
  simp [histogramA, histogramB] at counts

/-- Every request emitted by the honest close has a distinct statement index
after aggregate substitution. -/
theorem aggregate_substitution_cannot_reuse_statement_index :
    ∀ closed request blocker,
      close honestReady = .awaitingTierZero closed request blocker →
      ({ request
         histogram := histogramA
         recommendation := recommendationOf histogramA
         recommendation_exact := rfl } : TierZeroStatement) ≠
      ({ request
         histogram := histogramB
         recommendation := recommendationOf histogramB
         recommendation_exact := rfl } : TierZeroStatement) := by
  intro _ request _ _
  exact aggregate_substitution_changes_statement request histogramA histogramB histograms_differ

#assert_axioms participantRoster_injective
#assert_axioms committeeRoster_injective
#assert_compiled player_zero_metadata_is_structurally_admitted
#assert_compiled all_four_checked_admissions_are_present
#assert_compiled honest_three_of_four_shamir_preflight
#assert_compiled honest_multiplayer_reaches_typed_tier_zero_boundary
#assert_compiled honest_close_is_locally_one_shot
#assert_compiled byte_identical_replay_is_refused_in_one_collector
#assert_compiled duplicate_nullifier_on_another_slot_is_refused
#assert_compiled wrong_round_is_refused
#assert_compiled changed_ciphertext_cannot_replace_occupied_slot
#assert_compiled under_threshold_close_is_refused
#assert_axioms repeated_identity_cannot_discharge_roster_obligation
#assert_compiled same_participant_key_cannot_occupy_two_context_slots
#assert_compiled committee_commitment_is_internal_and_canonical
#assert_compiled synthesized_state_bypass_never_becomes_a_state
#assert_compiled fresh_state_replay_is_a_named_global_residual
#assert_compiled unauthenticated_reward_construction_is_blocked
#assert_axioms histograms_differ
#assert_compiled aggregate_substitution_cannot_reuse_statement_index

end Dregg2.Games.PathOfAngels.PrivateReconChoir.Examples
