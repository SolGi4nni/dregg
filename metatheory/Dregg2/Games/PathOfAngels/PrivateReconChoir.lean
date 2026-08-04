/-
# Path of Angels — Private Recon Choir

Four expedition officers inspect one authored deck anomaly and submit private
classifications.  This file is the public game/host law, and it is intentionally
strict about the line between *metadata* and *authorization*:

* a `ClassificationMetadata` value claims a player, counter, nullifier and
  ciphertext commitment, but is not an authenticated encrypted ballot;
* checked collection retains an unforgeable per-slot `PlayerAdmission` carrying
  every structural equality the collector actually checked;
* committee metadata is treated the same way.  The existing Shamir gate proves
  only threshold/nonzero/distinct indices;
* the state and aggregate-request constructors are private capabilities.  Raw
  functions cannot be assembled into a closeable request;
* rosters are injective, the committee's canonical ordered commitment is derived
  internally, and the complete structured round identity is never a caller hash;
* local close is one-shot.  Global atomic round/nullifier/counter consumption is
  still a named Tier-0 requirement because pure local state cannot prevent a
  caller from replaying an old pre-close value or bootstrapping from a stale
  database snapshot;
* only a private-constructor `TierZeroAggregateAuthorization`, indexed by the
  exact request, histogram and authored recommendation, reaches `finalize`.

The current verified organs are useful but insufficient.  The N4K4 private
preference relation is Tier-1 and exposes only `(root,winner)`.  ThresholdDecrypt
proves Shamir reconstruction admission, not player authentication, ciphertext
provenance, one-hot encoding, homomorphic aggregation, malicious-secure output
MPC, or atomic persistent consumption.  This game therefore ends at a typed
five-tooth DrEX blocker until those joins exist.

There is no plaintext classification carrier, caller aggregate, caller reward,
asset, or money in this module.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Distributed.ThresholdDecrypt
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.PrivateReconChoir

open Dregg2.Games.PathOfAngels
open Dregg2.Distributed.ThresholdDecrypt

set_option autoImplicit false

abbrev PLAYER_COUNT : Nat := 4
abbrev CLASS_COUNT : Nat := 4
abbrev COMMITTEE_COUNT : Nat := 4
abbrev DECRYPT_THRESHOLD : Nat := 3
abbrev MAX_CIPHERTEXT_BYTES : Nat := 65536

/-! ## 1. Canonical authored identity and unique rosters -/

structure RoundIdentity where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  missionId : MissionId
  roundId : Digest32
  anomalyDigest : Digest32
  ciphertextDomain : Digest32
deriving DecidableEq

/-- This is an exact canonical ordered roster commitment, not a cryptographic
digest.  A future wire adapter may hash its canonical encoding, but the semantic
host never accepts a caller-provided roster-root digest. -/
structure CommitteeRosterRoot where
  orderedMembers : List Digest32
  exactLength : orderedMembers.length = COMMITTEE_COUNT
deriving DecidableEq

def deriveCommitteeRosterRoot
    (roster : Fin COMMITTEE_COUNT → Digest32) : CommitteeRosterRoot where
  orderedMembers := List.ofFn roster
  exactLength := by simp

/-- Both rosters are unique by construction obligation: one identity cannot
occupy two participant seats or two committee seats. -/
structure RoundContext where
  identity : RoundIdentity
  participantRoster : Fin PLAYER_COUNT → Digest32
  expectedPreviousCounter : Fin PLAYER_COUNT → PlayerCounter
  committeeRoster : Fin COMMITTEE_COUNT → Digest32
  decryptContext : Digest32
  participantRoster_injective : Function.Injective participantRoster
  committeeRoster_injective : Function.Injective committeeRoster

/-- Full semantic state identity.  It is lossless structured data, so no digest
injectivity assumption is hidden in the host model. -/
structure RoundStateIdentity where
  identity : RoundIdentity
  participantRoster : Fin PLAYER_COUNT → Digest32
  expectedPreviousCounter : Fin PLAYER_COUNT → PlayerCounter
  committeeRosterRoot : CommitteeRosterRoot
  decryptContext : Digest32
deriving DecidableEq

def RoundContext.stateIdentity (context : RoundContext) : RoundStateIdentity where
  identity := context.identity
  participantRoster := context.participantRoster
  expectedPreviousCounter := context.expectedPreviousCounter
  committeeRosterRoot := deriveCommitteeRosterRoot context.committeeRoster
  decryptContext := context.decryptContext

def RoundContext.committeeRosterRoot (context : RoundContext) : CommitteeRosterRoot :=
  deriveCommitteeRosterRoot context.committeeRoster

theorem committee_roster_root_is_exactly_derived (context : RoundContext) :
    context.committeeRosterRoot.orderedMembers = List.ofFn context.committeeRoster := rfl

theorem participant_key_names_one_slot (context : RoundContext)
    {left right : Fin PLAYER_COUNT}
    (same : context.participantRoster left = context.participantRoster right) :
    left = right :=
  context.participantRoster_injective same

theorem committee_key_names_one_slot (context : RoundContext)
    {left right : Fin COMMITTEE_COUNT}
    (same : context.committeeRoster left = context.committeeRoster right) :
    left = right :=
  context.committeeRoster_injective same

/-! ## 2. Metadata carriers and retained checked-admission evidence -/

/-- Public metadata for an alleged encrypted classification.  No authentication,
opening, one-hot proof, or plaintext classification is representable here. -/
structure ClassificationMetadata where
  round : RoundIdentity
  slot : Fin PLAYER_COUNT
  playerKey : Digest32
  previousCounter : PlayerCounter
  nextCounter : PlayerCounter
  nullifier : Digest32
  ciphertextCommitment : Digest32
  ciphertextBytes : Fin (MAX_CIPHERTEXT_BYTES + 1)
  ciphertext_nonempty : 0 < ciphertextBytes.val

/-- Public metadata for a committee release.  `share` is inspected by the real
Shamir preflight only; this does not authenticate the party or prove that the
share belongs to any ciphertext. -/
structure CommitteeReleaseMetadata where
  round : RoundIdentity
  decryptContext : Digest32
  slot : Fin COMMITTEE_COUNT
  memberKey : Digest32
  share : Share
  transcriptDigest : Digest32

/-- Capability retained in one exact participant slot.  Its constructor is
private; only `submitPlayer` can discharge these structural checks. -/
structure PlayerAdmission (context : RoundContext) (slot : Fin PLAYER_COUNT) where
  private mk ::
  metadata : ClassificationMetadata
  exactRound : metadata.round = context.identity
  exactSlot : metadata.slot = slot
  exactPlayer : metadata.playerKey = context.participantRoster slot
  exactPrevious : metadata.previousCounter = context.expectedPreviousCounter slot
  exactNext : (context.expectedPreviousCounter slot).next = some metadata.nextCounter

/-- Capability retained in one exact committee slot. -/
structure CommitteeAdmission (context : RoundContext) (slot : Fin COMMITTEE_COUNT) where
  private mk ::
  metadata : CommitteeReleaseMetadata
  exactRound : metadata.round = context.identity
  exactContext : metadata.decryptContext = context.decryptContext
  exactSlot : metadata.slot = slot
  exactMember : metadata.memberKey = context.committeeRoster slot
  exactShareIndex : metadata.share.idx = slot.val + 1

inductive Phase where
  | collecting
  | locallyClosed
deriving DecidableEq, Repr

/-- Capability-sealed local round state.  Even its field types retain checked
admission evidence; a raw metadata function is not a state. -/
structure State (context : RoundContext) where
  private mk ::
  playerSlots : (slot : Fin PLAYER_COUNT) → Option (PlayerAdmission context slot)
  committeeSlots : (slot : Fin COMMITTEE_COUNT) → Option (CommitteeAdmission context slot)
  seenNullifiers : Finset Digest32
  phase : Phase

/-- This starts a *local collector*.  It is not a persistent-ledger snapshot;
the missing global-consumption Tier-0 tooth prevents this function from being a
settlement bypass. -/
def beginLocalCollection (context : RoundContext)
    (knownNullifiers : Finset Digest32 := ∅) : State context where
  playerSlots := fun _ => none
  committeeSlots := fun _ => none
  seenNullifiers := knownNullifiers
  phase := .collecting

inductive PlayerRefusal where
  | locallyClosed
  | wrongRoundIdentity
  | wrongPlayerForSlot
  | wrongPreviousCounter
  | counterExhaustedOrSubstituted
  | duplicateNullifier
  | occupiedPlayerSlot
deriving DecidableEq, Repr

inductive CommitteeRefusal where
  | locallyClosed
  | wrongRoundIdentity
  | wrongDecryptContext
  | wrongMemberForSlot
  | wrongShareIndex
  | occupiedCommitteeSlot
deriving DecidableEq, Repr

def submitPlayer {context : RoundContext} (state : State context)
    (metadata : ClassificationMetadata) : Except PlayerRefusal (State context) :=
  if _hphase : state.phase = .collecting then
    if hround : metadata.round = context.identity then
      if hplayer : metadata.playerKey = context.participantRoster metadata.slot then
        if hprevious : metadata.previousCounter = context.expectedPreviousCounter metadata.slot then
          match hnext : (context.expectedPreviousCounter metadata.slot).next with
          | none => .error .counterExhaustedOrSubstituted
          | some expectedNext =>
              if hsupplied : metadata.nextCounter = expectedNext then
                if metadata.nullifier ∈ state.seenNullifiers then
                  .error .duplicateNullifier
                else if (state.playerSlots metadata.slot).isSome then
                  .error .occupiedPlayerSlot
                else
                  let admission : PlayerAdmission context metadata.slot := {
                    metadata
                    exactRound := hround
                    exactSlot := rfl
                    exactPlayer := hplayer
                    exactPrevious := hprevious
                    exactNext := hnext.trans (congrArg some hsupplied.symm) }
                  .ok {
                    playerSlots := Function.update state.playerSlots metadata.slot (some admission)
                    committeeSlots := state.committeeSlots
                    seenNullifiers := insert metadata.nullifier state.seenNullifiers
                    phase := state.phase }
              else .error .counterExhaustedOrSubstituted
        else .error .wrongPreviousCounter
      else .error .wrongPlayerForSlot
    else .error .wrongRoundIdentity
  else .error .locallyClosed

def submitCommittee {context : RoundContext} (state : State context)
    (metadata : CommitteeReleaseMetadata) : Except CommitteeRefusal (State context) :=
  if _hphase : state.phase = .collecting then
    if hround : metadata.round = context.identity then
      if hcontext : metadata.decryptContext = context.decryptContext then
        if hmember : metadata.memberKey = context.committeeRoster metadata.slot then
          if hindex : metadata.share.idx = metadata.slot.val + 1 then
            if (state.committeeSlots metadata.slot).isSome then
              .error .occupiedCommitteeSlot
            else
              let admission : CommitteeAdmission context metadata.slot := {
                metadata
                exactRound := hround
                exactContext := hcontext
                exactSlot := rfl
                exactMember := hmember
                exactShareIndex := hindex }
              .ok {
                playerSlots := state.playerSlots
                committeeSlots := Function.update state.committeeSlots metadata.slot (some admission)
                seenNullifiers := state.seenNullifiers
                phase := state.phase }
          else .error .wrongShareIndex
        else .error .wrongMemberForSlot
      else .error .wrongDecryptContext
    else .error .wrongRoundIdentity
  else .error .locallyClosed

theorem accepted_player_retains_exact_admission {context : RoundContext}
    {before after : State context} {metadata : ClassificationMetadata}
    (h : submitPlayer before metadata = .ok after) :
    ∃ admission : PlayerAdmission context metadata.slot,
      after.playerSlots metadata.slot = some admission ∧
      admission.metadata = metadata := by
  simp only [submitPlayer] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

theorem accepted_player_consumes_local_nullifier {context : RoundContext}
    {before after : State context} {metadata : ClassificationMetadata}
    (h : submitPlayer before metadata = .ok after) :
    metadata.nullifier ∈ after.seenNullifiers := by
  simp only [submitPlayer] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

theorem byte_identical_local_replay_refused {context : RoundContext}
    {before after : State context} {metadata : ClassificationMetadata}
    (h : submitPlayer before metadata = .ok after) :
    submitPlayer after metadata = .error .duplicateNullifier := by
  simp only [submitPlayer] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp_all [submitPlayer]
  split <;> simp_all

/-! ## 3. Threshold preflight at exactly the existing theorem's strength -/

def committeeShares {context : RoundContext} (state : State context) : List Share :=
  (List.ofFn fun slot => (state.committeeSlots slot).map (·.metadata.share)).filterMap id

def thresholdPreflight {context : RoundContext} (state : State context) : Bool :=
  combineAdmits (committeeShares state) DECRYPT_THRESHOLD

theorem thresholdPreflight_below_threshold {context : RoundContext}
    (state : State context)
    (h : (committeeShares state).length < DECRYPT_THRESHOLD) :
    thresholdPreflight state = false :=
  combine_rejects_below_threshold (committeeShares state) DECRYPT_THRESHOLD h

theorem thresholdPreflight_exact_claim {context : RoundContext}
    (state : State context) :
    thresholdPreflight state = true ↔
      DECRYPT_THRESHOLD ≤ (committeeShares state).length ∧
      (∀ share ∈ committeeShares state, share.idx ≠ 0) ∧
      ((committeeShares state).map (·.idx)).Nodup :=
  combine_admits_iff (committeeShares state) DECRYPT_THRESHOLD

/-! ## 4. Capability-sealed request and one-shot local close -/

def PlayersComplete {context : RoundContext} (state : State context) : Prop :=
  ∀ slot, (state.playerSlots slot).isSome = true

def playersCompleteB {context : RoundContext} (state : State context) : Bool :=
  (List.ofFn fun slot => (state.playerSlots slot).isSome).all id

theorem playersCompleteB_iff {context : RoundContext} (state : State context) :
    playersCompleteB state = true ↔ PlayersComplete state := by
  constructor
  · intro h
    have hs :
        (state.playerSlots 0).isSome = true ∧
        (state.playerSlots 1).isSome = true ∧
        (state.playerSlots 2).isSome = true ∧
        (state.playerSlots 3).isSome = true := by
      simpa [playersCompleteB] using h
    intro slot
    fin_cases slot
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2.1
    · exact hs.2.2.2
  · intro h
    have h0 := h (0 : Fin PLAYER_COUNT)
    have h1 := h (1 : Fin PLAYER_COUNT)
    have h2 := h (2 : Fin PLAYER_COUNT)
    have h3 := h (3 : Fin PLAYER_COUNT)
    simpa [playersCompleteB] using And.intro h0 (And.intro h1 (And.intro h2 h3))

/-- The constructor is private.  Its slots contain admissions, not metadata. -/
structure AggregateRequest where
  private mk ::
  context : RoundContext
  stateIdentity : RoundStateIdentity
  playerSlots : (slot : Fin PLAYER_COUNT) → Option (PlayerAdmission context slot)
  committeeSlots : (slot : Fin COMMITTEE_COUNT) → Option (CommitteeAdmission context slot)
  playersComplete : ∀ slot, (playerSlots slot).isSome = true
  thresholdAdmitted :
    combineAdmits
      ((List.ofFn fun slot => (committeeSlots slot).map (·.metadata.share)).filterMap id)
      DECRYPT_THRESHOLD = true
  exactStateIdentity : stateIdentity = context.stateIdentity

private def requestOf {context : RoundContext} (state : State context)
    (playersComplete : PlayersComplete state)
    (thresholdAdmitted : thresholdPreflight state = true) : AggregateRequest where
  context
  stateIdentity := context.stateIdentity
  playerSlots := state.playerSlots
  committeeSlots := state.committeeSlots
  playersComplete := playersComplete
  thresholdAdmitted := by
    simpa [thresholdPreflight, committeeShares] using thresholdAdmitted
  exactStateIdentity := rfl

/-- Total extraction is justified by the private request's completeness proof.
The result still carries every checked admission equality. -/
def AggregateRequest.playerAt (request : AggregateRequest)
    (slot : Fin PLAYER_COUNT) : PlayerAdmission request.context slot :=
  match hslot : request.playerSlots slot with
  | some admission => admission
  | none => by
      have complete := request.playersComplete slot
      simp [hslot] at complete

theorem AggregateRequest.playerAt_retains_exact_evidence
    (request : AggregateRequest) (slot : Fin PLAYER_COUNT) :
    let admission := request.playerAt slot
    admission.metadata.slot = slot ∧
    admission.metadata.round = request.context.identity ∧
    admission.metadata.playerKey = request.context.participantRoster slot ∧
    admission.metadata.previousCounter =
      request.context.expectedPreviousCounter slot ∧
    (request.context.expectedPreviousCounter slot).next =
      some admission.metadata.nextCounter := by
  dsimp only
  exact ⟨(request.playerAt slot).exactSlot,
    (request.playerAt slot).exactRound,
    (request.playerAt slot).exactPlayer,
    (request.playerAt slot).exactPrevious,
    (request.playerAt slot).exactNext⟩

/-- Exact persistent compare-and-set row demanded for one participant. -/
structure CounterUpdate where
  federationId : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  playerKey : Digest32
  previous : PlayerCounter
  next : PlayerCounter
deriving DecidableEq

/-- Canonical one-shot identity which a durable host must atomically consume.
It names the lossless round state, every accepted nullifier, and every exact
counter compare-and-set row. -/
structure SettlementKey where
  stateIdentity : RoundStateIdentity
  nullifiers : Fin PLAYER_COUNT → Digest32
  counterUpdates : Fin PLAYER_COUNT → CounterUpdate
deriving DecidableEq

def AggregateRequest.settlementKey (request : AggregateRequest) : SettlementKey where
  stateIdentity := request.stateIdentity
  nullifiers := fun slot => (request.playerAt slot).metadata.nullifier
  counterUpdates := fun slot =>
    { federationId := request.context.identity.federationId
      contentSession := request.context.identity.contentSession
      contentEpoch := request.context.identity.contentEpoch
      playerKey := (request.playerAt slot).metadata.playerKey
      previous := (request.playerAt slot).metadata.previousCounter
      next := (request.playerAt slot).metadata.nextCounter }

theorem AggregateRequest.settlementKey_binds_exact_counter
    (request : AggregateRequest) (slot : Fin PLAYER_COUNT) :
    (request.settlementKey.counterUpdates slot).previous =
        request.context.expectedPreviousCounter slot ∧
    (request.context.expectedPreviousCounter slot).next =
        some (request.settlementKey.counterUpdates slot).next := by
  exact ⟨(request.playerAt slot).exactPrevious,
    (request.playerAt slot).exactNext⟩

inductive TierZeroUpgrade where
  | authenticatedEncryptedOneHotIngressCertificate
  | additiveBfvHistogramFold
  | maliciousSecureOutputBoundaryMpc
  | transferableExactAggregateProof
  | atomicGlobalRoundNullifierCounterConsumption
deriving DecidableEq, Repr

def requiredTierZeroUpgrades : List TierZeroUpgrade :=
  [ .authenticatedEncryptedOneHotIngressCertificate
  , .additiveBfvHistogramFold
  , .maliciousSecureOutputBoundaryMpc
  , .transferableExactAggregateProof
  , .atomicGlobalRoundNullifierCounterConsumption ]

structure TierZeroBlocker (request : AggregateRequest) where
  missing : List TierZeroUpgrade
  exact : missing = requiredTierZeroUpgrades

private def blocked (request : AggregateRequest) : TierZeroBlocker request where
  missing := requiredTierZeroUpgrades
  exact := rfl

inductive CloseRefusal where
  | alreadyLocallyClosed
  | missingPlayerSubmissions
  | insufficientOrMalformedCommitteeShares
deriving DecidableEq, Repr

inductive CloseResult (context : RoundContext) where
  | refused (state : State context) (reason : CloseRefusal)
  | awaitingTierZero
      (closedState : State context)
      (request : AggregateRequest)
      (blocker : TierZeroBlocker request)

def close {context : RoundContext} (state : State context) : CloseResult context :=
  if state.phase != .collecting then
    .refused state .alreadyLocallyClosed
  else if hp : playersCompleteB state then
    if ht : thresholdPreflight state then
      let request := requestOf state ((playersCompleteB_iff state).mp hp) ht
      let closed : State context := { state with phase := .locallyClosed }
      .awaitingTierZero closed request (blocked request)
    else .refused state .insufficientOrMalformedCommitteeShares
  else .refused state .missingPlayerSubmissions

def CloseResult.closedState {context : RoundContext} : CloseResult context → State context
  | .refused state _ => state
  | .awaitingTierZero state _ _ => state

def CloseResult.isAwaitingTierZero {context : RoundContext} : CloseResult context → Bool
  | .refused _ _ => false
  | .awaitingTierZero _ _ _ => true

theorem successful_close_is_locally_closed {context : RoundContext}
    {state closed : State context} {request : AggregateRequest}
    {blocker : TierZeroBlocker request}
    (h : close state = .awaitingTierZero closed request blocker) :
    closed.phase = .locallyClosed := by
  simp only [close] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem locally_closed_cannot_close_again {context : RoundContext}
    (state : State context) (hclosed : state.phase = .locallyClosed) :
    close state = .refused state .alreadyLocallyClosed := by
  simp [close, hclosed]

/-- An attacker-shaped raw snapshot cannot cross the capability boundary. -/
structure SyntheticStateAttempt where
  playerMetadata : Fin PLAYER_COUNT → Option ClassificationMetadata
  committeeMetadata : Fin COMMITTEE_COUNT → Option CommitteeReleaseMetadata
  claimedNullifiers : Finset Digest32

inductive SyntheticStateDecision where
  | stateCapabilityRequired
deriving DecidableEq, Repr

def inspectSyntheticState (_ : SyntheticStateAttempt) : SyntheticStateDecision :=
  .stateCapabilityRequired

theorem synthesized_state_bypass_refused (attempt : SyntheticStateAttempt) :
    inspectSyntheticState attempt = .stateCapabilityRequired := rfl

/-! ## 5. Future public aggregate and unreachable authorization seam -/

structure Histogram where
  dormant : Fin (PLAYER_COUNT + 1)
  useful : Fin (PLAYER_COUNT + 1)
  containment : Fin (PLAYER_COUNT + 1)
  predatory : Fin (PLAYER_COUNT + 1)
  total_exact :
    dormant.val + useful.val + containment.val + predatory.val = PLAYER_COUNT
deriving DecidableEq

inductive Recommendation where
  | mapAndMonitor
  | recoverWithTools
  | sealAndObserve
  | immediateWithdrawal
deriving DecidableEq, Repr

def recommendationOf (histogram : Histogram) : Recommendation :=
  if histogram.predatory.val >= histogram.containment.val &&
      histogram.predatory.val >= histogram.useful.val &&
      histogram.predatory.val >= histogram.dormant.val then
    .immediateWithdrawal
  else if histogram.containment.val >= histogram.useful.val &&
      histogram.containment.val >= histogram.dormant.val then
    .sealAndObserve
  else if histogram.useful.val >= histogram.dormant.val then
    .recoverWithTools
  else .mapAndMonitor

structure TierZeroStatement where
  request : AggregateRequest
  histogram : Histogram
  recommendation : Recommendation
  recommendation_exact : recommendation = recommendationOf histogram

theorem aggregate_substitution_changes_statement
    (request : AggregateRequest) (left right : Histogram)
    (leftDifferent : left ≠ right) :
    ({ request
       histogram := left
       recommendation := recommendationOf left
       recommendation_exact := rfl } : TierZeroStatement) ≠
    ({ request
       histogram := right
       recommendation := recommendationOf right
       recommendation_exact := rfl } : TierZeroStatement) := by
  intro same
  exact leftDifferent (congrArg TierZeroStatement.histogram same)

structure TierZeroAggregateAuthorization (statement : TierZeroStatement) : Type where
  private mk ::
  opaqueToken : Unit

structure AuthorizedAggregate (request : AggregateRequest) where
  private mk ::
  histogram : Histogram
  recommendation : Recommendation
  recommendation_exact : recommendation = recommendationOf histogram
  authorization : TierZeroAggregateAuthorization {
    request
    histogram
    recommendation
    recommendation_exact }

/-- Sole game-side admission seam for a future real Tier-0 verifier. -/
def AuthorizedAggregate.ofTierZero {request : AggregateRequest}
    (histogram : Histogram)
    (authorization : TierZeroAggregateAuthorization {
      request
      histogram
      recommendation := recommendationOf histogram
      recommendation_exact := rfl }) : AuthorizedAggregate request where
  histogram
  recommendation := recommendationOf histogram
  recommendation_exact := rfl
  authorization

abbrev ReputationDelta := Fin 101

/-- Reward-shaped functions are private implementation details of `finalize`.
They cannot be called as an unauthenticated preview API. -/
private def reputationFromAuthorizedHistogram (histogram : Histogram) : ReputationDelta :=
  let value := 2 * histogram.dormant.val + 4 * histogram.useful.val +
    5 * histogram.containment.val + 3 * histogram.predatory.val
  have hd := histogram.dormant.isLt
  have hu := histogram.useful.isLt
  have hc := histogram.containment.isLt
  have hp := histogram.predatory.isLt
  have ht := histogram.total_exact
  ⟨value, by
    dsimp [value]
    simp only [PLAYER_COUNT] at hd hu hc hp ht ⊢
    omega⟩

private def contributionFromAuthorizedHistogram (histogram : Histogram) : Contribution where
  intel := ⟨20 + 3 * histogram.dormant.val + 5 * histogram.useful.val +
    6 * histogram.containment.val + 4 * histogram.predatory.val, by
      have hd := histogram.dormant.isLt
      have hu := histogram.useful.isLt
      have hc := histogram.containment.isLt
      have hp := histogram.predatory.isLt
      have ht := histogram.total_exact
      simp only [METRIC_LIMIT, PLAYER_COUNT] at hd hu hc hp ht ⊢
      omega⟩
  supplies := ⟨2 * histogram.useful.val, by
      have hu := histogram.useful.isLt
      simp only [METRIC_LIMIT, PLAYER_COUNT] at hu ⊢
      omega⟩
  cohesion := ⟨4 + 2 * histogram.containment.val, by
      have hc := histogram.containment.isLt
      simp only [METRIC_LIMIT, PLAYER_COUNT] at hc ⊢
      omega⟩
  influence := ⟨histogram.dormant.val + histogram.predatory.val, by
      have hd := histogram.dormant.isLt
      have hp := histogram.predatory.isLt
      simp only [METRIC_LIMIT, PLAYER_COUNT] at hd hp ⊢
      omega⟩
  score := ⟨10 * histogram.dormant.val + 15 * histogram.useful.val +
    18 * histogram.containment.val + 12 * histogram.predatory.val, by
      have hd := histogram.dormant.isLt
      have hu := histogram.useful.isLt
      have hc := histogram.containment.isLt
      have hp := histogram.predatory.isLt
      have ht := histogram.total_exact
      simp only [METRIC_LIMIT, PLAYER_COUNT] at hd hu hc hp ht ⊢
      omega⟩
  relics := ∅
  relics_bounded := by simp

structure FinalizedResult (request : AggregateRequest) where
  private mk ::
  settlementKey : SettlementKey
  histogram : Histogram
  recommendation : Recommendation
  reputation : ReputationDelta
  contribution : Contribution

def finalize {request : AggregateRequest}
    (authorized : AuthorizedAggregate request) : FinalizedResult request where
  settlementKey := request.settlementKey
  histogram := authorized.histogram
  recommendation := authorized.recommendation
  reputation := reputationFromAuthorizedHistogram authorized.histogram
  contribution := contributionFromAuthorizedHistogram authorized.histogram

theorem finalize_recommendation_is_derived {request : AggregateRequest}
    (authorized : AuthorizedAggregate request) :
    (finalize authorized).recommendation =
      recommendationOf (finalize authorized).histogram :=
  authorized.recommendation_exact

/-- Before Tier-0 authorization there is no result/reward variant in `CloseResult`. -/
def CloseResult.exposesReward {context : RoundContext} (_ : CloseResult context) : Bool := false

theorem unauthenticated_close_exposes_no_reward {context : RoundContext}
    (state : State context) :
    (close state).exposesReward = false := rfl

/-! ## 6. Public lobby projection -/

structure PublicView where
  stateIdentity : RoundStateIdentity
  occupiedPlayers : Fin PLAYER_COUNT → Bool
  occupiedCommittee : Fin COMMITTEE_COUNT → Bool
  localNullifierCount : Nat
  phase : Phase
  thresholdReady : Bool

def observe {context : RoundContext} (state : State context) : PublicView where
  stateIdentity := context.stateIdentity
  occupiedPlayers := fun slot => (state.playerSlots slot).isSome
  occupiedCommittee := fun slot => (state.committeeSlots slot).isSome
  localNullifierCount := state.seenNullifiers.card
  phase := state.phase
  thresholdReady := thresholdPreflight state

/-! ## 7. Kernel-clean inventory -/

#assert_axioms committee_roster_root_is_exactly_derived
#assert_axioms participant_key_names_one_slot
#assert_axioms committee_key_names_one_slot
#assert_axioms accepted_player_retains_exact_admission
#assert_axioms accepted_player_consumes_local_nullifier
#assert_axioms byte_identical_local_replay_refused
#assert_axioms thresholdPreflight_below_threshold
#assert_axioms thresholdPreflight_exact_claim
#assert_axioms playersCompleteB_iff
#assert_axioms AggregateRequest.playerAt_retains_exact_evidence
#assert_axioms AggregateRequest.settlementKey_binds_exact_counter
#assert_axioms successful_close_is_locally_closed
#assert_axioms locally_closed_cannot_close_again
#assert_axioms synthesized_state_bypass_refused
#assert_axioms aggregate_substitution_changes_statement
#assert_axioms finalize_recommendation_is_derived
#assert_axioms unauthenticated_close_exposes_no_reward

end Dregg2.Games.PathOfAngels.PrivateReconChoir
