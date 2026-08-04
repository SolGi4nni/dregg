/-
# CrewExpeditionAuthority — specialist preparation and exact crew mandates

This module is an isolated, executable authority mechanic for Khovokhi away
missions.  Four specialists can prepare a site alone, and can undo that work
alone: the sensor officer sweeps sectors, the engineer braces barriers, the
containment officer damps hazards, and the salvage officer stages cargo.

The irreversible verbs are a different kind of move.  Hazardous breach,
quarantine, extraction, and abort require a threshold certificate whose signed
body contains the exact mission, federation, expedition, complete roster,
roster digest, operation, sequence, and semantic pre-state snapshot.  Distinct
roster members are counted once; action-specific specialist participation is
required in addition to the numeric threshold.  Every accepted action advances
the sequence, so an old certificate is unspendable even if its operation would
otherwise still make sense.

`Config.verifyApproval` is the cryptographic boundary.  It is passed the exact
credential, exact body, and opaque signature.  This file does not replace a
signature scheme with Lean arithmetic.  The executable fixture at the end uses
a deliberately non-cryptographic test verifier; the game authorization and
state-transition semantics are the object defined here.

Nothing in this module promotes canon or mints a market asset.  Extraction emits
only the bounded `ActivityOutcome.Checked` already admitted by the mission.
-/
import Dregg2.Games.PathOfAngels.ActivityOutcome
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.CrewExpeditionAuthority

open Dregg2.Games.PathOfAngels

set_option autoImplicit false

abbrev CREW_SIZE : Nat := 4
abbrev MAX_SECTORS : Nat := 32
abbrev MAX_BARRIERS : Nat := 32
abbrev MAX_HAZARDS : Nat := 32
abbrev MAX_SALVAGE : Nat := 32
abbrev MAX_STEPS : Nat := 128
abbrev MAX_SUPPLIES : Nat := 256

structure OfficerId where
  value : Nat
deriving Repr, DecidableEq

structure CredentialId where
  value : Nat
deriving Repr, DecidableEq

structure SectorId where
  value : Nat
deriving Repr, DecidableEq

structure BarrierId where
  value : Nat
deriving Repr, DecidableEq

structure HazardId where
  value : Nat
deriving Repr, DecidableEq

structure SalvageId where
  value : Nat
deriving Repr, DecidableEq

inductive SpecialistRole where
  | sensor
  | engineer
  | containment
  | salvage
deriving Repr, DecidableEq

structure Seat where
  officer : OfficerId
  role : SpecialistRole
  credential : CredentialId
deriving Repr, DecidableEq

structure BarrierSpec where
  id : BarrierId
  sector : SectorId
  hazard : HazardId
  breachSupplyCost : Nat
deriving Repr, DecidableEq

structure HazardSpec where
  id : HazardId
  sector : SectorId
deriving Repr, DecidableEq

structure SalvageSpec where
  id : SalvageId
  sector : SectorId
  relic : RelicId
  behind : Option BarrierId
deriving Repr, DecidableEq

inductive CargoCustody where
  | onDeck (sector : SectorId)
  | staged (officer : OfficerId)
  | secured
deriving Repr, DecidableEq

structure CargoRecord where
  id : SalvageId
  custody : CargoCustody
deriving Repr, DecidableEq

inductive MissionPhase where
  | field
  | extracted
  | aborted
deriving Repr, DecidableEq

/-- The whole semantic state.  The sequence is changed only by `step`; individual
transition arms cannot select their own sequence. -/
structure State where
  phase : MissionPhase
  sequence : Nat
  supplies : Nat
  swept : Finset SectorId
  braced : Finset BarrierId
  damped : Finset HazardId
  breached : Finset BarrierId
  quarantined : Finset HazardId
  cargo : List CargoRecord
deriving DecidableEq

/-- The exact state view signed by a crew mandate.  This is intentionally not a
home-grown hash.  A wire layer may commit to its canonical encoding, but the Lean
authority relation compares the full semantic object. -/
structure StateSnapshot where
  phase : MissionPhase
  sequence : Nat
  supplies : Nat
  swept : Finset SectorId
  braced : Finset BarrierId
  damped : Finset HazardId
  breached : Finset BarrierId
  quarantined : Finset HazardId
  cargo : List CargoRecord
deriving DecidableEq

def snapshot (state : State) : StateSnapshot where
  phase := state.phase
  sequence := state.sequence
  supplies := state.supplies
  swept := state.swept
  braced := state.braced
  damped := state.damped
  breached := state.breached
  quarantined := state.quarantined
  cargo := state.cargo

inductive IrreversibleOp where
  | hazardousBreach (barrier : BarrierId)
  | quarantine (hazard : HazardId)
  | extract
  | abort
deriving Repr, DecidableEq

/-- Exact message authenticated by every approval.  Carrying the complete roster
prevents a signature collected for one seating from being interpreted under a
different role assignment even if an external digest registry is stale. -/
structure MandateBody where
  federationId : Digest32
  missionId : MissionId
  missionArtifact : ArtifactRef
  contentRoot : Digest32
  expeditionId : Digest32
  rosterDigest : Digest32
  roster : List Seat
  sequence : Nat
  preState : StateSnapshot
  operation : IrreversibleOp
deriving DecidableEq

/-- Opaque to the game semantics.  Production callers supply a verifier whose
signature object is decoded into this bounded carrier. -/
structure ApprovalSignature where
  value : Nat
deriving Repr, DecidableEq

structure Approval where
  signer : OfficerId
  body : MandateBody
  signature : ApprovalSignature
deriving DecidableEq

structure ThresholdPolicy where
  hazardousBreach : Nat
  quarantine : Nat
  extract : Nat
  abort : Nat
deriving Repr, DecidableEq

structure RawConfig where
  expeditionId : Digest32
  rosterDigest : Digest32
  roster : List Seat
  sectors : List SectorId
  barriers : List BarrierSpec
  hazards : List HazardSpec
  salvage : List SalvageSpec
  thresholds : ThresholdPolicy
  operationalSupplyBudget : Nat
  stepBudget : Nat
  policy : ActivityOutcome.Policy
  fieldArtifact : ArtifactRef

def officerIds (raw : RawConfig) : List OfficerId := raw.roster.map Seat.officer
def credentialIds (raw : RawConfig) : List CredentialId := raw.roster.map Seat.credential
def roles (raw : RawConfig) : List SpecialistRole := raw.roster.map Seat.role
def barrierIds (raw : RawConfig) : List BarrierId := raw.barriers.map BarrierSpec.id
def hazardIds (raw : RawConfig) : List HazardId := raw.hazards.map HazardSpec.id
def salvageIds (raw : RawConfig) : List SalvageId := raw.salvage.map SalvageSpec.id
def salvageRelics (raw : RawConfig) : List RelicId := raw.salvage.map SalvageSpec.relic

def barrierById? : List BarrierSpec → BarrierId → Option BarrierSpec
  | [], _ => none
  | barrier :: barriers, id =>
      if barrier.id = id then some barrier else barrierById? barriers id

def hazardById? : List HazardSpec → HazardId → Option HazardSpec
  | [], _ => none
  | hazard :: hazards, id =>
      if hazard.id = id then some hazard else hazardById? hazards id

def salvageById? : List SalvageSpec → SalvageId → Option SalvageSpec
  | [], _ => none
  | item :: items, id =>
      if item.id = id then some item else salvageById? items id

def seatByOfficer? : List Seat → OfficerId → Option Seat
  | [], _ => none
  | seat :: seats, id =>
      if seat.officer = id then some seat else seatByOfficer? seats id

def cargoById? : List CargoRecord → SalvageId → Option CargoRecord
  | [], _ => none
  | item :: items, id =>
      if item.id = id then some item else cargoById? items id

def thresholdsValidB (thresholds : ThresholdPolicy) : Bool :=
  decide (0 < thresholds.hazardousBreach ∧ thresholds.hazardousBreach ≤ CREW_SIZE) &&
  decide (0 < thresholds.quarantine ∧ thresholds.quarantine ≤ CREW_SIZE) &&
  decide (0 < thresholds.extract ∧ thresholds.extract ≤ CREW_SIZE) &&
  decide (0 < thresholds.abort ∧ thresholds.abort ≤ CREW_SIZE)

/-- Content validation for all game-authoritative finite tables. -/
def configValidB (raw : RawConfig) : Bool :=
  decide (raw.roster.length = CREW_SIZE) &&
  decide (officerIds raw).Nodup &&
  decide (credentialIds raw).Nodup &&
  decide (roles raw).Nodup &&
  decide (0 < raw.sectors.length ∧ raw.sectors.length ≤ MAX_SECTORS) &&
  decide raw.sectors.Nodup &&
  decide (raw.barriers.length ≤ MAX_BARRIERS) &&
  decide (barrierIds raw).Nodup &&
  raw.barriers.all (fun barrier =>
    decide (barrier.sector ∈ raw.sectors) &&
    (match hazardById? raw.hazards barrier.hazard with
    | none => false
    | some hazard => decide (hazard.sector = barrier.sector)) &&
    decide (0 < barrier.breachSupplyCost) &&
    decide (barrier.breachSupplyCost ≤ raw.operationalSupplyBudget)) &&
  decide (raw.hazards.length ≤ MAX_HAZARDS) &&
  decide (hazardIds raw).Nodup &&
  raw.hazards.all (fun hazard => decide (hazard.sector ∈ raw.sectors)) &&
  decide (raw.salvage.length ≤ MAX_SALVAGE) &&
  decide (salvageIds raw).Nodup &&
  decide (salvageRelics raw).Nodup &&
  raw.salvage.all (fun item =>
    decide (item.sector ∈ raw.sectors) &&
    decide (item.relic ∈ raw.policy.mission.allowedRelics) &&
    match item.behind with
    | none => true
    | some barrierId =>
        match barrierById? raw.barriers barrierId with
        | none => false
        | some barrier => decide (barrier.sector = item.sector)) &&
  thresholdsValidB raw.thresholds &&
  decide (raw.operationalSupplyBudget ≤ MAX_SUPPLIES) &&
  decide (0 < raw.stepBudget ∧ raw.stepBudget ≤ MAX_STEPS) &&
  decide (raw.fieldArtifact ∈ raw.policy.allowedBeta) &&
  decide (raw.fieldArtifact.missionId = raw.policy.mission.missionId)

/-- The verifier is an injected boundary, so the semantic state machine never
contains a shadow signature implementation. -/
structure Config where
  raw : RawConfig
  verifyApproval : CredentialId → MandateBody → ApprovalSignature → Bool
  valid : configValidB raw = true

def roleOf? (cfg : Config) (officer : OfficerId) : Option SpecialistRole :=
  (seatByOfficer? cfg.raw.roster officer).map Seat.role

def officerOwnsB (cfg : Config) (officer : OfficerId) (role : SpecialistRole) : Bool :=
  decide (roleOf? cfg officer = some role)

def initialCargo (raw : RawConfig) : List CargoRecord :=
  raw.salvage.map fun item => { id := item.id, custody := .onDeck item.sector }

def initialState (cfg : Config) : State where
  phase := .field
  sequence := 0
  supplies := cfg.raw.operationalSupplyBudget
  swept := ∅
  braced := ∅
  damped := ∅
  breached := ∅
  quarantined := ∅
  cargo := initialCargo cfg.raw

def cargoLocationValidB (cfg : Config) (record : CargoRecord) : Bool :=
  match salvageById? cfg.raw.salvage record.id with
  | none => false
  | some spec =>
      match record.custody with
      | .onDeck sector => sector == spec.sector
      | .staged officer => officerOwnsB cfg officer .salvage
      | .secured => true

def noStagedCargoB (state : State) : Bool :=
  state.cargo.all fun record =>
    match record.custody with
    | .staged _ => false
    | _ => true

def noSecuredCargoB (state : State) : Bool :=
  state.cargo.all fun record => record.custody != .secured

def hazardBreachedB (cfg : Config) (state : State) (hazard : HazardId) : Bool :=
  cfg.raw.barriers.any fun barrier =>
    decide (barrier.id ∈ state.breached) && barrier.hazard == hazard

/-- Complete persistent state invariant.  An accepted transition preserves the
authored cargo identity sequence, declared-table membership, bounds, and phase
custody discipline. -/
def stateValidB (cfg : Config) (state : State) : Bool :=
  decide (state.sequence ≤ cfg.raw.stepBudget) &&
  decide (state.supplies ≤ cfg.raw.operationalSupplyBudget) &&
  decide (state.swept ⊆ cfg.raw.sectors.toFinset) &&
  decide (state.braced ⊆ (barrierIds cfg.raw).toFinset) &&
  decide (state.damped ⊆ (hazardIds cfg.raw).toFinset) &&
  decide (state.breached ⊆ (barrierIds cfg.raw).toFinset) &&
  decide (state.quarantined ⊆ (hazardIds cfg.raw).toFinset) &&
  cfg.raw.hazards.all (fun hazard =>
    decide (hazard.id ∉ state.quarantined) || hazardBreachedB cfg state hazard.id) &&
  decide (state.cargo.map CargoRecord.id = salvageIds cfg.raw) &&
  decide (state.cargo.map CargoRecord.id).Nodup &&
  state.cargo.all (cargoLocationValidB cfg) &&
  match state.phase with
  | .field => noSecuredCargoB state
  | .extracted => noStagedCargoB state
  | .aborted => noStagedCargoB state && noSecuredCargoB state

def expectedBody (cfg : Config) (state : State)
    (operation : IrreversibleOp) : MandateBody where
  federationId := cfg.raw.policy.mission.federationId
  missionId := cfg.raw.policy.mission.missionId
  missionArtifact := cfg.raw.policy.mission.artifact
  contentRoot := cfg.raw.policy.mission.contentRoot
  expeditionId := cfg.raw.expeditionId
  rosterDigest := cfg.raw.rosterDigest
  roster := cfg.raw.roster
  sequence := state.sequence
  preState := snapshot state
  operation

def approvalSigners (approvals : List Approval) : List OfficerId :=
  approvals.map Approval.signer

def approvalValidB (cfg : Config) (body : MandateBody)
    (approval : Approval) : Bool :=
  approval.body == body &&
  match seatByOfficer? cfg.raw.roster approval.signer with
  | none => false
  | some seat => cfg.verifyApproval seat.credential body approval.signature

def thresholdFor (thresholds : ThresholdPolicy) : IrreversibleOp → Nat
  | .hazardousBreach _ => thresholds.hazardousBreach
  | .quarantine _ => thresholds.quarantine
  | .extract => thresholds.extract
  | .abort => thresholds.abort

def signersHaveRoleB (cfg : Config) (signers : List OfficerId)
    (role : SpecialistRole) : Bool :=
  signers.any fun officer => officerOwnsB cfg officer role

/-- Numeric threshold is not sufficient: the specialists whose domains are
placed at risk must be among the distinct signers. -/
def operationRolesB (cfg : Config) (operation : IrreversibleOp)
    (signers : List OfficerId) : Bool :=
  match operation with
  | .hazardousBreach _ =>
      signersHaveRoleB cfg signers .engineer &&
      signersHaveRoleB cfg signers .containment
  | .quarantine _ =>
      signersHaveRoleB cfg signers .sensor &&
      signersHaveRoleB cfg signers .containment
  | .extract =>
      signersHaveRoleB cfg signers .engineer &&
      signersHaveRoleB cfg signers .salvage
  | .abort =>
      signersHaveRoleB cfg signers .sensor &&
      signersHaveRoleB cfg signers .containment

/-- Exact multisignature admission.  Duplicate signer rows refuse before their
length can contribute to the threshold. -/
def mandateAcceptedB (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval) : Bool :=
  let body := expectedBody cfg state operation
  let signers := approvalSigners approvals
  decide signers.Nodup &&
  decide (approvals.length ≤ CREW_SIZE) &&
  approvals.all (approvalValidB cfg body) &&
  decide (thresholdFor cfg.raw.thresholds operation ≤ approvals.length) &&
  operationRolesB cfg operation signers

theorem accepted_mandate_signers_are_distinct (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval)
    (h : mandateAcceptedB cfg state operation approvals = true) :
    (approvalSigners approvals).Nodup := by
  simp only [mandateAcceptedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem accepted_mandate_reaches_threshold (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval)
    (h : mandateAcceptedB cfg state operation approvals = true) :
    thresholdFor cfg.raw.thresholds operation ≤ approvals.length := by
  simp only [mandateAcceptedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

theorem accepted_mandate_is_roster_bounded (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval)
    (h : mandateAcceptedB cfg state operation approvals = true) :
    approvals.length ≤ CREW_SIZE := by
  simp only [mandateAcceptedB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

/-- Every counted approval authenticates the one exact body derived from the
current state.  This is stronger than checking only the operation tag. -/
theorem accepted_approval_binds_exact_body (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval) (approval : Approval)
    (haccepted : mandateAcceptedB cfg state operation approvals = true)
    (hmem : approval ∈ approvals) :
    approval.body = expectedBody cfg state operation := by
  simp only [mandateAcceptedB, Bool.and_eq_true, decide_eq_true_eq] at haccepted
  have hall := haccepted.1.1.2
  have hvalid := (List.all_eq_true.mp hall) approval hmem
  simp only [approvalValidB, Bool.and_eq_true] at hvalid
  exact beq_iff_eq.mp hvalid.1

theorem accepted_breach_has_engineer_and_containment
    (cfg : Config) (state : State) (barrier : BarrierId)
    (approvals : List Approval)
    (h : mandateAcceptedB cfg state (.hazardousBreach barrier) approvals = true) :
    signersHaveRoleB cfg (approvalSigners approvals) .engineer = true ∧
      signersHaveRoleB cfg (approvalSigners approvals) .containment = true := by
  simp only [mandateAcceptedB, Bool.and_eq_true, decide_eq_true_eq,
    operationRolesB] at h
  exact h.2

def setCargo (records : List CargoRecord) (id : SalvageId)
    (custody : CargoCustody) : List CargoRecord :=
  records.map fun record => if record.id = id then { record with custody } else record

def secureStaged (records : List CargoRecord) : List CargoRecord :=
  records.map fun record =>
    match record.custody with
    | .staged _ => { record with custody := .secured }
    | _ => record

def restoreStaged (cfg : Config) (records : List CargoRecord) : List CargoRecord :=
  records.map fun record =>
    match record.custody with
    | .staged _ =>
        match salvageById? cfg.raw.salvage record.id with
        | some spec => { record with custody := .onDeck spec.sector }
        | none => record
    | _ => record

def stagedRecords (state : State) : List CargoRecord :=
  state.cargo.filter fun record =>
    match record.custody with
    | .staged _ => true
    | _ => false

def stagedRelics (cfg : Config) (state : State) : List RelicId :=
  (stagedRecords state).filterMap fun record =>
    (salvageById? cfg.raw.salvage record.id).map SalvageSpec.relic

def fieldCandidates (cfg : Config) (state : State) : List ArtifactRef :=
  if state.quarantined = ∅ then [] else [cfg.raw.fieldArtifact]

inductive TerminalKind where
  | extraction
  | abort
deriving Repr, DecidableEq

def rawOutcome (cfg : Config) (state : State) : TerminalKind → ActivityOutcome.Raw
  | .extraction => {
      contribution := {
        intel := state.swept.card
        supplies := state.supplies
        cohesion := CREW_SIZE + state.quarantined.card
        influence := 0
        score := 25 * (stagedRecords state).length +
          10 * state.quarantined.card + 5 * state.breached.card
        relics := stagedRelics cfg state
      }
      betaCandidates := fieldCandidates cfg state
    }
  | .abort => {
      contribution := {
        intel := state.swept.card
        supplies := 0
        cohesion := 1
        influence := 0
        score := 3 * state.quarantined.card
        relics := []
      }
      betaCandidates := fieldCandidates cfg state
    }

structure FinalReceipt (cfg : Config) where
  kind : TerminalKind
  binding : MandateBody
  signers : Finset OfficerId
  finalSequence : Nat
  outcome : ActivityOutcome.Checked cfg.raw.policy
deriving DecidableEq

structure TransitionResult (cfg : Config) where
  state : State
  receipt : Option (FinalReceipt cfg)
deriving DecidableEq

inductive Action where
  | sweep (officer : OfficerId) (sector : SectorId)
  | clearSweep (officer : OfficerId) (sector : SectorId)
  | brace (officer : OfficerId) (barrier : BarrierId)
  | releaseBrace (officer : OfficerId) (barrier : BarrierId)
  | dampen (officer : OfficerId) (hazard : HazardId)
  | releaseDampener (officer : OfficerId) (hazard : HazardId)
  | stage (officer : OfficerId) (salvage : SalvageId)
  | unstage (officer : OfficerId) (salvage : SalvageId)
  | authorized (operation : IrreversibleOp) (approvals : List Approval)
deriving DecidableEq

def reversibleResult (cfg : Config) (state : State) : TransitionResult cfg :=
  { state, receipt := none }

private def sweepTransition (cfg : Config) (state : State)
    (officer : OfficerId) (sector : SectorId) : Option (TransitionResult cfg) :=
  if !officerOwnsB cfg officer .sensor then none
  else if sector ∉ cfg.raw.sectors then none
  else if sector ∈ state.swept then none
  else some (reversibleResult cfg { state with swept := insert sector state.swept })

private def clearSweepTransition (cfg : Config) (state : State)
    (officer : OfficerId) (sector : SectorId) : Option (TransitionResult cfg) :=
  if !officerOwnsB cfg officer .sensor then none
  else if sector ∉ state.swept then none
  else some (reversibleResult cfg {
    state with swept := Finset.erase state.swept sector })

private def braceTransition (cfg : Config) (state : State)
    (officer : OfficerId) (barrierId : BarrierId) : Option (TransitionResult cfg) := do
  let _barrier ← barrierById? cfg.raw.barriers barrierId
  if !officerOwnsB cfg officer .engineer then none
  else if barrierId ∈ state.braced then none
  else some (reversibleResult cfg {
    state with braced := insert barrierId state.braced })

private def releaseBraceTransition (cfg : Config) (state : State)
    (officer : OfficerId) (barrierId : BarrierId) : Option (TransitionResult cfg) :=
  if !officerOwnsB cfg officer .engineer then none
  else if barrierId ∉ state.braced then none
  else some (reversibleResult cfg {
    state with braced := Finset.erase state.braced barrierId })

private def dampenTransition (cfg : Config) (state : State)
    (officer : OfficerId) (hazardId : HazardId) : Option (TransitionResult cfg) := do
  let _hazard ← hazardById? cfg.raw.hazards hazardId
  if !officerOwnsB cfg officer .containment then none
  else if hazardId ∈ state.damped then none
  else some (reversibleResult cfg {
    state with damped := insert hazardId state.damped })

private def releaseDampenerTransition (cfg : Config) (state : State)
    (officer : OfficerId) (hazardId : HazardId) : Option (TransitionResult cfg) :=
  if !officerOwnsB cfg officer .containment then none
  else if hazardId ∉ state.damped then none
  else some (reversibleResult cfg {
    state with damped := Finset.erase state.damped hazardId })

private def stageTransition (cfg : Config) (state : State)
    (officer : OfficerId) (salvageId : SalvageId) : Option (TransitionResult cfg) := do
  let spec ← salvageById? cfg.raw.salvage salvageId
  let record ← cargoById? state.cargo salvageId
  if !officerOwnsB cfg officer .salvage then none
  else if spec.sector ∉ state.swept then none
  else if !(match spec.behind with
    | none => true
    | some barrier => decide (barrier ∈ state.breached)) then none
  else if record.custody != .onDeck spec.sector then none
  else some (reversibleResult cfg {
    state with cargo := setCargo state.cargo salvageId (.staged officer) })

private def unstageTransition (cfg : Config) (state : State)
    (officer : OfficerId) (salvageId : SalvageId) : Option (TransitionResult cfg) := do
  let spec ← salvageById? cfg.raw.salvage salvageId
  let record ← cargoById? state.cargo salvageId
  if !officerOwnsB cfg officer .salvage then none
  else if record.custody != .staged officer then none
  else some (reversibleResult cfg {
    state with cargo := setCargo state.cargo salvageId (.onDeck spec.sector) })

private def breachTransition (cfg : Config) (state : State)
    (barrierId : BarrierId) (approvals : List Approval) : Option (TransitionResult cfg) := do
  let barrier ← barrierById? cfg.raw.barriers barrierId
  let operation := IrreversibleOp.hazardousBreach barrierId
  if !mandateAcceptedB cfg state operation approvals then none
  else if barrierId ∈ state.breached then none
  else if barrier.sector ∉ state.swept then none
  else if barrierId ∉ state.braced then none
  else if barrier.hazard ∉ state.damped then none
  else if state.supplies < barrier.breachSupplyCost then none
  else some (reversibleResult cfg {
    state with
      supplies := state.supplies - barrier.breachSupplyCost
      breached := insert barrierId state.breached })

private def quarantineTransition (cfg : Config) (state : State)
    (hazardId : HazardId) (approvals : List Approval) : Option (TransitionResult cfg) := do
  let _hazard ← hazardById? cfg.raw.hazards hazardId
  let operation := IrreversibleOp.quarantine hazardId
  if !mandateAcceptedB cfg state operation approvals then none
  else if hazardId ∈ state.quarantined then none
  else if !hazardBreachedB cfg state hazardId then none
  else if hazardId ∉ state.damped then none
  else some (reversibleResult cfg {
    state with quarantined := insert hazardId state.quarantined })

private def terminalReceipt? (cfg : Config) (state : State)
    (kind : TerminalKind) (operation : IrreversibleOp)
    (approvals : List Approval) : Option (FinalReceipt cfg) := do
  let outcome ← ActivityOutcome.validate cfg.raw.policy (rawOutcome cfg state kind)
  some {
    kind
    binding := expectedBody cfg state operation
    signers := (approvalSigners approvals).toFinset
    finalSequence := state.sequence + 1
    outcome
  }

private def extractionReadyB (cfg : Config) (state : State) : Bool :=
  !(stagedRecords state).isEmpty &&
  cfg.raw.barriers.all fun barrier =>
    decide (barrier.id ∉ state.breached) ||
      decide (barrier.hazard ∈ state.quarantined)

private def extractTransition (cfg : Config) (state : State)
    (approvals : List Approval) : Option (TransitionResult cfg) := do
  let operation := IrreversibleOp.extract
  if !mandateAcceptedB cfg state operation approvals then none
  else if !extractionReadyB cfg state then none
  else
    let receipt ← terminalReceipt? cfg state .extraction operation approvals
    some {
      state := { state with phase := .extracted, cargo := secureStaged state.cargo }
      receipt := some receipt
    }

private def abortTransition (cfg : Config) (state : State)
    (approvals : List Approval) : Option (TransitionResult cfg) := do
  let operation := IrreversibleOp.abort
  if !mandateAcceptedB cfg state operation approvals then none
  else
    let receipt ← terminalReceipt? cfg state .abort operation approvals
    some {
      state := { state with phase := .aborted, cargo := restoreStaged cfg state.cargo }
      receipt := some receipt
    }

private def irreversibleTransition (cfg : Config) (state : State)
    (operation : IrreversibleOp) (approvals : List Approval) : Option (TransitionResult cfg) :=
  match operation with
  | .hazardousBreach barrier => breachTransition cfg state barrier approvals
  | .quarantine hazard => quarantineTransition cfg state hazard approvals
  | .extract => extractTransition cfg state approvals
  | .abort => abortTransition cfg state approvals

private def transition (cfg : Config) (state : State) : Action → Option (TransitionResult cfg)
  | .sweep officer sector => sweepTransition cfg state officer sector
  | .clearSweep officer sector => clearSweepTransition cfg state officer sector
  | .brace officer barrier => braceTransition cfg state officer barrier
  | .releaseBrace officer barrier => releaseBraceTransition cfg state officer barrier
  | .dampen officer hazard => dampenTransition cfg state officer hazard
  | .releaseDampener officer hazard => releaseDampenerTransition cfg state officer hazard
  | .stage officer salvage => stageTransition cfg state officer salvage
  | .unstage officer salvage => unstageTransition cfg state officer salvage
  | .authorized operation approvals =>
      irreversibleTransition cfg state operation approvals

/-- Public transition.  It accepts only an invariant-preserving field action,
and advances the sequence in one shared place after the action has succeeded. -/
def step (cfg : Config) (state : State) (action : Action) : Option (TransitionResult cfg) :=
  if !stateValidB cfg state then none
  else if state.phase != .field then none
  else if state.sequence ≥ cfg.raw.stepBudget then none
  else
    match transition cfg state action with
    | none => none
    | some result =>
        let advanced := { result.state with sequence := state.sequence + 1 }
        if stateValidB cfg advanced then
          some { result with state := advanced }
        else none

def replay (cfg : Config) : Nat → State → List Action →
    Option (State × List (FinalReceipt cfg))
  | _, state, [] => some (state, [])
  | 0, _, _ :: _ => none
  | fuel + 1, state, action :: actions => do
      let result ← step cfg state action
      let (finalState, receipts) ← replay cfg fuel result.state actions
      let receipts := match result.receipt with
        | none => receipts
        | some receipt => receipt :: receipts
      some (finalState, receipts)

theorem step_deterministic (cfg : Config) (state : State) (action : Action)
    {first second : TransitionResult cfg}
    (hfirst : step cfg state action = some first)
    (hsecond : step cfg state action = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem replay_deterministic (cfg : Config) (fuel : Nat) (state : State)
    (actions : List Action) {first second : State × List (FinalReceipt cfg)}
    (hfirst : replay cfg fuel state actions = some first)
    (hsecond : replay cfg fuel state actions = some second) : first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem step_advances_sequence_exactly (cfg : Config) (state : State) (action : Action)
    (result : TransitionResult cfg) (h : step cfg state action = some result) :
    result.state.sequence = state.sequence + 1 := by
  simp only [step] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i transitionResult htransition
  split at h <;> try contradiction
  cases h
  rfl

theorem step_output_valid (cfg : Config) (state : State) (action : Action)
    (result : TransitionResult cfg) (h : step cfg state action = some result) :
    stateValidB cfg result.state = true := by
  simp only [step] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  assumption

theorem setCargo_preserves_ids (records : List CargoRecord) (id : SalvageId)
    (custody : CargoCustody) :
    (setCargo records id custody).map CargoRecord.id = records.map CargoRecord.id := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      change
        (if record.id = id then { record with custody } else record).id ::
            (setCargo records id custody).map CargoRecord.id =
          record.id :: records.map CargoRecord.id
      rw [ih]
      by_cases heq : record.id = id <;> simp [heq]

theorem secureStaged_preserves_ids (records : List CargoRecord) :
    (secureStaged records).map CargoRecord.id = records.map CargoRecord.id := by
  induction records with
  | nil => rfl
  | cons record records ih =>
      change
        (match record.custody with
          | .staged _ => { record with custody := .secured }
          | _ => record).id :: (secureStaged records).map CargoRecord.id =
          record.id :: records.map CargoRecord.id
      rw [ih]
      cases record.custody <;> rfl

/-- A mandate built for the current snapshot is stale after any accepted action,
because the next snapshot has a different exact sequence. -/
theorem accepted_step_changes_expected_body (cfg : Config) (state : State)
    (action : Action) (result : TransitionResult cfg)
    (operation : IrreversibleOp) (h : step cfg state action = some result) :
    expectedBody cfg result.state operation ≠ expectedBody cfg state operation := by
  intro heq
  have hseq := congrArg MandateBody.sequence heq
  simp only [expectedBody] at hseq
  have hadvance := step_advances_sequence_exactly cfg state action result h
  omega

theorem terminal_outcome_contribution_accepted (cfg : Config)
    (receipt : FinalReceipt cfg) :
    cfg.raw.policy.mission.acceptsContribution receipt.outcome.contribution = true :=
  receipt.outcome.contribution_accepted

theorem terminal_outcome_candidates_declared (cfg : Config)
    (receipt : FinalReceipt cfg) :
    receipt.outcome.betaCandidates ⊆ cfg.raw.policy.allowedBeta :=
  receipt.outcome.beta_candidates_declared

/-! ## Executable expedition: prepare, breach, quarantine, recover, extract -/

def zeroDigest : Digest32 where
  bytes := List.replicate 32 0
  length_eq := by simp

def oneDigest : Digest32 where
  bytes := 1 :: List.replicate 31 0
  length_eq := by simp

def fixtureMissionId : MissionId := ⟨8801⟩
def fixtureSector : SectorId := ⟨447⟩
def fixtureHazard : HazardId := ⟨9⟩
def fixtureBarrier : BarrierId := ⟨12⟩
def fixtureSalvage : SalvageId := ⟨77⟩
def fixtureRelic : RelicId := ⟨600⟩

def fixtureArtifact : ArtifactRef where
  missionId := fixtureMissionId
  artifactId := ⟨8802⟩
  sourceDigest := zeroDigest
  contentDigest := oneDigest

def fixtureMission : MissionSpec where
  missionId := fixtureMissionId
  artifact := fixtureArtifact
  epoch := ⟨1⟩
  federationId := zeroDigest
  contentRoot := oneDigest
  activationDigest := zeroDigest
  contentSession := oneDigest
  runSeed := zeroDigest
  budget := {
    intel := ⟨8, by decide⟩
    supplies := ⟨8, by decide⟩
    cohesion := ⟨8, by decide⟩
    influence := ⟨8, by decide⟩
    score := ⟨100, by decide⟩
    relics := ⟨2, by decide⟩
  }
  allowedRelics := {fixtureRelic}
  privacy := .processSeparatedThreshold
  ballot := .none
  artifact_matches := rfl
  allowed_relics_bounded := by simp

def fixturePolicy : ActivityOutcome.Policy where
  mission := fixtureMission
  allowedBeta := {fixtureArtifact}
  resultLimit := ⟨1, by decide⟩
  catalogue_bounded := by simp

def sensorSeat : Seat := { officer := ⟨1⟩, role := .sensor, credential := ⟨101⟩ }
def engineerSeat : Seat := { officer := ⟨2⟩, role := .engineer, credential := ⟨102⟩ }
def containmentSeat : Seat := { officer := ⟨3⟩, role := .containment, credential := ⟨103⟩ }
def salvageSeat : Seat := { officer := ⟨4⟩, role := .salvage, credential := ⟨104⟩ }

def fixtureRawConfig : RawConfig where
  expeditionId := oneDigest
  rosterDigest := zeroDigest
  roster := [sensorSeat, engineerSeat, containmentSeat, salvageSeat]
  sectors := [fixtureSector]
  barriers := [{
    id := fixtureBarrier
    sector := fixtureSector
    hazard := fixtureHazard
    breachSupplyCost := 2
  }]
  hazards := [{ id := fixtureHazard, sector := fixtureSector }]
  salvage := [{
    id := fixtureSalvage
    sector := fixtureSector
    relic := fixtureRelic
    behind := some fixtureBarrier
  }]
  thresholds := {
    hazardousBreach := 3
    quarantine := 2
    extract := 3
    abort := 2
  }
  operationalSupplyBudget := 4
  stepBudget := 16
  policy := fixturePolicy
  fieldArtifact := fixtureArtifact

theorem fixture_config_valid : configValidB fixtureRawConfig = true := by
  native_decide

def fixtureRemoteSector : SectorId := ⟨448⟩

/-- Merely naming a declared hazard is insufficient: the barrier and hazard must
occupy the same authored sector. -/
def fixtureRemoteHazardRawConfig : RawConfig := {
  fixtureRawConfig with
  sectors := [fixtureSector, fixtureRemoteSector]
  hazards := [{ id := fixtureHazard, sector := fixtureRemoteSector }]
}

theorem cross_sector_hazard_reference_refuses_pack :
    configValidB fixtureRemoteHazardRawConfig = false := by
  native_decide

/-- `behind` means physically behind this local barrier, not dependent on an
arbitrary barrier elsewhere in the activated pack. -/
def fixtureRemoteCargoRawConfig : RawConfig := {
  fixtureRawConfig with
  sectors := [fixtureSector, fixtureRemoteSector]
  salvage := [{
    id := fixtureSalvage
    sector := fixtureRemoteSector
    relic := fixtureRelic
    behind := some fixtureBarrier
  }]
}

theorem cross_sector_salvage_barrier_reference_refuses_pack :
    configValidB fixtureRemoteCargoRawConfig = false := by
  native_decide

/-- A deterministic fixture authenticator.  It is a test double, not a signature
scheme: the production semantic boundary is the injected `verifyApproval`. -/
def fixtureVerifier (credential : CredentialId) (body : MandateBody)
    (signature : ApprovalSignature) : Bool :=
  signature.value == credential.value * 1000 + body.sequence * 10 +
    match body.operation with
    | .hazardousBreach barrier => 1 + barrier.value
    | .quarantine hazard => 100 + hazard.value
    | .extract => 500
    | .abort => 700

def fixtureConfig : Config where
  raw := fixtureRawConfig
  verifyApproval := fixtureVerifier
  valid := fixture_config_valid

def signFixture (cfg : Config) (state : State) (operation : IrreversibleOp)
    (seat : Seat) : Approval :=
  let body := expectedBody cfg state operation
  let suffix := match operation with
    | .hazardousBreach barrier => 1 + barrier.value
    | .quarantine hazard => 100 + hazard.value
    | .extract => 500
    | .abort => 700
  {
    signer := seat.officer
    body
    signature := ⟨seat.credential.value * 1000 + body.sequence * 10 + suffix⟩
  }

def fixtureInitial : State := initialState fixtureConfig

def after? (state : State) (action : Action) : State :=
  match step fixtureConfig state action with
  | some result => result.state
  | none => state

def sweptState : State := after? fixtureInitial (.sweep sensorSeat.officer fixtureSector)
def bracedState : State := after? sweptState (.brace engineerSeat.officer fixtureBarrier)
def preparedState : State := after? bracedState (.dampen containmentSeat.officer fixtureHazard)

def breachOperation : IrreversibleOp := .hazardousBreach fixtureBarrier
def breachApprovals : List Approval :=
  [ signFixture fixtureConfig preparedState breachOperation sensorSeat
  , signFixture fixtureConfig preparedState breachOperation engineerSeat
  , signFixture fixtureConfig preparedState breachOperation containmentSeat
  ]

def breachedState : State :=
  after? preparedState (.authorized breachOperation breachApprovals)

def quarantineOperation : IrreversibleOp := .quarantine fixtureHazard
def quarantineApprovals : List Approval :=
  [ signFixture fixtureConfig breachedState quarantineOperation sensorSeat
  , signFixture fixtureConfig breachedState quarantineOperation containmentSeat
  ]

def quarantinedState : State :=
  after? breachedState (.authorized quarantineOperation quarantineApprovals)

def stagedState : State :=
  after? quarantinedState (.stage salvageSeat.officer fixtureSalvage)

def extractApprovals : List Approval :=
  [ signFixture fixtureConfig stagedState .extract sensorSeat
  , signFixture fixtureConfig stagedState .extract engineerSeat
  , signFixture fixtureConfig stagedState .extract salvageSeat
  ]

def fixturePlan : List Action :=
  [ .sweep sensorSeat.officer fixtureSector
  , .brace engineerSeat.officer fixtureBarrier
  , .dampen containmentSeat.officer fixtureHazard
  , .authorized breachOperation breachApprovals
  , .authorized quarantineOperation quarantineApprovals
  , .stage salvageSeat.officer fixtureSalvage
  , .authorized .extract extractApprovals
  ]

def fixtureMissionSucceedsB : Bool :=
  match replay fixtureConfig fixturePlan.length fixtureInitial fixturePlan with
  | some (state, [receipt]) =>
      decide (state.phase = .extracted) &&
      decide (state.sequence = 7) &&
      decide (state.supplies = 2) &&
      decide (fixtureBarrier ∈ state.breached) &&
      decide (fixtureHazard ∈ state.quarantined) &&
      decide (cargoById? state.cargo fixtureSalvage =
        some { id := fixtureSalvage, custody := .secured }) &&
      decide (receipt.kind = .extraction) &&
      decide (receipt.signers =
        {sensorSeat.officer, engineerSeat.officer, salvageSeat.officer}) &&
      decide (receipt.outcome.contribution.relics = {fixtureRelic}) &&
      decide (fixtureArtifact ∈ receipt.outcome.betaCandidates) &&
      stateValidB fixtureConfig state
  | _ => false

theorem fixture_crew_prepares_breaches_quarantines_and_extracts :
    fixtureMissionSucceedsB = true := by
  native_decide

theorem wrong_specialist_cannot_sweep :
    step fixtureConfig fixtureInitial
      (.sweep engineerSeat.officer fixtureSector) = none := by
  native_decide

def fixtureReversiblePlan : List Action :=
  [ .sweep sensorSeat.officer fixtureSector
  , .clearSweep sensorSeat.officer fixtureSector
  , .sweep sensorSeat.officer fixtureSector
  , .brace engineerSeat.officer fixtureBarrier
  , .releaseBrace engineerSeat.officer fixtureBarrier
  , .brace engineerSeat.officer fixtureBarrier
  , .dampen containmentSeat.officer fixtureHazard
  , .releaseDampener containmentSeat.officer fixtureHazard
  , .dampen containmentSeat.officer fixtureHazard
  ]

def fixtureReversibleRoundTripB : Bool :=
  match replay fixtureConfig fixtureReversiblePlan.length fixtureInitial
      fixtureReversiblePlan with
  | some (state, []) =>
      decide (state.swept = {fixtureSector}) &&
      decide (state.braced = {fixtureBarrier}) &&
      decide (state.damped = {fixtureHazard}) &&
      decide (state.breached = ∅) &&
      decide (state.sequence = fixtureReversiblePlan.length)
  | _ => false

theorem specialists_can_reverse_preparation_without_a_mandate :
    fixtureReversibleRoundTripB = true := by
  native_decide

def duplicateBreachApprovals : List Approval :=
  [ signFixture fixtureConfig preparedState breachOperation engineerSeat
  , signFixture fixtureConfig preparedState breachOperation engineerSeat
  , signFixture fixtureConfig preparedState breachOperation containmentSeat
  ]

theorem duplicate_signer_cannot_fill_breach_threshold :
    mandateAcceptedB fixtureConfig preparedState breachOperation
      duplicateBreachApprovals = false := by
  native_decide

def twoBreachApprovals : List Approval := breachApprovals.take 2

theorem two_of_four_cannot_authorize_hazardous_breach :
    mandateAcceptedB fixtureConfig preparedState breachOperation
      twoBreachApprovals = false := by
  native_decide

def noContainmentBreachApprovals : List Approval :=
  [ signFixture fixtureConfig preparedState breachOperation sensorSeat
  , signFixture fixtureConfig preparedState breachOperation engineerSeat
  , signFixture fixtureConfig preparedState breachOperation salvageSeat
  ]

theorem threshold_without_containment_specialist_refuses :
    mandateAcceptedB fixtureConfig preparedState breachOperation
      noContainmentBreachApprovals = false := by
  native_decide

def wrongMissionApproval : Approval :=
  { (signFixture fixtureConfig preparedState breachOperation sensorSeat) with
    body := { expectedBody fixtureConfig preparedState breachOperation with
      missionId := ⟨999999⟩ } }

def exactEngineerBreachApproval : Approval :=
  signFixture fixtureConfig preparedState breachOperation engineerSeat

def exactContainmentBreachApproval : Approval :=
  signFixture fixtureConfig preparedState breachOperation containmentSeat

theorem wrong_mission_binding_refuses :
    mandateAcceptedB fixtureConfig preparedState breachOperation
      [wrongMissionApproval, exactEngineerBreachApproval,
        exactContainmentBreachApproval] = false := by
  native_decide

def wrongRosterApproval : Approval :=
  { (signFixture fixtureConfig preparedState breachOperation sensorSeat) with
    body := { expectedBody fixtureConfig preparedState breachOperation with
      roster := [engineerSeat, sensorSeat, containmentSeat, salvageSeat] } }

theorem wrong_roster_binding_refuses :
    mandateAcceptedB fixtureConfig preparedState breachOperation
      [wrongRosterApproval, exactEngineerBreachApproval,
        exactContainmentBreachApproval] = false := by
  native_decide

theorem stale_breach_mandate_refuses_after_one_more_action :
    mandateAcceptedB fixtureConfig breachedState breachOperation breachApprovals = false := by
  native_decide

theorem exact_breach_approvals_do_authorize :
    mandateAcceptedB fixtureConfig preparedState breachOperation breachApprovals = true := by
  native_decide

/-- Same sequence is not enough: a certificate for the prepared state cannot be
spent against a different branch carrying altered supplies. -/
def alternatePreparedState : State := { preparedState with supplies := 3 }

theorem full_prestate_snapshot_prevents_same_sequence_branch_replay :
    mandateAcceptedB fixtureConfig alternatePreparedState breachOperation
      breachApprovals = false := by
  native_decide

def unstageResultState : State :=
  after? stagedState (.unstage salvageSeat.officer fixtureSalvage)

def unstageRestoresExactDeckCustodyB : Bool :=
  decide (unstageResultState.sequence = stagedState.sequence + 1) &&
  decide (cargoById? unstageResultState.cargo fixtureSalvage =
    some { id := fixtureSalvage, custody := .onDeck fixtureSector }) &&
  decide (unstageResultState.phase = .field)

theorem salvage_specialist_can_reverse_staging_exactly :
    unstageRestoresExactDeckCustodyB = true := by
  native_decide

def abortApprovals : List Approval :=
  [ signFixture fixtureConfig stagedState .abort sensorSeat
  , signFixture fixtureConfig stagedState .abort containmentSeat
  ]

def fixtureAbortB : Bool :=
  match step fixtureConfig stagedState (.authorized .abort abortApprovals) with
  | some result =>
      match result.receipt with
      | some receipt =>
          decide (result.state.phase = .aborted) &&
          decide (result.state.sequence = stagedState.sequence + 1) &&
          decide (cargoById? result.state.cargo fixtureSalvage =
            some { id := fixtureSalvage, custody := .onDeck fixtureSector }) &&
          decide (receipt.kind = .abort) &&
          decide (receipt.signers = {sensorSeat.officer, containmentSeat.officer}) &&
          decide (receipt.outcome.contribution.relics = ∅) &&
          decide (fixtureArtifact ∈ receipt.outcome.betaCandidates) &&
          stateValidB fixtureConfig result.state
      | none => false
  | none => false

theorem two_specialists_can_abort_and_exact_cargo_returns :
    fixtureAbortB = true := by
  native_decide

def prematureStageState : State := preparedState

theorem cargo_behind_barrier_cannot_be_staged_before_breach :
    step fixtureConfig prematureStageState
      (.stage salvageSeat.officer fixtureSalvage) = none := by
  native_decide

def prematureExtractApprovals : List Approval :=
  [ signFixture fixtureConfig preparedState .extract sensorSeat
  , signFixture fixtureConfig preparedState .extract engineerSeat
  , signFixture fixtureConfig preparedState .extract salvageSeat
  ]

theorem certificate_cannot_vote_past_extraction_readiness :
    step fixtureConfig preparedState
      (.authorized .extract prematureExtractApprovals) = none := by
  native_decide

/-! ## Axiom accounting -/

#assert_axioms accepted_mandate_signers_are_distinct
#assert_axioms accepted_mandate_reaches_threshold
#assert_axioms accepted_mandate_is_roster_bounded
#assert_axioms accepted_approval_binds_exact_body
#assert_axioms accepted_breach_has_engineer_and_containment
#assert_axioms step_deterministic
#assert_axioms replay_deterministic
#assert_axioms step_advances_sequence_exactly
#assert_axioms step_output_valid
#assert_axioms setCargo_preserves_ids
#assert_axioms secureStaged_preserves_ids
#assert_axioms accepted_step_changes_expected_body
#assert_axioms terminal_outcome_contribution_accepted
#assert_axioms terminal_outcome_candidates_declared

#assert_compiled fixture_config_valid
#assert_compiled cross_sector_hazard_reference_refuses_pack
#assert_compiled cross_sector_salvage_barrier_reference_refuses_pack
#assert_compiled fixture_crew_prepares_breaches_quarantines_and_extracts
#assert_compiled wrong_specialist_cannot_sweep
#assert_compiled specialists_can_reverse_preparation_without_a_mandate
#assert_compiled duplicate_signer_cannot_fill_breach_threshold
#assert_compiled two_of_four_cannot_authorize_hazardous_breach
#assert_compiled threshold_without_containment_specialist_refuses
#assert_compiled wrong_mission_binding_refuses
#assert_compiled wrong_roster_binding_refuses
#assert_compiled stale_breach_mandate_refuses_after_one_more_action
#assert_compiled exact_breach_approvals_do_authorize
#assert_compiled full_prestate_snapshot_prevents_same_sequence_branch_replay
#assert_compiled salvage_specialist_can_reverse_staging_exactly
#assert_compiled two_specialists_can_abort_and_exact_cargo_returns
#assert_compiled cargo_behind_barrier_cannot_be_staged_before_breach
#assert_compiled certificate_cannot_vote_past_extraction_readiness

end Dregg2.Games.PathOfAngels.CrewExpeditionAuthority
