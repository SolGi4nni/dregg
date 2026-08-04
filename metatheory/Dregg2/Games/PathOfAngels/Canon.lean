/-
# Dregg2.Games.PathOfAngels.Canon — beta records and curator-only alpha canon.

A game can add an exact artifact to the beta record.  It cannot move anything into
alpha canon or supersede an alpha artifact.  Those transitions require the opaque
`CuratorCapability`, an expected revision, and the exact four-part `ArtifactRef`.
There is deliberately no constructor for that capability in the game semantics.
-/
import Dregg2.Games.PathOfAngels.Judged

namespace Dregg2.Games.PathOfAngels

inductive CanonStatus where
  | beta
  | alpha
  | superseded
deriving DecidableEq, Repr

/-- Canon is represented by one known-artifact population and two disjoint status
subsets.  Beta is the remainder, so an artifact can never simultaneously carry two
statuses. -/
structure CanonState where
  federationId : Digest32
  contentRoot : Digest32
  /-- Digest of the detached, signed activation envelope.  This lives outside the
  self-described content bundle and can therefore name the exact manifest. -/
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  curatorKey : Digest32
  /-- The unique current PoA world.  A game receipt must name this exact value as
  its pre-world, and a successful game effect replaces it with the receipt's
  proof-carrying post-world. -/
  world : WorldState
  known : Finset ArtifactRef
  alpha : Finset ArtifactRef
  superseded : Finset ArtifactRef
  consumedRuns : Finset ReceiptKey
  /-- Canonical strictly-sorted sparse table; absence is the only zero encoding. -/
  playerCounters : PlayerCounterTable
  revision : Nat
  curatorCounter : Nat
  alpha_known : alpha ⊆ known
  superseded_known : superseded ⊆ known
  alpha_disjoint_superseded : Disjoint alpha superseded

def CanonState.empty (federationId contentRoot activationDigest contentSession : Digest32)
    (contentEpoch : EpochId) (curatorKey : Digest32) : CanonState where
  federationId := federationId
  contentRoot := contentRoot
  activationDigest := activationDigest
  contentSession := contentSession
  contentEpoch := contentEpoch
  curatorKey := curatorKey
  world := WorldState.empty
  known := ∅
  alpha := ∅
  superseded := ∅
  consumedRuns := ∅
  playerCounters := PlayerCounterTable.empty
  revision := 0
  curatorCounter := 0
  alpha_known := by simp
  superseded_known := by simp
  alpha_disjoint_superseded := by simp

def CanonState.isBeta (state : CanonState) (artifact : ArtifactRef) : Bool :=
  decide (artifact ∈ state.known ∧ artifact ∉ state.alpha ∧
    artifact ∉ state.superseded)

def CanonState.isAlpha (state : CanonState) (artifact : ArtifactRef) : Bool :=
  decide (artifact ∈ state.known ∧ artifact ∈ state.alpha ∧
    artifact ∉ state.superseded)

theorem CanonState.isBeta_eq_true_iff (state : CanonState) (artifact : ArtifactRef) :
    state.isBeta artifact = true ↔ artifact ∈ state.known ∧
      artifact ∉ state.alpha ∧ artifact ∉ state.superseded := by
  simp [CanonState.isBeta]

theorem CanonState.isAlpha_eq_true_iff (state : CanonState) (artifact : ArtifactRef) :
    state.isAlpha artifact = true ↔ artifact ∈ state.known ∧
      artifact ∈ state.alpha ∧ artifact ∉ state.superseded := by
  simp [CanonState.isAlpha]

def CanonState.status (state : CanonState) (artifact : ArtifactRef) : Option CanonStatus :=
  if artifact ∉ state.known then none
  else if artifact ∈ state.superseded then some .superseded
  else if artifact ∈ state.alpha then some .alpha
  else some .beta

/-! ## The game authority surface -/

/-- A game can register only an artifact carried by a judged run receipt.  There is
no free-standing `discoverBeta` bypass and no alpha/supersede constructor. -/
inductive GameEffect where
  | recordRun (run : JudgedRun)

def GameEffect.artifact : GameEffect → ArtifactRef
  | .recordRun run => run.receipt.mission.artifact

def GameEffect.receipt : GameEffect → RunReceipt
  | .recordRun run => run.receipt

/-- Domain separation and one-shot replay admission for a game-originated beta
record. -/
def GameEffectChecks (effect : GameEffect) (state : CanonState) : Bool :=
  decide (effect.receipt.key ∉ state.consumedRuns) &&
  decide (effect.receipt.federationId = state.federationId) &&
  decide (effect.receipt.contentRoot = state.contentRoot) &&
  decide (effect.receipt.activationDigest = state.activationDigest) &&
  decide (effect.receipt.contentSession = state.contentSession) &&
  decide (effect.receipt.contentEpoch = state.contentEpoch) &&
  decide (effect.receipt.previousPlayerCounter =
    (state.playerCounters.lookup effect.receipt.counterKey).val) &&
  decide (effect.receipt.preWorld = state.world) &&
  decide (effect.receipt.playerCounter < PLAYER_COUNTER_MODULUS)

theorem GameEffectChecks_eq_true_iff (effect : GameEffect) (state : CanonState) :
    GameEffectChecks effect state = true ↔
      effect.receipt.key ∉ state.consumedRuns ∧
      effect.receipt.federationId = state.federationId ∧
      effect.receipt.contentRoot = state.contentRoot ∧
      effect.receipt.activationDigest = state.activationDigest ∧
      effect.receipt.contentSession = state.contentSession ∧
      effect.receipt.contentEpoch = state.contentEpoch ∧
      effect.receipt.previousPlayerCounter =
        (state.playerCounters.lookup effect.receipt.counterKey).val ∧
      effect.receipt.preWorld = state.world ∧
      effect.receipt.playerCounter < PLAYER_COUNTER_MODULUS := by
  simp only [GameEffectChecks, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- A game effect adds exactly one known beta candidate and preserves both curated
status sets byte-for-byte. -/
def applyGameEffect (effect : GameEffect) (state : CanonState) : Option CanonState :=
  if hchecks : GameEffectChecks effect state = true then
    let checks := (GameEffectChecks_eq_true_iff effect state).mp hchecks
    let nextCounter : PlayerCounter :=
      ⟨effect.receipt.playerCounter, checks.2.2.2.2.2.2.2.2⟩
    let nextCounterNonzero : nextCounter ≠ 0 := by
      intro hzero
      have hval := congrArg Fin.val hzero
      have hpositive := effect.receipt.player_counter_positive
      simp only [nextCounter, Fin.val_zero] at hval
      omega
    some {
      federationId := state.federationId
      contentRoot := state.contentRoot
      activationDigest := state.activationDigest
      contentSession := state.contentSession
      contentEpoch := state.contentEpoch
      curatorKey := state.curatorKey
      world := effect.receipt.postWorld
      known := insert effect.artifact state.known
      alpha := state.alpha
      superseded := state.superseded
      consumedRuns := insert effect.receipt.key state.consumedRuns
      playerCounters := state.playerCounters.set effect.receipt.counterKey nextCounter
        nextCounterNonzero
      revision := state.revision + 1
      curatorCounter := state.curatorCounter
      alpha_known := by
        intro artifact ha
        exact Finset.mem_insert_of_mem (state.alpha_known ha)
      superseded_known := by
        intro artifact hs
        exact Finset.mem_insert_of_mem (state.superseded_known hs)
      alpha_disjoint_superseded := state.alpha_disjoint_superseded
    }
  else none

theorem applyGameEffect_alpha_unchanged {effect : GameEffect} {before after : CanonState}
    (h : applyGameEffect effect before = some after) : after.alpha = before.alpha := by
  simp only [applyGameEffect] at h
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem applyGameEffect_superseded_unchanged {effect : GameEffect}
    {before after : CanonState} (h : applyGameEffect effect before = some after) :
    after.superseded = before.superseded := by
  simp only [applyGameEffect] at h
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]

theorem applyGameEffect_records_beta_candidate {effect : GameEffect}
    {before after : CanonState} (h : applyGameEffect effect before = some after) :
    effect.artifact ∈ after.known := by
  simp only [applyGameEffect] at h
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

theorem applyGameEffect_replay_refused (effect : GameEffect) (state : CanonState)
    (h : effect.receipt.key ∈ state.consumedRuns) :
    applyGameEffect effect state = none := by
  simp [applyGameEffect, GameEffectChecks, h]

theorem applyGameEffect_consumes_counter {effect : GameEffect} {before after : CanonState}
    (h : applyGameEffect effect before = some after) :
    effect.receipt.key ∈ after.consumedRuns := by
  simp only [applyGameEffect] at h
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  simp

theorem applyGameEffect_advances_player_counter {effect : GameEffect}
    {before after : CanonState} (h : applyGameEffect effect before = some after) :
    (before.playerCounters.lookup effect.receipt.counterKey).val =
        effect.receipt.previousPlayerCounter ∧
      (after.playerCounters.lookup effect.receipt.counterKey).val = effect.receipt.playerCounter := by
  simp only [applyGameEffect] at h
  split at h
  · rename_i hc
    have checks := (GameEffectChecks_eq_true_iff effect before).mp hc
    injection h with heq
    rw [← heq]
    constructor
    · exact checks.2.2.2.2.2.2.1.symm
    · simp
  · contradiction

/-- Canon owns the world chain: the receipt starts at the exact canonical world
and successful admission installs its proof-carrying successor. -/
theorem applyGameEffect_chains_world {effect : GameEffect}
    {before after : CanonState} (h : applyGameEffect effect before = some after) :
    effect.receipt.preWorld = before.world ∧
      after.world = effect.receipt.postWorld := by
  simp only [applyGameEffect] at h
  split at h
  · rename_i hc
    have checks := (GameEffectChecks_eq_true_iff effect before).mp hc
    injection h with heq
    rw [← heq]
    exact ⟨checks.2.2.2.2.2.2.2.1, rfl⟩
  · contradiction

theorem applyGameEffect_same_counter_replay_refused {effect : GameEffect}
    {before after : CanonState} (h : applyGameEffect effect before = some after) :
    applyGameEffect effect after = none :=
  applyGameEffect_replay_refused effect after (applyGameEffect_consumes_counter h)

/-! ## Atomic judged game settlement -/

/-- The public result of the one semantic transaction: executable judgment first,
then exact canon admission.  `postWorld` is a projection of the judged receipt,
never an independently supplied state. -/
structure SettledRun where
  judged : JudgedRun
  postWorld : WorldState
  postCanon : CanonState
  postWorld_exact : postWorld = judged.receipt.postWorld

def settleActiveRun (active : ActiveRunState) (carrier : FinalizedCarrier)
    (claim : RunClaim) (submitted : SubmittedRun) (beforeCanon : CanonState) :
    Option SettledRun :=
  match judgeActive active carrier claim submitted with
  | none => none
  | some judged =>
      match applyGameEffect (.recordRun judged) beforeCanon with
      | none => none
      | some postCanon => some {
          judged
          postWorld := judged.receipt.postWorld
          postCanon
          postWorld_exact := rfl
        }

theorem settleActiveRun_success_exact {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {submitted : SubmittedRun}
    {beforeCanon : CanonState} {settled : SettledRun}
    (h : settleActiveRun active carrier claim submitted beforeCanon = some settled) :
    judgeActive active carrier claim submitted = some settled.judged ∧
      applyGameEffect (.recordRun settled.judged) beforeCanon = some settled.postCanon ∧
      settled.postWorld = settled.judged.receipt.postWorld := by
  unfold settleActiveRun at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Option.some.injEq] at h
  subst settled
  exact ⟨by assumption, by assumption, rfl⟩

theorem settleActiveRun_success_counter_advanced {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {submitted : SubmittedRun}
    {beforeCanon : CanonState} {settled : SettledRun}
    (h : settleActiveRun active carrier claim submitted beforeCanon = some settled) :
    (settled.postCanon.playerCounters.lookup settled.judged.receipt.counterKey).val =
      settled.judged.receipt.playerCounter := by
  have exactness := settleActiveRun_success_exact h
  exact (applyGameEffect_advances_player_counter exactness.2.1).2

theorem settleActiveRun_success_world_chained {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {submitted : SubmittedRun}
    {beforeCanon : CanonState} {settled : SettledRun}
    (h : settleActiveRun active carrier claim submitted beforeCanon = some settled) :
    settled.judged.receipt.preWorld = beforeCanon.world ∧
      settled.postCanon.world = settled.judged.receipt.postWorld ∧
      settled.postWorld = settled.postCanon.world := by
  have exactness := settleActiveRun_success_exact h
  have chained := applyGameEffect_chains_world exactness.2.1
  exact ⟨chained.1, chained.2, exactness.2.2.trans chained.2.symm⟩

theorem settleActiveRun_replay_refused {active : ActiveRunState}
    {carrier : FinalizedCarrier} {claim : RunClaim} {submitted : SubmittedRun}
    {beforeCanon : CanonState} {settled : SettledRun}
    (h : settleActiveRun active carrier claim submitted beforeCanon = some settled) :
    applyGameEffect (.recordRun settled.judged) settled.postCanon = none := by
  exact applyGameEffect_same_counter_replay_refused (settleActiveRun_success_exact h).2.1

/-! ## Curator actions -/

/-- One Lean-owned admission carrier for every curator mutation.  The detached
activation digest binds the exact signed manifest without introducing a
self-referential digest inside that manifest's catalog. -/
structure CanonAdmission where
  federationId : Digest32
  contentRoot : Digest32
  activationDigest : Digest32
  contentSession : Digest32
  contentEpoch : EpochId
  curatorKey : Digest32
  expectedRevision : Nat
  previousCuratorCounter : Nat
  curatorCounter : Nat

def CanonAdmission.accepts (admission : CanonAdmission) (state : CanonState) : Bool :=
  decide (admission.federationId = state.federationId) &&
  decide (admission.contentRoot = state.contentRoot) &&
  decide (admission.activationDigest = state.activationDigest) &&
  decide (admission.contentSession = state.contentSession) &&
  decide (admission.contentEpoch = state.contentEpoch) &&
  decide (admission.curatorKey = state.curatorKey) &&
  decide (admission.expectedRevision = state.revision) &&
  decide (admission.previousCuratorCounter = state.curatorCounter) &&
  decide (admission.curatorCounter = admission.previousCuratorCounter + 1)

theorem CanonAdmission.accepts_eq_true_iff (admission : CanonAdmission)
    (state : CanonState) : admission.accepts state = true ↔
      admission.federationId = state.federationId ∧
      admission.contentRoot = state.contentRoot ∧
      admission.activationDigest = state.activationDigest ∧
      admission.contentSession = state.contentSession ∧
      admission.contentEpoch = state.contentEpoch ∧
      admission.curatorKey = state.curatorKey ∧
      admission.expectedRevision = state.revision ∧
      admission.previousCuratorCounter = state.curatorCounter ∧
      admission.curatorCounter = admission.previousCuratorCounter + 1 := by
  simp only [CanonAdmission.accepts, Bool.and_eq_true, decide_eq_true_eq]
  tauto

theorem CanonAdmission.rejects_wrong_curatorKey (admission : CanonAdmission)
    (state : CanonState) (h : admission.curatorKey ≠ state.curatorKey) :
    admission.accepts state = false := by
  simp [CanonAdmission.accepts, h]

theorem CanonAdmission.rejects_wrong_activation (admission : CanonAdmission)
    (state : CanonState) (h : admission.activationDigest ≠ state.activationDigest) :
    admission.accepts state = false := by
  simp [CanonAdmission.accepts, h]

/-- Promote precisely this reviewed artifact under one complete admission. -/
structure Promotion where
  artifact : ArtifactRef
  admission : CanonAdmission

/-- Supersede precisely this alpha artifact under one complete admission. -/
structure Supersession where
  artifact : ArtifactRef
  admission : CanonAdmission

inductive CuratorAction where
  | promote (promotion : Promotion)
  | supersede (supersession : Supersession)

def CuratorAction.admission : CuratorAction → CanonAdmission
  | .promote promotion => promotion.admission
  | .supersede supersession => supersession.admission

/-- Issued only after verifying the pinned curator's signature over the canonical
bytes of this exact full action.  The index includes the action tag, exact artifact,
and every admission field, so a token cannot be replayed for another decision. -/
opaque CuratorCapability (action : CuratorAction) : Type

/-- Exact-artifact beta → alpha promotion.  A stale revision, unknown artifact,
already-alpha artifact, or superseded artifact refuses. -/
def applyPromotion (promotion : Promotion)
    (_capability : CuratorCapability (.promote promotion))
    (state : CanonState) : Option CanonState :=
  if hadmission : promotion.admission.accepts state = true then
    if hb : state.isBeta promotion.artifact = true then
      let hp := (CanonState.isBeta_eq_true_iff state promotion.artifact).mp hb
      some {
        federationId := state.federationId
        contentRoot := state.contentRoot
        activationDigest := state.activationDigest
        contentSession := state.contentSession
        contentEpoch := state.contentEpoch
        curatorKey := state.curatorKey
        world := state.world
        known := state.known
        alpha := insert promotion.artifact state.alpha
        superseded := state.superseded
        consumedRuns := state.consumedRuns
        playerCounters := state.playerCounters
        revision := state.revision + 1
        curatorCounter := promotion.admission.curatorCounter
        alpha_known := by
          intro artifact ha
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hp.1
          · exact state.alpha_known ha
        superseded_known := state.superseded_known
        alpha_disjoint_superseded := by
          rw [Finset.disjoint_left]
          intro artifact ha hs
          rcases Finset.mem_insert.mp ha with rfl | ha
          · exact hp.2.2 hs
          · exact (Finset.disjoint_left.mp state.alpha_disjoint_superseded) ha hs
      }
    else none
  else none

/-- Exact-artifact alpha → superseded transition. -/
def applySupersession (supersession : Supersession)
    (_capability : CuratorCapability (.supersede supersession))
    (state : CanonState) : Option CanonState :=
  if hadmission : supersession.admission.accepts state = true then
    if ha : state.isAlpha supersession.artifact = true then
      let hp := (CanonState.isAlpha_eq_true_iff state supersession.artifact).mp ha
      some {
        federationId := state.federationId
        contentRoot := state.contentRoot
        activationDigest := state.activationDigest
        contentSession := state.contentSession
        contentEpoch := state.contentEpoch
        curatorKey := state.curatorKey
        world := state.world
        known := state.known
        alpha := state.alpha.erase supersession.artifact
        superseded := insert supersession.artifact state.superseded
        consumedRuns := state.consumedRuns
        playerCounters := state.playerCounters
        revision := state.revision + 1
        curatorCounter := supersession.admission.curatorCounter
        alpha_known := by
          intro artifact hmem
          exact state.alpha_known (Finset.mem_of_mem_erase hmem)
        superseded_known := by
          intro artifact hmem
          rcases Finset.mem_insert.mp hmem with rfl | hmem
          · exact hp.1
          · exact state.superseded_known hmem
        alpha_disjoint_superseded := by
          rw [Finset.disjoint_left]
          intro artifact hAlpha hSuperseded
          rcases Finset.mem_insert.mp hSuperseded with hEq | hOld
          · subst artifact
            exact (Finset.mem_erase.mp hAlpha).1 rfl
          · exact (Finset.disjoint_left.mp state.alpha_disjoint_superseded)
              (Finset.mem_of_mem_erase hAlpha) hOld
      }
    else none
  else none

def applyCuratorAction (action : CuratorAction)
    (capability : CuratorCapability action)
    (state : CanonState) : Option CanonState :=
  match action with
  | .promote promotion => applyPromotion promotion capability state
  | .supersede supersession => applySupersession supersession capability state

theorem applyPromotion_exact {promotion : Promotion}
    {capability : CuratorCapability (.promote promotion)}
    {before after : CanonState} (h : applyPromotion promotion capability before = some after) :
    after.alpha = insert promotion.artifact before.alpha ∧
      after.known = before.known ∧ after.superseded = before.superseded := by
  simp only [applyPromotion] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  exact ⟨rfl, rfl, rfl⟩

theorem applyPromotion_admission_exact {promotion : Promotion}
    {capability : CuratorCapability (.promote promotion)}
    {before after : CanonState} (h : applyPromotion promotion capability before = some after) :
    promotion.admission.accepts before = true ∧
      after.curatorCounter = promotion.admission.curatorCounter ∧
      after.revision = before.revision + 1 := by
  simp only [applyPromotion] at h
  split at h
  · rename_i hadmission
    split at h <;> try contradiction
    injection h with heq
    rw [← heq]
    exact ⟨hadmission, rfl, rfl⟩
  · contradiction

theorem applyPromotion_rejects_stale_revision (promotion : Promotion)
    (capability : CuratorCapability (.promote promotion))
    (state : CanonState)
    (h : promotion.admission.expectedRevision ≠ state.revision) :
    applyPromotion promotion capability state = none := by
  simp [applyPromotion, CanonAdmission.accepts, h]

theorem applyPromotion_rejects_nonbeta (promotion : Promotion)
    (capability : CuratorCapability (.promote promotion))
    (state : CanonState)
    (h : state.isBeta promotion.artifact = false) :
    applyPromotion promotion capability state = none := by
  simp [applyPromotion, h]

theorem applySupersession_exact {supersession : Supersession}
    {capability : CuratorCapability (.supersede supersession)}
    {before after : CanonState}
    (h : applySupersession supersession capability before = some after) :
    after.alpha = before.alpha.erase supersession.artifact ∧
      after.superseded = insert supersession.artifact before.superseded ∧
      after.known = before.known := by
  simp only [applySupersession] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  exact ⟨rfl, rfl, rfl⟩

theorem applySupersession_admission_exact {supersession : Supersession}
    {capability : CuratorCapability (.supersede supersession)}
    {before after : CanonState}
    (h : applySupersession supersession capability before = some after) :
    supersession.admission.accepts before = true ∧
      after.curatorCounter = supersession.admission.curatorCounter ∧
      after.revision = before.revision + 1 := by
  simp only [applySupersession] at h
  split at h
  · rename_i hadmission
    split at h <;> try contradiction
    injection h with heq
    rw [← heq]
    exact ⟨hadmission, rfl, rfl⟩
  · contradiction

/-! ## The authority theorem -/

inductive CanonTransition : CanonState → CanonState → Prop where
  | game (effect : GameEffect) {before after : CanonState}
      (applied : applyGameEffect effect before = some after) :
      CanonTransition before after
  | curator (action : CuratorAction)
      (capability : CuratorCapability action)
      {before after : CanonState}
      (applied : applyCuratorAction action capability before = some after) :
      CanonTransition before after

/-- If alpha changes along a declared canon transition, the transition contains an
actual opaque curator capability and a curator action whose checked application is
the new state.  The game case is discharged by `applyGameEffect_alpha_unchanged`. -/
theorem alpha_change_requires_curator {before after : CanonState}
    (transition : CanonTransition before after) (changed : before.alpha ≠ after.alpha) :
    ∃ action, ∃ capability : CuratorCapability action,
      applyCuratorAction action capability before = some after := by
  cases transition with
  | game effect applied =>
      exact (changed (applyGameEffect_alpha_unchanged applied).symm).elim
  | curator action capability applied =>
      exact ⟨action, capability, applied⟩

/-- No game effect can promote canon. -/
theorem no_game_effect_promotes {effect : GameEffect} {before after : CanonState}
    (applied : applyGameEffect effect before = some after) :
    after.alpha = before.alpha :=
  applyGameEffect_alpha_unchanged applied

#assert_axioms CanonState.isBeta_eq_true_iff
#assert_axioms CanonState.isAlpha_eq_true_iff
#assert_axioms CanonAdmission.accepts_eq_true_iff
#assert_axioms CanonAdmission.rejects_wrong_curatorKey
#assert_axioms CanonAdmission.rejects_wrong_activation
#assert_axioms GameEffectChecks_eq_true_iff
#assert_axioms applyGameEffect_alpha_unchanged
#assert_axioms applyGameEffect_superseded_unchanged
#assert_axioms applyGameEffect_records_beta_candidate
#assert_axioms applyGameEffect_replay_refused
#assert_axioms applyGameEffect_consumes_counter
#assert_axioms applyGameEffect_advances_player_counter
#assert_axioms applyGameEffect_chains_world
#assert_axioms applyGameEffect_same_counter_replay_refused
#assert_axioms settleActiveRun_success_exact
#assert_axioms settleActiveRun_success_counter_advanced
#assert_axioms settleActiveRun_success_world_chained
#assert_axioms settleActiveRun_replay_refused
#assert_axioms applyPromotion_exact
#assert_axioms applyPromotion_admission_exact
#assert_axioms applyPromotion_rejects_stale_revision
#assert_axioms applyPromotion_rejects_nonbeta
#assert_axioms applySupersession_exact
#assert_axioms applySupersession_admission_exact
#assert_axioms alpha_change_requires_curator
#assert_axioms no_game_effect_promotes

end Dregg2.Games.PathOfAngels
