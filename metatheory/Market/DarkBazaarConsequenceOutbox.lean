/-
# Market.DarkBazaarConsequenceOutbox — prepare first, dispatch once, recover by observation

The Dark Bazaar's private clearing proof authorizes a game consequence, but the proof alone does
not make an external game turn exactly once.  The deployment must choose the market, roster,
reward rule, target, and method; persist a complete global consequence key before dispatch; and
pass that same key into an idempotent executor ledger.

This module states that protocol as two durable maps:

* the outbox moves `absent -> prepared -> landed`;
* the executor ledger moves `absent -> committed` under the same `ConsequenceKey`.

The executor commit deliberately leaves the outbox in `prepared`.  That is the real crash window:
the effect may already have landed while the host has not yet recorded its receipt.  Retrying from
that state cannot commit another effect because the executor ledger already owns the global key;
recovery only observes that receipt and advances the outbox to `landed`.

The key below is the complete semantic tuple, not its deployed hash compression.  Hash collision
resistance and persistence refinement are external cryptographic/system obligations; no such fact
is smuggled in as a Lean axiom.
-/

import Dregg2.Tactics

namespace Market.DarkBazaarConsequenceOutbox

set_option autoImplicit false

/-! ## 1. Deployment-owned identity and reward policy -/

abbrev DeploymentId := Nat
abbrev CellId := Nat
abbrev ActorId := Nat
abbrev AssetId := Nat
abbrev MethodId := Nat
abbrev Digest := Nat
abbrev TurnId := Nat

/-- Full public market identity.  A 32-bit proof session is not an application identity. -/
structure MarketIdentity where
  deployment : DeploymentId
  listingCell : CellId
  seller : ActorId
  reserve : Nat
  deterministicSeed : Digest
  relationId : Digest
deriving DecidableEq, Repr

/-- One deployment-owned guild roster seat.  A private winner selects the corresponding character
cell; the winner is never itself treated as a target cell. -/
structure RosterSeat where
  actor : ActorId
  characterCell : CellId
deriving DecidableEq, Repr

/-- Deployment-owned roster and reward rule.  The complete ordered roster and rule are part of the
replay identity, not merely checked against a caller-provided self-pin. -/
structure RewardPolicy where
  policyId : Digest
  rosterCommitment : Digest
  roster : List RosterSeat
  method : MethodId
  rewardAsset : AssetId
  rewardAmount : Nat
  consequenceTag : Digest
deriving DecidableEq, Repr

/-- Ordered finite winner-to-character selection.  A missing winner fails closed. -/
def selectTargetFromRoster : List RosterSeat → ActorId → Option CellId
  | [], _ => none
  | seat :: rest, winner =>
      if seat.actor = winner then some seat.characterCell
      else selectTargetFromRoster rest winner

def RewardPolicy.selectTarget (policy : RewardPolicy) (winner : ActorId) : Option CellId :=
  selectTargetFromRoster policy.roster winner

/-- Every successful selection is witnessed by an actual finite roster seat. -/
theorem selectTargetFromRoster_sound {roster : List RosterSeat}
    {winner : ActorId} {target : CellId}
    (selected : selectTargetFromRoster roster winner = some target) :
    ∃ seat, seat ∈ roster ∧ seat.actor = winner ∧ seat.characterCell = target := by
  induction roster with
  | nil => simp [selectTargetFromRoster] at selected
  | cons head tail ih =>
      simp only [selectTargetFromRoster] at selected
      split at selected
      · rename_i actorMatches
        simp only [Option.some.injEq] at selected
        exact ⟨head, by simp, actorMatches, selected⟩
      · rcases ih selected with ⟨seat, member, actorMatches, targetMatches⟩
        exact ⟨seat, by simp [member], actorMatches, targetMatches⟩

/-- The host configuration owns both market and policy. -/
structure DeploymentConfig where
  id : DeploymentId
  market : MarketIdentity
  policy : RewardPolicy
  marketOwned : market.deployment = id
  rosterActorsUnique : (policy.roster.map RosterSeat.actor).Nodup
deriving Repr

/-- Complete accepted private-settlement identity. -/
structure VerifiedSettlement where
  market : MarketIdentity
  sourceReceipt : Digest
  acceptedStatement : Digest
  winner : ActorId
  settlementTurn : TurnId
  finalReceipt : Digest
deriving DecidableEq, Repr

/-- Only a settlement for the configured market, backed by non-sentinel final coordinates, may
enter this consequence protocol. -/
structure DeploymentAccepts (deployment : DeploymentConfig)
    (settlement : VerifiedSettlement) : Prop where
  market : settlement.market = deployment.market
  settlementTurnNonzero : settlement.settlementTurn ≠ 0
  finalReceiptNonzero : settlement.finalReceipt ≠ 0

/-- Payload-free player intent.  It carries no market, roster, reward, target, or method. -/
inductive PublicAction where
  | enter
  | refresh
deriving DecidableEq, Repr

structure PlayerRequest where
  journeyId : Digest
  action : PublicAction
deriving DecidableEq, Repr

/-! ## 2. Global consequence key and exact effect -/

/-- Lossless global key.  New frontend objects or request ids cannot create a second identity for
the same verified settlement and deployment policy. -/
structure ConsequenceKey where
  deployment : DeploymentId
  market : MarketIdentity
  policy : RewardPolicy
  sourceReceipt : Digest
  acceptedStatement : Digest
  winner : ActorId
  settlementTurn : TurnId
  finalReceipt : Digest
deriving DecidableEq, Repr

/-- Exact executor effect.  Every routing and reward field comes from deployment configuration;
the recipient alone comes from the verified private result. -/
structure GameEffect where
  recipient : ActorId
  target : CellId
  method : MethodId
  rewardAsset : AssetId
  rewardAmount : Nat
  consequenceTag : Digest
deriving DecidableEq, Repr

def consequenceKey (deployment : DeploymentConfig)
    (settlement : VerifiedSettlement) : ConsequenceKey :=
  { deployment := deployment.id
    market := deployment.market
    policy := deployment.policy
    sourceReceipt := settlement.sourceReceipt
    acceptedStatement := settlement.acceptedStatement
    winner := settlement.winner
    settlementTurn := settlement.settlementTurn
    finalReceipt := settlement.finalReceipt }

def deploymentEffect (deployment : DeploymentConfig)
    (settlement : VerifiedSettlement) (selectedTarget : CellId) : GameEffect :=
  { recipient := settlement.winner
    target := selectedTarget
    method := deployment.policy.method
    rewardAsset := deployment.policy.rewardAsset
    rewardAmount := deployment.policy.rewardAmount
    consequenceTag := deployment.policy.consequenceTag }

/-- Persistable operation prepared by the host.  `requestAudit` is presentation provenance only;
it does not occur in the authority key or effect. -/
structure PreparedOperation where
  key : ConsequenceKey
  effect : GameEffect
  requestAudit : Digest
deriving DecidableEq, Repr

/-- The sole preparation function accepts the deployment's policy, not a policy argument from the
player.  An unpinned winner fails closed instead of being routed to a caller-selected/default cell. -/
def prepare (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (_accepted : DeploymentAccepts deployment settlement)
    (request : PlayerRequest) : Option PreparedOperation :=
  match deployment.policy.selectTarget settlement.winner with
  | none => none
  | some target => some
      { key := consequenceKey deployment settlement
        effect := deploymentEffect deployment settlement target
        requestAudit := request.journeyId }

/-- The prepared global key names the deployment-owned market and policy exactly. -/
theorem prepared_key_is_deployment_owned
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation) :
    operation.key.market = deployment.market ∧
    operation.key.policy = deployment.policy := by
  unfold prepare at prepared
  split at prepared
  · contradiction
  · simp only [Option.some.injEq] at prepared
    subst operation
    exact ⟨rfl, rfl⟩

/-- The prepared reward and method are the deployment's values, while the target is exactly the
character cell selected for the verified winner by the deployment-owned finite roster. -/
theorem prepared_effect_is_deployment_owned
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation) :
    ∃ target,
      deployment.policy.selectTarget settlement.winner = some target ∧
      operation.effect = deploymentEffect deployment settlement target := by
  unfold prepare at prepared
  split at prepared
  · simp_all
  · rename_i target selected
    simp only [Option.some.injEq] at prepared
    subst operation
    exact ⟨target, selected, rfl⟩

/-- In particular, the prepared target is the selected guild character, not the winner id or a
caller-provided cell. -/
theorem prepared_target_is_roster_selected
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation) :
    deployment.policy.selectTarget settlement.winner = some operation.effect.target := by
  rcases prepared_effect_is_deployment_owned deployment settlement accepted request operation
    prepared with ⟨target, selected, effect⟩
  rw [effect]
  exact selected

/-- The selected target is backed by an actual deployment-owned roster entry for the verified
winner. -/
theorem prepared_target_is_roster_member
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation) :
    ∃ seat, seat ∈ deployment.policy.roster ∧
      seat.actor = settlement.winner ∧
      seat.characterCell = operation.effect.target := by
  apply selectTargetFromRoster_sound
  exact prepared_target_is_roster_selected deployment settlement accepted request operation prepared

/-- A verified winner absent from the deployment roster cannot produce an operation. -/
theorem unpinned_winner_cannot_prepare
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (missing : deployment.policy.selectTarget settlement.winner = none) :
    prepare deployment settlement accepted request = none := by
  simp [prepare, missing]

/-- Changing the public journey request cannot alter either authority key or game effect. -/
theorem caller_request_cannot_change_authority
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (left right : PlayerRequest)
    (leftOperation rightOperation : PreparedOperation)
    (leftPrepared : prepare deployment settlement accepted left = some leftOperation)
    (rightPrepared : prepare deployment settlement accepted right = some rightOperation) :
    leftOperation.key = rightOperation.key ∧
    leftOperation.effect = rightOperation.effect := by
  unfold prepare at leftPrepared rightPrepared
  cases selected : deployment.policy.selectTarget settlement.winner with
  | none => simp [selected] at leftPrepared
  | some target =>
    simp only [selected, Option.some.injEq] at leftPrepared rightPrepared
    subst leftOperation
    subst rightOperation
    exact ⟨rfl, rfl⟩

/-- A settlement for another market cannot be accepted by this deployment. -/
theorem substituted_market_refused (deployment : DeploymentConfig)
    (settlement : VerifiedSettlement)
    (wrong : settlement.market ≠ deployment.market) :
    ¬ DeploymentAccepts deployment settlement := by
  intro accepted
  exact wrong accepted.market

/-- Distinct deployment markets yield distinct global keys, even for identical settlement bytes. -/
theorem different_market_has_different_key
    {left right : DeploymentConfig} (settlement : VerifiedSettlement)
    (different : left.market ≠ right.market) :
    consequenceKey left settlement ≠ consequenceKey right settlement := by
  intro equal
  exact different (congrArg ConsequenceKey.market equal)

/-- Distinct deployment policies yield distinct global keys. -/
theorem different_policy_has_different_key
    {left right : DeploymentConfig} (settlement : VerifiedSettlement)
    (different : left.policy ≠ right.policy) :
    consequenceKey left settlement ≠ consequenceKey right settlement := by
  intro equal
  exact different (congrArg ConsequenceKey.policy equal)

/-! ## 3. Executor receipt and durable maps -/

/-- Opaque-in-production executor result, modeled here by its semantic fields. -/
structure EngineReceipt where
  key : ConsequenceKey
  effect : GameEffect
  gameTurn : TurnId
  preState : Digest
  postState : Digest
  finalized : Bool
deriving DecidableEq, Repr

def EngineReceipt.Binds (receipt : EngineReceipt) (operation : PreparedOperation) : Prop :=
  receipt.key = operation.key ∧
  receipt.effect = operation.effect ∧
  receipt.gameTurn ≠ 0 ∧
  receipt.preState ≠ receipt.postState ∧
  receipt.finalized = true

/-- Durable outbox phase.  A settled/landed shape cannot exist without its exact operation and
executor receipt. -/
inductive OutboxEntry where
  | prepared (operation : PreparedOperation)
  | landed (operation : PreparedOperation) (receipt : EngineReceipt)
deriving DecidableEq, Repr

/-- One global durable state shared by every frontend/object instance. -/
structure World where
  outbox : ConsequenceKey → Option OutboxEntry
  engine : ConsequenceKey → Option EngineReceipt

/-- Functional single-key update used by both durable indices. -/
def write {Value : Type} (store : ConsequenceKey → Option Value)
    (key : ConsequenceKey) (value : Value) : ConsequenceKey → Option Value :=
  fun query => if query = key then some value else store query

@[simp] theorem write_same {Value : Type} (store : ConsequenceKey → Option Value)
    (key : ConsequenceKey) (value : Value) : write store key value key = some value := by
  simp [write]

/-- `prepare` is the only absent-to-pending transition and performs no executor mutation. -/
structure PrepareStep (before : World) (operation : PreparedOperation) (after : World) : Prop where
  fresh : before.outbox operation.key = none
  outbox : after.outbox = write before.outbox operation.key (.prepared operation)
  engine : after.engine = before.engine

/-- The executor may commit only an already-prepared operation under a globally fresh key.  The
outbox deliberately remains prepared until a separate observation/landing write. -/
structure EngineCommitStep (before : World) (operation : PreparedOperation)
    (receipt : EngineReceipt) (after : World) : Prop where
  prepared : before.outbox operation.key = some (.prepared operation)
  fresh : before.engine operation.key = none
  receiptBinds : receipt.Binds operation
  outbox : after.outbox = before.outbox
  engine : after.engine = write before.engine operation.key receipt

/-- Recovery observes the already-committed receipt and advances only the outbox.  There is no
executor-dispatch premise or mutation in this transition. -/
structure LandStep (before : World) (operation : PreparedOperation)
    (receipt : EngineReceipt) (after : World) : Prop where
  prepared : before.outbox operation.key = some (.prepared operation)
  committed : before.engine operation.key = some receipt
  receiptBinds : receipt.Binds operation
  outbox : after.outbox = write before.outbox operation.key (.landed operation receipt)
  engine : after.engine = before.engine

/-- Canonical landing result used by crash-recovery existence proofs. -/
def landResult (before : World) (operation : PreparedOperation)
    (receipt : EngineReceipt) : World :=
  { outbox := write before.outbox operation.key (.landed operation receipt)
    engine := before.engine }

/-! ## 4. Prepare-before-dispatch and no caller-selected reward -/

/-- Preparing an outbox entry cannot execute a game effect. -/
theorem preparation_does_not_dispatch
    {before after : World} {operation : PreparedOperation}
    (step : PrepareStep before operation after) : after.engine = before.engine :=
  step.engine

/-- Every executor commit has a durable prepared predecessor under the exact same global key. -/
theorem engine_commit_requires_prepared
    {before after : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : EngineCommitStep before operation receipt after) :
    before.outbox operation.key = some (.prepared operation) :=
  step.prepared

/-- An absent outbox entry cannot dispatch directly. -/
theorem absent_outbox_cannot_commit
    {before : World} {operation : PreparedOperation}
    (absent : before.outbox operation.key = none) :
    ¬ ∃ receipt after, EngineCommitStep before operation receipt after := by
  rintro ⟨receipt, after, step⟩
  have prepared := step.prepared
  rw [absent] at prepared
  contradiction

/-- A receipt that substitutes a caller-selected reward amount cannot bind the prepared operation. -/
theorem caller_selected_reward_refused
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation)
    (receipt : EngineReceipt)
    (wrong : receipt.effect.rewardAmount ≠ deployment.policy.rewardAmount) :
    ¬ receipt.Binds operation := by
  intro binds
  rcases prepared_effect_is_deployment_owned deployment settlement accepted request operation
    prepared with ⟨target, _, effect⟩
  apply wrong
  rw [binds.2.1, effect]
  rfl

/-- A receipt routed to any cell other than the deployment roster's selected winner target cannot
bind the prepared operation. -/
theorem caller_selected_target_refused
    (deployment : DeploymentConfig) (settlement : VerifiedSettlement)
    (accepted : DeploymentAccepts deployment settlement) (request : PlayerRequest)
    (operation : PreparedOperation)
    (prepared : prepare deployment settlement accepted request = some operation)
    (receipt : EngineReceipt)
    (wrong : deployment.policy.selectTarget settlement.winner ≠
      some receipt.effect.target) :
    ¬ receipt.Binds operation := by
  intro binds
  apply wrong
  rw [binds.2.1]
  exact prepared_target_is_roster_selected deployment settlement accepted request operation prepared

/-- The executor's durable record after commit contains the exact bound receipt while the outbox
still says prepared.  This is the recoverable crash window. -/
theorem engine_commit_creates_recoverable_window
    {before after : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : EngineCommitStep before operation receipt after) :
    after.outbox operation.key = some (.prepared operation) ∧
    after.engine operation.key = some receipt := by
  constructor
  · rw [step.outbox]
    exact step.prepared
  · rw [step.engine]
    exact write_same before.engine operation.key receipt

/-! ## 5. Crash/retry exactly-once laws -/

/-- Once the executor owns the global key, another commit of the same operation cannot start. -/
theorem engine_commit_cannot_repeat
    {before committed : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (first : EngineCommitStep before operation receipt committed) :
    ¬ ∃ secondReceipt final,
      EngineCommitStep committed operation secondReceipt final := by
  intro second
  rcases second with ⟨secondReceipt, final, again⟩
  have present : committed.engine operation.key = some receipt :=
    (engine_commit_creates_recoverable_window first).2
  have fresh := again.fresh
  rw [present] at fresh
  contradiction

/-- The receipt in the executor's global key slot is unique. -/
theorem committed_receipt_unique
    {world : World} {operation : PreparedOperation} {left right : EngineReceipt}
    (hleft : world.engine operation.key = some left)
    (hright : world.engine operation.key = some right) : left = right := by
  rw [hleft] at hright
  exact Option.some.inj hright

/-- Any successful executor commit can be landed by observation without another game turn. -/
theorem committed_effect_can_land
    {before committed : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : EngineCommitStep before operation receipt committed) :
    LandStep committed operation receipt (landResult committed operation receipt) := by
  refine ⟨(engine_commit_creates_recoverable_window step).1,
    (engine_commit_creates_recoverable_window step).2, step.receiptBinds, rfl, rfl⟩

/-- Landing preserves the executor record, so it cannot manufacture or repeat an effect. -/
theorem landing_does_not_dispatch
    {before after : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : LandStep before operation receipt after) : after.engine = before.engine :=
  step.engine

/-- A crash is lossless at this semantic durable boundary. -/
def CrashesTo (before after : World) : Prop := after = before

/-- **Crash/retry apex.** If the host crashes after the executor commit but before marking the
outbox landed, retry cannot execute a second effect and can always recover by observing the one
committed receipt. -/
theorem crash_retry_cannot_double_land
    {before committed crashed : World} {operation : PreparedOperation}
    {receipt : EngineReceipt}
    (commit : EngineCommitStep before operation receipt committed)
    (crash : CrashesTo committed crashed) :
    (¬ ∃ secondReceipt final,
      EngineCommitStep crashed operation secondReceipt final) ∧
    ∃ landed, LandStep crashed operation receipt landed := by
  subst crashed
  refine ⟨engine_commit_cannot_repeat commit, ?_⟩
  exact ⟨landResult committed operation receipt, committed_effect_can_land commit⟩

/-- After recovery marks the outbox landed, the same global key remains present in the executor
ledger and cannot be dispatched again. -/
theorem landed_state_cannot_dispatch_again
    {before landed : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : LandStep before operation receipt landed) :
    ¬ ∃ secondReceipt final,
      EngineCommitStep landed operation secondReceipt final := by
  intro second
  rcases second with ⟨secondReceipt, final, again⟩
  have present : landed.engine operation.key = some receipt := by
    rw [step.engine]
    exact step.committed
  have fresh := again.fresh
  rw [present] at fresh
  contradiction

/-- The prepared-to-landed transition itself is one-shot: a landed entry cannot be observed as a
second prepared entry and landed again. -/
theorem land_step_cannot_repeat
    {before landed : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : LandStep before operation receipt landed) :
    ¬ ∃ secondReceipt final,
      LandStep landed operation secondReceipt final := by
  intro second
  rcases second with ⟨secondReceipt, final, again⟩
  have alreadyLanded : landed.outbox operation.key =
      some (.landed operation receipt) := by
    rw [step.outbox]
    exact write_same before.outbox operation.key (.landed operation receipt)
  have prepared := again.prepared
  rw [alreadyLanded] at prepared
  have impossible : OutboxEntry.landed operation receipt =
      OutboxEntry.prepared operation := Option.some.inj prepared
  cases impossible

/-- A landed outbox names the exact operation and receipt observed in the executor ledger. -/
theorem land_step_records_exact_receipt
    {before after : World} {operation : PreparedOperation} {receipt : EngineReceipt}
    (step : LandStep before operation receipt after) :
    after.outbox operation.key = some (.landed operation receipt) ∧
    after.engine operation.key = some receipt := by
  constructor
  · rw [step.outbox]
    exact write_same before.outbox operation.key (.landed operation receipt)
  · rw [step.engine]
    exact step.committed

/-! ## 6. Axiom hygiene -/

#assert_not_depends_on Market.DarkBazaarConsequenceOutbox.consequenceKey [
  Market.DarkBazaarConsequenceOutbox.PlayerRequest]

#assert_all_clean [
  Market.DarkBazaarConsequenceOutbox.selectTargetFromRoster_sound,
  Market.DarkBazaarConsequenceOutbox.prepared_key_is_deployment_owned,
  Market.DarkBazaarConsequenceOutbox.prepared_effect_is_deployment_owned,
  Market.DarkBazaarConsequenceOutbox.prepared_target_is_roster_selected,
  Market.DarkBazaarConsequenceOutbox.prepared_target_is_roster_member,
  Market.DarkBazaarConsequenceOutbox.unpinned_winner_cannot_prepare,
  Market.DarkBazaarConsequenceOutbox.caller_request_cannot_change_authority,
  Market.DarkBazaarConsequenceOutbox.substituted_market_refused,
  Market.DarkBazaarConsequenceOutbox.different_market_has_different_key,
  Market.DarkBazaarConsequenceOutbox.different_policy_has_different_key,
  Market.DarkBazaarConsequenceOutbox.preparation_does_not_dispatch,
  Market.DarkBazaarConsequenceOutbox.engine_commit_requires_prepared,
  Market.DarkBazaarConsequenceOutbox.absent_outbox_cannot_commit,
  Market.DarkBazaarConsequenceOutbox.caller_selected_reward_refused,
  Market.DarkBazaarConsequenceOutbox.caller_selected_target_refused,
  Market.DarkBazaarConsequenceOutbox.engine_commit_creates_recoverable_window,
  Market.DarkBazaarConsequenceOutbox.engine_commit_cannot_repeat,
  Market.DarkBazaarConsequenceOutbox.committed_receipt_unique,
  Market.DarkBazaarConsequenceOutbox.committed_effect_can_land,
  Market.DarkBazaarConsequenceOutbox.landing_does_not_dispatch,
  Market.DarkBazaarConsequenceOutbox.crash_retry_cannot_double_land,
  Market.DarkBazaarConsequenceOutbox.landed_state_cannot_dispatch_again,
  Market.DarkBazaarConsequenceOutbox.land_step_cannot_repeat,
  Market.DarkBazaarConsequenceOutbox.land_step_records_exact_receipt]

end Market.DarkBazaarConsequenceOutbox
