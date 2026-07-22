/-
# Market.PrivateClearingGameConsequence — a private clear fires one exact game effect

`dreggnet-market/private_clearing_consequence.rs` consumes a verified private
Dark Bazaar settlement in a game.  Its replay key is derived from the complete
source statement, winner, settlement turn, deployment-selected target, and
consequence tag.  The target engine returns one real committed turn receipt.

This module states the semantic law behind that boundary.  It deliberately
keeps two operational facts as explicit interfaces:

* `DurableReplay` says what it means for the host to durably record a consumed
  consequence key, including record idempotence; and
* `GameCommitAuthority.Committed` / `CommittedObservation` say that the target
  engine durably exposes the exact already-committed game receipt after restart.

Lean does not infer either fact from a process-local set, a file write, or a
hash.  Subject to those assumptions, the theorems prove that an accepted game
effect is bound to the exact settlement source, complete private statement,
winner, settlement turn, target, and tag; that it is one-shot; and that crash
recovery records an already-observed commit without dispatching a second turn.

The replay identity below is the complete semantic tuple rather than its BLAKE3
compression.  Collision resistance of the deployed compression remains a
cryptographic refinement premise, while no field is lost in this law.
-/
import Market.DarkBazaarAttestation
import Dregg2.Tactics

namespace Market.PrivateClearingGameConsequence

open Market.DarkBazaarAttestation
open Market.MpcClearingSecurity
open Dregg2.Intent.Ring

set_option autoImplicit false

abbrev ActorId := Nat
abbrev GameTarget := Nat
abbrev ConsequenceTag := Nat
abbrev TurnId := Nat

/-! ## 1. Exact verified settlement and complete consequence identity. -/

/-- Complete public statement accepted by the private clearing verifier. -/
structure PrivateClearingStatement (C : OrderCommitmentCarrier) where
  sourceRoot : C.Digest
  session : Nat
  rule : Nat
  output : CrossingLeakage

/-- Relying-party policy for the private result.  `winnerOf` is the authoritative
winner selection used by the settled market, not a caller-supplied identity. -/
structure SettlementAuthority (C : OrderCommitmentCarrier) where
  expectedSession : Nat
  expectedRule : Nat
  winnerOf : OrderSourcePayload → CrossingLeakage → ActorId

/-- One exact private settlement ready to authorize a game consequence. -/
structure VerifiedPrivateSettlement (C : OrderCommitmentCarrier)
    (authority : SettlementAuthority C) where
  source : CommittedOrderSource C
  statement : PrivateClearingStatement C
  receipt : SettlementReceipt C
  winner : ActorId
  settlementTurn : TurnId
  sourceBound : statement.sourceRoot = source.root
  sessionBound : statement.session = authority.expectedSession
  ruleBound : statement.rule = authority.expectedRule
  receiptExact : ExactSettlementReceipt source statement.output receipt
  winnerBound : winner = authority.winnerOf source.payload statement.output
  settlementTurnNonzero : settlementTurn ≠ 0
  pricePositive : 0 < statement.output.pStar
  volumePositive : 0 < statement.output.vStar

/-- Deployment-owned routing.  A target may expose multiple separately replayed
effects by assigning distinct tags. -/
structure ConsequencePolicy where
  target : GameTarget
  tag : ConsequenceTag

/-- Lossless pre-hash replay identity.  This is exactly the tuple which the Rust
gate domain-separates and hashes. -/
structure ConsequenceKey (C : OrderCommitmentCarrier) where
  sourceRoot : C.Digest
  statement : PrivateClearingStatement C
  winner : ActorId
  settlementTurn : TurnId
  target : GameTarget
  tag : ConsequenceTag

def consequenceKey {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy) : ConsequenceKey C :=
  { sourceRoot := settlement.source.root
    statement := settlement.statement
    winner := settlement.winner
    settlementTurn := settlement.settlementTurn
    target := policy.target
    tag := policy.tag }

/-! ## 2. Target-engine receipt and exact binding. -/

/-- Public receipt returned by the consuming game engine.  The routing fields
are repeated so a host cannot silently dispatch a proof under a different
winner, target, or semantic effect. -/
structure GameReceipt (C : OrderCommitmentCarrier) where
  sourceRoot : C.Digest
  statement : PrivateClearingStatement C
  winner : ActorId
  settlementTurn : TurnId
  target : GameTarget
  tag : ConsequenceTag
  gameTurn : TurnId
  actionCount : Nat
  preState : Nat
  postState : Nat

/-- Exact receipt shape and routing weld. -/
def GameReceipt.Binds {C : OrderCommitmentCarrier}
    (receipt : GameReceipt C) (key : ConsequenceKey C) : Prop :=
  receipt.sourceRoot = key.sourceRoot ∧
  receipt.statement = key.statement ∧
  receipt.winner = key.winner ∧
  receipt.settlementTurn = key.settlementTurn ∧
  receipt.target = key.target ∧
  receipt.tag = key.tag ∧
  receipt.gameTurn ≠ 0 ∧
  0 < receipt.actionCount ∧
  receipt.preState ≠ receipt.postState

/-- Target-engine operational authority.  A production instance means that the
receipt is present in the engine's durable committed receipt/state index. -/
structure GameCommitAuthority (C : OrderCommitmentCarrier) where
  Committed : GameReceipt C → Prop

/-! ## 3. Explicit durable replay interface. -/

/-- Abstract durable one-shot store.  These laws are assumptions about the
host's persistence implementation, not consequences of the pure settlement
proof. -/
structure DurableReplay (Key : Type) where
  Store : Type
  consumed : Store → Key → Prop
  record : Store → Key → Store
  recordConsumes : ∀ state key, consumed (record state key) key
  recordPreserves : ∀ state recorded other,
    consumed state other → consumed (record state recorded) other
  recordIdempotent : ∀ state key,
    record (record state key) key = record state key

/-- Successful normal execution: the key was fresh, the target returned the
exact bound receipt, that receipt is authoritatively committed, and the durable
replay record advanced. -/
def Dispatches {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    (game : GameCommitAuthority C)
    (durable : DurableReplay (ConsequenceKey C))
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy)
    (before : durable.Store) (receipt : GameReceipt C)
    (after : durable.Store) : Prop :=
  let key := consequenceKey settlement policy
  ¬ durable.consumed before key ∧
  receipt.Binds key ∧
  game.Committed receipt ∧
  after = durable.record before key

/-- Durable observation used only in the post-game/pre-replay crash window.
Its proof fields are the engine-specific recovery assumption. -/
structure CommittedObservation {C : OrderCommitmentCarrier}
    (game : GameCommitAuthority C) (key : ConsequenceKey C) where
  receipt : GameReceipt C
  binding : receipt.Binds key
  committed : game.Committed receipt

/-- Recovery never dispatches.  It validates an exact already-committed
observation and performs only the missing durable replay write. -/
def Recovers {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    (durable : DurableReplay (ConsequenceKey C))
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy)
    (before : durable.Store)
    (_observation : CommittedObservation game (consequenceKey settlement policy))
    (after : durable.Store) : Prop :=
  let key := consequenceKey settlement policy
  ¬ durable.consumed before key ∧
  after = durable.record before key

/-- The recovery API contains no dispatch operation. -/
def recoveryDispatchCount : Nat := 0

/-! ## 4. Exact game-facing consequence. -/

/-- An accepted consequence names the exact authorized settlement tuple and
the underlying exact settlement still executes the canonical fhEgg transition. -/
theorem dispatched_consequence_binds_exact_settlement_and_target
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    {settlement : VerifiedPrivateSettlement C authority}
    {policy : ConsequencePolicy}
    {before after : durable.Store} {gameReceipt : GameReceipt C}
    (hdispatch : Dispatches game durable settlement policy before gameReceipt after) :
    gameReceipt.sourceRoot = C.commit settlement.source.payload ∧
    gameReceipt.statement = settlement.statement ∧
    gameReceipt.winner =
      authority.winnerOf settlement.source.payload settlement.statement.output ∧
    gameReceipt.settlementTurn = settlement.settlementTurn ∧
    gameReceipt.target = policy.target ∧
    gameReceipt.tag = policy.tag ∧
    game.Committed gameReceipt ∧
    settleRing settlement.receipt.pre
      (settlementsOf settlement.receipt.nodes) = some settlement.receipt.post := by
  rcases hdispatch with
    ⟨_, hbind, hcommitted, _⟩
  rcases hbind with
    ⟨hsource, hstatement, hwinner, hturn, htarget, htag, _, _, _⟩
  refine ⟨hsource.trans settlement.source.root_eq, hstatement,
    hwinner.trans settlement.winnerBound, hturn, htarget, htag, hcommitted, ?_⟩
  exact exact_settlement_receipt_settles settlement.receiptExact
    settlement.pricePositive settlement.volumePositive

/-- A receipt with a substituted complete private statement cannot cross the
game gate. -/
theorem substituted_statement_cannot_dispatch
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy) (before after : durable.Store)
    (receipt : GameReceipt C)
    (hwrong : receipt.statement ≠ settlement.statement) :
    ¬ Dispatches game durable settlement policy before receipt after := by
  intro hdispatch
  rcases hdispatch with ⟨_, hbind, _, _⟩
  exact hwrong hbind.2.1

/-- A receipt with a substituted winner cannot cross the game gate. -/
theorem substituted_winner_cannot_dispatch
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy) (before after : durable.Store)
    (receipt : GameReceipt C)
    (hwrong : receipt.winner ≠ settlement.winner) :
    ¬ Dispatches game durable settlement policy before receipt after := by
  intro hdispatch
  rcases hdispatch with ⟨_, hbind, _, _⟩
  exact hwrong hbind.2.2.1

/-- A receipt with a substituted target cannot cross the game gate. -/
theorem substituted_target_cannot_dispatch
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy) (before after : durable.Store)
    (receipt : GameReceipt C)
    (hwrong : receipt.target ≠ policy.target) :
    ¬ Dispatches game durable settlement policy before receipt after := by
  intro hdispatch
  rcases hdispatch with ⟨_, hbind, _, _⟩
  exact hwrong hbind.2.2.2.2.1

/-- A settlement-turn substitution cannot create a new replay identity for the
same private result. -/
theorem substituted_settlement_turn_cannot_dispatch
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    (settlement : VerifiedPrivateSettlement C authority)
    (policy : ConsequencePolicy) (before after : durable.Store)
    (receipt : GameReceipt C)
    (hwrong : receipt.settlementTurn ≠ settlement.settlementTurn) :
    ¬ Dispatches game durable settlement policy before receipt after := by
  intro hdispatch
  rcases hdispatch with ⟨_, hbind, _, _⟩
  exact hwrong hbind.2.2.2.1

/-! ## 5. One-shot and crash-recovery laws. -/

/-- A successful dispatch durably consumes its complete key.  No second game
receipt can dispatch from the resulting store under that same settlement and
target policy. -/
theorem successful_dispatch_is_one_shot
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    {settlement : VerifiedPrivateSettlement C authority}
    {policy : ConsequencePolicy}
    {before after : durable.Store} {receipt : GameReceipt C}
    (hdispatch : Dispatches game durable settlement policy before receipt after) :
    durable.consumed after (consequenceKey settlement policy) ∧
    ∀ (secondReceipt : GameReceipt C) (final : durable.Store),
      ¬ Dispatches game durable settlement policy after secondReceipt final := by
  rcases hdispatch with ⟨_, _, _, rfl⟩
  constructor
  · exact durable.recordConsumes before (consequenceKey settlement policy)
  · intro secondReceipt final hsecond
    exact hsecond.1 <|
      durable.recordConsumes before (consequenceKey settlement policy)

/-- **Crash-recovery idempotence.**  Re-observing the exact target-specific
committed receipt performs zero game dispatches, records the missing replay key,
and is an idempotent persistence operation.  Afterwards neither normal dispatch
nor another recovery can consume the same consequence again. -/
theorem reobserving_committed_receipt_is_idempotent_and_cannot_dispatch_twice
    {C : OrderCommitmentCarrier}
    {authority : SettlementAuthority C}
    {game : GameCommitAuthority C}
    {durable : DurableReplay (ConsequenceKey C)}
    {settlement : VerifiedPrivateSettlement C authority}
    {policy : ConsequencePolicy}
    {before after : durable.Store}
    {observation : CommittedObservation game (consequenceKey settlement policy)}
    (hrecover : Recovers durable settlement policy before observation after) :
    observation.receipt.Binds (consequenceKey settlement policy) ∧
    game.Committed observation.receipt ∧
    recoveryDispatchCount = 0 ∧
    durable.consumed after (consequenceKey settlement policy) ∧
    durable.record after (consequenceKey settlement policy) = after ∧
    (∀ (receipt : GameReceipt C) (final : durable.Store),
      ¬ Dispatches game durable settlement policy after receipt final) ∧
    (∀ (final : durable.Store),
      ¬ Recovers durable settlement policy after observation final) := by
  rcases hrecover with ⟨_, rfl⟩
  have hconsumed := durable.recordConsumes before
    (consequenceKey settlement policy)
  refine ⟨observation.binding, observation.committed, rfl, hconsumed,
    durable.recordIdempotent before (consequenceKey settlement policy), ?_, ?_⟩
  · intro receipt final hdispatch
    exact hdispatch.1 hconsumed
  · intro final hrecoverAgain
    exact hrecoverAgain.1 hconsumed

/-! Structural binding must not silently acquire durability or dispatch
semantics merely because it is used by the host lifecycle. -/
#assert_not_depends_on Market.PrivateClearingGameConsequence.GameReceipt.Binds [
  Market.PrivateClearingGameConsequence.DurableReplay,
  Market.PrivateClearingGameConsequence.Dispatches,
  Market.PrivateClearingGameConsequence.Recovers]

#assert_all_clean [
  Market.PrivateClearingGameConsequence.dispatched_consequence_binds_exact_settlement_and_target,
  Market.PrivateClearingGameConsequence.substituted_statement_cannot_dispatch,
  Market.PrivateClearingGameConsequence.substituted_winner_cannot_dispatch,
  Market.PrivateClearingGameConsequence.substituted_target_cannot_dispatch,
  Market.PrivateClearingGameConsequence.substituted_settlement_turn_cannot_dispatch,
  Market.PrivateClearingGameConsequence.successful_dispatch_is_one_shot,
  Market.PrivateClearingGameConsequence.reobserving_committed_receipt_is_idempotent_and_cannot_dispatch_twice]

end Market.PrivateClearingGameConsequence
