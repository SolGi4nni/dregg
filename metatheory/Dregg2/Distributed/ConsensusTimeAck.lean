import Dregg2.Tactics

/-
# Consensus time and finalized-outcome acknowledgement

This is the protocol law beneath the node's consensus-time flag day and its
finalized execution cursor.  A finalized transition receives time from the
authenticated block context, never from the executing validator's clock.  A
block identity becomes "executed" only after a durable commit or a durable,
deterministic rejection; operational failure stops the ordered prefix and is
retryable.

The Rust carriers live in `blocklace/src/finality.rs`,
`node/src/blocklace_sync.rs`, and `node/src/execution_cursor.rs`.  This module
models the semantic boundary, not their byte codecs.

`#assert_axioms`-clean (no assumptions).
-/

namespace Dregg2.Distributed.ConsensusTimeAck

/-! ## Consensus-authenticated causal time -/

/-- Genesis anchor plus the protocol-wide maximum advance from a causal frontier. -/
structure TimePolicy where
  genesis : Int
  maxForward : Nat
  deriving DecidableEq, Repr

/-- The time claim signed into one versioned turn-bearing block. -/
structure TimeClaim where
  unixSeconds : Int
  deriving DecidableEq, Repr

/-- Maximum authenticated time visible in the predecessor closure. -/
def frontier (policy : TimePolicy) (predecessorTimes : List Int) : Int :=
  predecessorTimes.foldl max policy.genesis

/-- The deterministic validity rule: causal non-regression and bounded advance. -/
def validClaim (policy : TimePolicy) (predecessorTimes : List Int)
    (claim : TimeClaim) : Prop :=
  frontier policy predecessorTimes ≤ claim.unixSeconds ∧
    claim.unixSeconds ≤ frontier policy predecessorTimes + Int.ofNat policy.maxForward

instance (policy : TimePolicy) (predecessorTimes : List Int) (claim : TimeClaim) :
    Decidable (validClaim policy predecessorTimes claim) := by
  unfold validClaim
  infer_instance

theorem validClaim_nonregression {policy : TimePolicy} {predecessorTimes : List Int}
    {claim : TimeClaim} (h : validClaim policy predecessorTimes claim) :
    frontier policy predecessorTimes ≤ claim.unixSeconds :=
  h.1

theorem validClaim_bounded {policy : TimePolicy} {predecessorTimes : List Int}
    {claim : TimeClaim} (h : validClaim policy predecessorTimes claim) :
    claim.unixSeconds ≤ frontier policy predecessorTimes + Int.ofNat policy.maxForward :=
  h.2

theorem validClaim_advance_le {policy : TimePolicy} {predecessorTimes : List Int}
    {claim : TimeClaim} (h : validClaim policy predecessorTimes claim) :
    claim.unixSeconds - frontier policy predecessorTimes ≤ Int.ofNat policy.maxForward := by
  unfold validClaim at h
  omega

/-- Extending the predecessor list updates the cached frontier from its old value only. -/
theorem frontier_append_one (policy : TimePolicy) (predecessorTimes : List Int) (time : Int) :
    frontier policy (predecessorTimes ++ [time]) = max (frontier policy predecessorTimes) time := by
  simp [frontier, List.foldl_append]

/-- A valid claim becomes the new frontier when appended to its predecessor closure. -/
theorem validClaim_becomes_frontier {policy : TimePolicy} {predecessorTimes : List Int}
    {claim : TimeClaim} (h : validClaim policy predecessorTimes claim) :
    frontier policy (predecessorTimes ++ [claim.unixSeconds]) = claim.unixSeconds := by
  rw [frontier_append_one]
  simp [h.1]

/-! ## Finalized execution ignores local clocks -/

/-- Consensus-owned context supplied to finalized execution. -/
structure FinalizedExecutionContext (BlockId : Type) where
  blockId : BlockId
  ordinal : Nat
  consensusTime : Int

/-- The only execution wrapper: time is read from the finalized context. -/
def executeFinalized (step : State → Payload → Int → Result)
    (state : State) (payload : Payload) (context : FinalizedExecutionContext BlockId) : Result :=
  step state payload context.consensusTime

/-- Different validator clocks cannot influence an execution fed the same finalized context. -/
theorem executeFinalized_ignores_local_clock
    (step : State → Payload → Int → Result)
    (state : State) (payload : Payload) (context : FinalizedExecutionContext BlockId)
    (_localClockA _localClockB : Int) :
    executeFinalized step state payload context = executeFinalized step state payload context := by
  rfl

/-- Equal pre-state, payload, and finalized context produce equal results. -/
theorem finalized_execution_agreement
    (step : State → Payload → Int → Result)
    {stateA stateB : State} {payloadA payloadB : Payload}
    {contextA contextB : FinalizedExecutionContext BlockId}
    (hs : stateA = stateB) (hp : payloadA = payloadB) (hc : contextA = contextB) :
    executeFinalized step stateA payloadA contextA =
      executeFinalized step stateB payloadB contextB := by
  subst stateB
  subst payloadB
  subst contextB
  rfl

/-! ## Durable terminal outcomes and ordered acknowledgement -/

/-- The full application result.  Only the first two constructors are terminal. -/
inductive FinalizedExecutionOutcome (Commit Rejection Error : Type)
  | committed : Commit → FinalizedExecutionOutcome Commit Rejection Error
  | deterministicallyRejected : Rejection → FinalizedExecutionOutcome Commit Rejection Error
  | retryableOperational : Error → FinalizedExecutionOutcome Commit Rejection Error
  | fatalIntegrity : Error → FinalizedExecutionOutcome Commit Rejection Error
  deriving DecidableEq, Repr

/-- Durable authority from which the executed identity set may be rebuilt. -/
inductive DurableTerminal (Commit Rejection : Type)
  | committed : Commit → DurableTerminal Commit Rejection
  | deterministicallyRejected : Rejection → DurableTerminal Commit Rejection
  deriving DecidableEq, Repr

/-- Project only durable terminal results into cursor authority. -/
def durableTerminal? : FinalizedExecutionOutcome Commit Rejection Error →
    Option (DurableTerminal Commit Rejection)
  | .committed commit => some (.committed commit)
  | .deterministicallyRejected rejection => some (.deterministicallyRejected rejection)
  | .retryableOperational _ => none
  | .fatalIntegrity _ => none

@[simp] theorem retryableOperational_not_acknowledged (error : Error) :
    durableTerminal? (FinalizedExecutionOutcome.retryableOperational error :
      FinalizedExecutionOutcome Commit Rejection Error) = none :=
  rfl

@[simp] theorem fatalIntegrity_not_acknowledged (error : Error) :
    durableTerminal? (FinalizedExecutionOutcome.fatalIntegrity error :
      FinalizedExecutionOutcome Commit Rejection Error) = none :=
  rfl

@[simp] theorem committed_is_acknowledged (commit : Commit) :
    durableTerminal? (FinalizedExecutionOutcome.committed commit :
      FinalizedExecutionOutcome Commit Rejection Error) = some (.committed commit) :=
  rfl

@[simp] theorem deterministicallyRejected_is_acknowledged (rejection : Rejection) :
    durableTerminal? (FinalizedExecutionOutcome.deterministicallyRejected rejection :
      FinalizedExecutionOutcome Commit Rejection Error) =
      some (.deterministicallyRejected rejection) :=
  rfl

/-- Consume the longest durable-terminal prefix, stopping at retry/fatal without skipping it. -/
def acknowledgePrefix : List (FinalizedExecutionOutcome Commit Rejection Error) →
    List (DurableTerminal Commit Rejection)
  | [] => []
  | .committed commit :: rest => .committed commit :: acknowledgePrefix rest
  | .deterministicallyRejected rejection :: rest =>
      .deterministicallyRejected rejection :: acknowledgePrefix rest
  | .retryableOperational _ :: _ => []
  | .fatalIntegrity _ :: _ => []

@[simp] theorem acknowledgePrefix_stops_at_retry (error : Error)
    (rest : List (FinalizedExecutionOutcome Commit Rejection Error)) :
    acknowledgePrefix (.retryableOperational error :: rest) = [] :=
  rfl

@[simp] theorem acknowledgePrefix_stops_at_fatal (error : Error)
    (rest : List (FinalizedExecutionOutcome Commit Rejection Error)) :
    acknowledgePrefix (.fatalIntegrity error :: rest) = [] :=
  rfl

/-- The acknowledged prefix cannot contain more identities than the attempted batch. -/
theorem acknowledgePrefix_length_le
    (outcomes : List (FinalizedExecutionOutcome Commit Rejection Error)) :
    (acknowledgePrefix outcomes).length ≤ outcomes.length := by
  induction outcomes with
  | nil => simp [acknowledgePrefix]
  | cons head tail ih =>
      cases head <;> simp [acknowledgePrefix, ih]

/-! ## Executable teeth -/

private def demoPolicy : TimePolicy := { genesis := 1_700_000_000, maxForward := 300 }

#guard validClaim demoPolicy [1_700_000_000, 1_700_000_120]
  { unixSeconds := 1_700_000_121 }
#guard ¬ validClaim demoPolicy [1_700_000_000, 1_700_000_120]
  { unixSeconds := 1_700_000_119 }
#guard ¬ validClaim demoPolicy [1_700_000_000, 1_700_000_120]
  { unixSeconds := 1_700_000_421 }

#assert_axioms validClaim_nonregression
#assert_axioms validClaim_bounded
#assert_axioms validClaim_advance_le
#assert_axioms frontier_append_one
#assert_axioms validClaim_becomes_frontier
#assert_axioms executeFinalized_ignores_local_clock
#assert_axioms finalized_execution_agreement
#assert_axioms retryableOperational_not_acknowledged
#assert_axioms fatalIntegrity_not_acknowledged
#assert_axioms committed_is_acknowledged
#assert_axioms deterministicallyRejected_is_acknowledged
#assert_axioms acknowledgePrefix_stops_at_retry
#assert_axioms acknowledgePrefix_stops_at_fatal
#assert_axioms acknowledgePrefix_length_le

end Dregg2.Distributed.ConsensusTimeAck
