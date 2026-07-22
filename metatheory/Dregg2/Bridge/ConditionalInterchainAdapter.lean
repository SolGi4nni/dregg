/-
# Dregg2.Bridge.ConditionalInterchainAdapter

The existing verified `InterchainAdapterDecision` answers *whether the foreign
evidence reaches consensus*.  That answer is necessary but not sufficient to
authorize a local credit: the same valid evidence must also be bound to the
local federation, nullifier, recipient, and amount that the executor is about
to use.

This module formalizes that conditional boundary.  It mirrors
`bridge/src/conditional_interchain_adapter.rs`, where identities are full
32-byte values; `Nat` is used here because only zero/default rejection and exact
equality matter.  No compression or field encoding is hidden in this model.

Attack model:

* recipient substitution: a proof for A is assembled into a request for B;
* cross-federation replay: a proof addressed to X is credited on Y;
* event splicing: finality for one nullifier/amount is paired with another;
* Nomad defaults: zero nullifier or zero local destination maps to acceptance;
* check/use drift: the implementation checks one binding and consumes another.

`build?` extracts one immutable `Binding` value and constructs its request only
when every condition holds.  The top iff theorem gives arbitrary-input
soundness and constructive completeness.  Concrete falsifiers exercise every
negative polarity, including the recipient-substitution behavior of the old
caller-recipient surface.

Maturity: this is the proved decision/reference object and the Rust wrapper is
executable with focused tests.  The unsafe caller-recipient builder has been
removed from the broad `InterchainAdapter` trait, and its current production
consumer routes through this conditional boundary.
-/

import Dregg2.Bridge.InterchainAdapterDecision
import Dregg2.Tactics

namespace Dregg2.Bridge.ConditionalInterchainAdapter

open Dregg2.Bridge.InterchainAdapterDecision

set_option autoImplicit false

structure Binding where
  nullifier : Nat
  recipient : Nat
  destination : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure ExpectedCredit where
  nullifier : Nat
  recipient : Nat
  amount : Nat
  deriving DecidableEq, Repr

structure MintRequest where
  nullifier : Nat
  recipient : Nat
  amount : Nat
  consensusVerified : Bool
  deriving DecidableEq, Repr

/-- The complete conditional admission relation.  The foreign trust decision is
the already-verified core; all remaining conjuncts are exact statement binding. -/
def Admits (rung : TrustRung) (localDestination : Nat)
    (binding : Binding) (expected : ExpectedCredit) : Prop :=
  reachedConsensusCore rung = true /\
    localDestination ≠ 0 /\
    binding.nullifier ≠ 0 /\
    binding.destination = localDestination /\
    binding.nullifier = expected.nullifier /\
    binding.recipient = expected.recipient /\
    binding.amount = expected.amount

instance instDecidableAdmits (rung : TrustRung) (localDestination : Nat)
    (binding : Binding) (expected : ExpectedCredit) :
    Decidable (Admits rung localDestination binding expected) := by
  unfold Admits
  infer_instance

/-- The request contains only values from the checked immutable binding. -/
def boundRequest (binding : Binding) : MintRequest :=
  { nullifier := binding.nullifier
  , recipient := binding.recipient
  , amount := binding.amount
  , consensusVerified := true }

/-- Fail-closed conditional builder.  `none` is the default for every missing
or mismatched condition. -/
def build? (rung : TrustRung) (localDestination : Nat)
    (binding : Binding) (expected : ExpectedCredit) : Option MintRequest :=
  if Admits rung localDestination binding expected then
    some (boundRequest binding)
  else none

/-- Exact soundness and completeness for arbitrary inputs. -/
theorem build_some_iff (rung : TrustRung) (localDestination : Nat)
    (binding : Binding) (expected : ExpectedCredit) (request : MintRequest) :
    build? rung localDestination binding expected = some request ↔
      Admits rung localDestination binding expected /\
        request = boundRequest binding := by
  by_cases h : Admits rung localDestination binding expected
  · simp [build?, h, eq_comm]
  · simp [build?, h]

theorem build_isSome_iff (rung : TrustRung) (localDestination : Nat)
    (binding : Binding) (expected : ExpectedCredit) :
    (build? rung localDestination binding expected).isSome = true ↔
      Admits rung localDestination binding expected := by
  unfold build?
  split <;> simp_all

/-- Any admitted request is exactly bound to the proof-carried statement. -/
theorem accepted_request_binds_statement
    {rung : TrustRung} {localDestination : Nat}
    {binding : Binding} {expected : ExpectedCredit} {request : MintRequest}
    (h : build? rung localDestination binding expected = some request) :
    request.nullifier = binding.nullifier /\
      request.recipient = binding.recipient /\
      request.amount = binding.amount /\
      request.consensusVerified = true /\
      binding.destination = localDestination /\
      binding.nullifier = expected.nullifier /\
      binding.recipient = expected.recipient /\
      binding.amount = expected.amount := by
  obtain ⟨hadmit, rfl⟩ :=
    (build_some_iff rung localDestination binding expected request).mp h
  exact ⟨rfl, rfl, rfl, rfl, hadmit.2.2.2.1, hadmit.2.2.2.2.1,
    hadmit.2.2.2.2.2.1, hadmit.2.2.2.2.2.2⟩

/-! ## Executable wire twin

Ten integer words mirror the Rust equality boundary:
`tag payload local bNull bRecipient bDestination bAmount eNull eRecipient eAmount`.
Unknown/malformed trust tags fail in `reachedConsensusWire`; malformed arity
fails in the FFI wrapper. -/

def conditionalWire (tag payload localDestination : Int)
    (bindingNullifier bindingRecipient bindingDestination bindingAmount : Int)
    (expectedNullifier expectedRecipient expectedAmount : Int) : Bool :=
  reachedConsensusWire tag payload &&
    localDestination != 0 &&
    bindingNullifier != 0 &&
    bindingDestination == localDestination &&
    bindingNullifier == expectedNullifier &&
    bindingRecipient == expectedRecipient &&
    bindingAmount == expectedAmount

/-- The exact propositional meaning of the executable ten-word boundary. -/
def ConditionalWireSpec (tag payload localDestination : Int)
    (bindingNullifier bindingRecipient bindingDestination bindingAmount : Int)
    (expectedNullifier expectedRecipient expectedAmount : Int) : Prop :=
  reachedConsensusWire tag payload = true /\
    localDestination ≠ 0 /\
    bindingNullifier ≠ 0 /\
    bindingDestination = localDestination /\
    bindingNullifier = expectedNullifier /\
    bindingRecipient = expectedRecipient /\
    bindingAmount = expectedAmount

/-- Arbitrary-wire soundness and completeness: the exported decision accepts
exactly the trust-and-statement-binding relation, including both polarities. -/
theorem conditionalWire_correct (tag payload localDestination : Int)
    (bindingNullifier bindingRecipient bindingDestination bindingAmount : Int)
    (expectedNullifier expectedRecipient expectedAmount : Int) :
    conditionalWire tag payload localDestination bindingNullifier bindingRecipient
        bindingDestination bindingAmount expectedNullifier expectedRecipient expectedAmount = true ↔
      ConditionalWireSpec tag payload localDestination bindingNullifier bindingRecipient
        bindingDestination bindingAmount expectedNullifier expectedRecipient expectedAmount := by
  simp [conditionalWire, ConditionalWireSpec, and_assoc]

@[export dregg_interchain_conditional_admit]
def conditionalFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toInt? with
  | [tag, payload, localDestination, bindingNullifier, bindingRecipient,
      bindingDestination, bindingAmount, expectedNullifier, expectedRecipient,
      expectedAmount] =>
      if conditionalWire tag payload localDestination bindingNullifier
          bindingRecipient bindingDestination bindingAmount expectedNullifier
          expectedRecipient expectedAmount then "1" else "0"
  | _ => "0"

#guard conditionalFFI "0 0 3 11 22 3 73 11 22 73" = "1"
#guard conditionalFFI "3 0 3 11 22 3 73 11 22 73" = "0" -- RPC
#guard conditionalFFI "0 0 3 11 22 3 73 11 44 73" = "0" -- recipient substitution
#guard conditionalFFI "0 0 3 11 22 9 73 11 22 73" = "0" -- wrong destination
#guard conditionalFFI "0 0 0 11 22 0 73 11 22 73" = "0" -- zero local destination
#guard conditionalFFI "0 0 3 0 22 3 73 0 22 73" = "0" -- zero nullifier
#guard conditionalFFI "garbage" = "0"

/-! ## Concrete attack/refusal witnesses -/

def honestBinding : Binding := ⟨11, 22, 3, 73⟩
def honestExpected : ExpectedCredit := ⟨11, 22, 73⟩
def substitutedRecipient : ExpectedCredit := ⟨11, 44, 73⟩
def wrongDestination : Binding := ⟨11, 22, 9, 73⟩
def wrongNullifier : ExpectedCredit := ⟨12, 22, 73⟩
def wrongAmount : ExpectedCredit := ⟨11, 22, 74⟩

/-- The old generic shape copies a caller-supplied recipient without relating it
to the binding.  This theorem is the formal recipient-substitution falsifier. -/
def oldCallerRecipientBuild (rung : TrustRung) (binding : Binding)
    (callerRecipient : Nat) : Option MintRequest :=
  if reachedConsensusCore rung then
    some (⟨binding.nullifier, callerRecipient, binding.amount, true⟩ : MintRequest)
  else none

theorem old_surface_exhibits_recipient_substitution :
    oldCallerRecipientBuild .proof honestBinding 44 =
      some (⟨11, 44, 73, true⟩ : MintRequest) := rfl

theorem honest_statement_admitted :
    build? .proof 3 honestBinding honestExpected = some (boundRequest honestBinding) := by
  decide

theorem recipient_substitution_refused :
    build? .proof 3 honestBinding substitutedRecipient = none := by decide

theorem cross_federation_replay_refused :
    build? .proof 3 wrongDestination honestExpected = none := by decide

theorem event_nullifier_splice_refused :
    build? .proof 3 honestBinding wrongNullifier = none := by decide

theorem event_amount_splice_refused :
    build? .proof 3 honestBinding wrongAmount = none := by decide

theorem zero_local_destination_refused :
    build? .proof 0 honestBinding honestExpected = none := by decide

theorem zero_nullifier_refused :
    build? .proof 3 ⟨0, 22, 3, 73⟩ ⟨0, 22, 73⟩ = none := by decide

theorem rpc_refused_even_when_statement_matches :
    build? .rpc 3 honestBinding honestExpected = none := by decide

theorem watchtower_fraud_refused_even_when_statement_matches :
    build? (.optimisticWatchtower false) 3 honestBinding honestExpected = none := by decide

theorem committee_noquorum_refused_even_when_statement_matches :
    build? (.committee false) 3 honestBinding honestExpected = none := by decide

#assert_all_clean [
  build_some_iff,
  build_isSome_iff,
  accepted_request_binds_statement,
  conditionalWire_correct,
  old_surface_exhibits_recipient_substitution,
  honest_statement_admitted,
  recipient_substitution_refused,
  cross_federation_replay_refused,
  event_nullifier_splice_refused,
  event_amount_splice_refused,
  zero_local_destination_refused,
  zero_nullifier_refused,
  rpc_refused_even_when_statement_matches,
  watchtower_fraud_refused_even_when_statement_matches,
  committee_noquorum_refused_even_when_statement_matches
]

end Dregg2.Bridge.ConditionalInterchainAdapter
