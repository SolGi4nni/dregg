/-
# Dregg2.Circuit.CommitmentTreeWideSpend -- historical spend/root atomicity

This is the semantic authority for the live faithful-note spend admission cut.
A spend names an exact finalized height and exact faithful-eight note root; the
pair must occur in the authenticated history, not merely look canonical.  Every
revealed nullifier is fresh both against durable state and inside its carrying
turn.  Success appends all public `(nullifier, value)` records and publishes the
abstract accumulator root of precisely that successor list in the same state
transition.  Any failed tooth is state identity.

`nullifierRoot` is parameterized here because the concrete Poseidon2 heap fold
lives in the circuit/runtime correspondence.  The theorem fixes the much more
important protocol boundary: the root that is attested is the root of exactly
the records atomically persisted, never a caller-selected predecessor or a
partially written suffix.
-/
import Dregg2.Circuit.CommitmentTreeWideHistory
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Circuit.CommitmentTreeWideSpend

open Dregg2.Circuit.CommitmentTreeWideHistory

set_option autoImplicit false

/-- Public coordinates of one shielded note spend.  The private opening and
membership path remain inside the proof; the finalized height/root pair and
revealed nullifier/value are the verifier-visible statement. -/
structure Spend where
  rootHeight : Nat
  noteRoot : Root8
  nullifier : Bytes32
  value : Nat
  deriving DecidableEq

/-- The exact `(height, root)` pair is present either at the authenticated
segment anchor or as the successor of an authenticated history edge. -/
def historicalPairBool (anchor : Anchor) (records : List Record)
    (height : Nat) (root : Root8) : Bool :=
  (anchor.height == height && anchor.root == root) ||
    records.any (fun record => record.height == height && record.successor == root)

def allHistoricalPairsBool (anchor : Anchor) (records : List Record)
    (spends : List Spend) : Bool :=
  spends.all (fun spend => historicalPairBool anchor records spend.rootHeight spend.noteRoot)

abbrev NullifierRecord := Bytes32 × Nat

def spendRecords (spends : List Spend) : List NullifierRecord :=
  spends.map fun spend => (spend.nullifier, spend.value)

/-- Freshness is batch-wide: no nullifier occurs in durable state and no two
spends in the same finalized turn reuse one another. -/
def freshBatchBool (durable : List NullifierRecord) (spends : List Spend) : Bool :=
  let proposed := spends.map (·.nullifier)
  decide (proposed.Nodup ∧ ∀ nullifier ∈ proposed, nullifier ∉ durable.map Prod.fst)

structure LiveSpendImage where
  historyAnchor : Anchor
  historyRecords : List Record
  nullifiers : List NullifierRecord
  attestedNullifierRoot : Root8
  deriving DecidableEq

def successorNullifiers (image : LiveSpendImage) (spends : List Spend) : List NullifierRecord :=
  image.nullifiers ++ spendRecords spends

/-- One all-or-nothing finalized spend attempt.  `historyAuthenticated` is the
result of replaying the sealed history under the enrolled hybrid roster.
`claimedSuccessorRoot` is accepted only when it equals the accumulator fold of
the exact successor records. -/
def atomicSpendWeld (nullifierRoot : List NullifierRecord -> Root8)
    (historyAuthenticated : Bool) (image : LiveSpendImage) (spends : List Spend)
    (claimedSuccessorRoot : Root8) : LiveSpendImage :=
  if historyAuthenticated &&
      allHistoricalPairsBool image.historyAnchor image.historyRecords spends &&
      freshBatchBool image.nullifiers spends &&
      decide (claimedSuccessorRoot = nullifierRoot (successorNullifiers image spends)) then
    { image with
      nullifiers := successorNullifiers image spends
      attestedNullifierRoot := claimedSuccessorRoot }
  else image

theorem unauthenticated_history_refuses
    (nullifierRoot : List NullifierRecord -> Root8) (image : LiveSpendImage)
    (spends : List Spend) (claimed : Root8) :
    atomicSpendWeld nullifierRoot false image spends claimed = image := by
  simp [atomicSpendWeld]

theorem wrong_historical_pair_refuses
    (nullifierRoot : List NullifierRecord -> Root8) (historyAuthenticated : Bool)
    (image : LiveSpendImage) (spends : List Spend) (claimed : Root8)
    (h : allHistoricalPairsBool image.historyAnchor image.historyRecords spends = false) :
    atomicSpendWeld nullifierRoot historyAuthenticated image spends claimed = image := by
  simp [atomicSpendWeld, h]

theorem duplicate_or_replayed_nullifier_refuses
    (nullifierRoot : List NullifierRecord -> Root8) (historyAuthenticated : Bool)
    (image : LiveSpendImage) (spends : List Spend) (claimed : Root8)
    (h : freshBatchBool image.nullifiers spends = false) :
    atomicSpendWeld nullifierRoot historyAuthenticated image spends claimed = image := by
  simp [atomicSpendWeld, h]

theorem wrong_nullifier_root_refuses
    (nullifierRoot : List NullifierRecord -> Root8) (historyAuthenticated : Bool)
    (image : LiveSpendImage) (spends : List Spend) (claimed : Root8)
    (h : claimed ≠ nullifierRoot (successorNullifiers image spends)) :
    atomicSpendWeld nullifierRoot historyAuthenticated image spends claimed = image := by
  simp [atomicSpendWeld, h]

theorem atomicSpendWeld_accepts_exact_persisted_successor
    (nullifierRoot : List NullifierRecord -> Root8) (historyAuthenticated : Bool)
    (image : LiveSpendImage) (spends : List Spend) (claimed : Root8)
    (h : (historyAuthenticated &&
      allHistoricalPairsBool image.historyAnchor image.historyRecords spends &&
      freshBatchBool image.nullifiers spends &&
      decide (claimed = nullifierRoot (successorNullifiers image spends))) = true)
    (hroot : claimed = nullifierRoot (successorNullifiers image spends)) :
    let after := atomicSpendWeld nullifierRoot historyAuthenticated image spends claimed
    after.nullifiers = successorNullifiers image spends /\
      after.attestedNullifierRoot = nullifierRoot after.nullifiers := by
  cases hAuth : historyAuthenticated <;> simp [hAuth] at h
  cases hHistory : allHistoricalPairsBool image.historyAnchor image.historyRecords spends <;>
    simp [hHistory] at h
  cases hFresh : freshBatchBool image.nullifiers spends <;> simp [hFresh] at h
  simp [atomicSpendWeld, hHistory, hFresh, hroot]

#assert_axioms unauthenticated_history_refuses
#assert_axioms wrong_historical_pair_refuses
#assert_axioms duplicate_or_replayed_nullifier_refuses
#assert_axioms wrong_nullifier_root_refuses
#assert_axioms atomicSpendWeld_accepts_exact_persisted_successor

end Dregg2.Circuit.CommitmentTreeWideSpend
