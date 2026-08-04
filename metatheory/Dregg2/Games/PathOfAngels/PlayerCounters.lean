/-
# Path of Angels — canonical finite player counters

Persistent player counters are a sorted, strictly key-ordered sparse table.  Zero
is represented only by absence, every stored value is a `PlayerCounter` (`u64` wire
range), and insertion preserves the canonical representation.  This replaces the
old infinite function-valued field with bytes a strict decoder can reproduce.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Circuit.FinKernelState
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels

open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinKernelState.SortedMap
open scoped Prod.Lex

set_option autoImplicit false

/-! ## Canonical ordering of the receipt counter namespace -/

instance : LinearOrder Digest32 :=
  LinearOrder.lift' Digest32.bytes (by
    intro left right h
    cases left
    cases right
    simp_all)

instance : LinearOrder EpochId :=
  LinearOrder.lift' EpochId.value (by
    intro left right h
    cases left
    cases right
    simp_all)

private abbrev PlayerCounterOrderKey :=
  Digest32 ×ₗ (Digest32 ×ₗ (Nat ×ₗ Digest32))

private def PlayerCounterKey.orderKey (key : PlayerCounterKey) : PlayerCounterOrderKey :=
  toLex (key.federationId,
    toLex (key.contentSession, toLex (key.contentEpoch.value, key.playerKey)))

instance : LinearOrder PlayerCounterKey :=
  LinearOrder.lift' PlayerCounterKey.orderKey (by
    rintro ⟨leftFederation, leftSession, ⟨leftEpoch⟩, leftPlayer⟩
      ⟨rightFederation, rightSession, ⟨rightEpoch⟩, rightPlayer⟩ h
    simp_all [PlayerCounterKey.orderKey])

/-! ## Sparse sorted table -/

/-- A canonical table: keys are strictly sorted by their complete domain identity,
and the absent entry is the unique representation of counter zero. -/
structure PlayerCounterTable where
  toMap : CanonMap PlayerCounterKey PlayerCounter 0

namespace PlayerCounterTable

def empty : PlayerCounterTable where
  toMap := CanonMap.empty

def lookup (table : PlayerCounterTable) (key : PlayerCounterKey) : PlayerCounter :=
  table.toMap.get key

/-- The exact canonical wire rows.  No hash-map enumeration or function oracle is
involved: these are already strictly key-sorted. -/
def rows (table : PlayerCounterTable) : List (PlayerCounterKey × PlayerCounter) :=
  table.toMap.toMap.entries

theorem rows_sorted (table : PlayerCounterTable) :
    ((table.rows.map Prod.fst).Pairwise (· < ·)) :=
  table.toMap.toMap.sortedKeys

theorem rows_no_zero (table : PlayerCounterTable) :
    ∀ row ∈ table.rows, row.2 ≠ (0 : PlayerCounter) :=
  table.toMap.canon

@[simp] theorem lookup_empty (key : PlayerCounterKey) : empty.lookup key = 0 := rfl

/-- Strict wire decoder: the supplied rows themselves must already be canonical.
It never sorts, deduplicates, or drops an explicit zero on the caller's behalf. -/
def ofRows? (wireRows : List (PlayerCounterKey × PlayerCounter)) : Option PlayerCounterTable :=
  if hsorted : (wireRows.map Prod.fst).Pairwise (· < ·) then
    if hnonzero : ∀ row ∈ wireRows, row.2 ≠ (0 : PlayerCounter) then
      some { toMap := { toMap := ⟨wireRows, hsorted⟩, canon := hnonzero } }
    else none
  else none

theorem ofRows_rows_exact {wireRows : List (PlayerCounterKey × PlayerCounter)}
    {table : PlayerCounterTable} (h : ofRows? wireRows = some table) : table.rows = wireRows := by
  simp only [ofRows?] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with heq
  rw [← heq]
  rfl

theorem ofRows_refuses_unsorted (wireRows : List (PlayerCounterKey × PlayerCounter))
    (h : ¬(wireRows.map Prod.fst).Pairwise (· < ·)) : ofRows? wireRows = none := by
  simp [ofRows?, h]

theorem ofRows_refuses_zero (wireRows : List (PlayerCounterKey × PlayerCounter))
    (hsorted : (wireRows.map Prod.fst).Pairwise (· < ·))
    (hzero : ∃ row ∈ wireRows, row.2 = (0 : PlayerCounter)) : ofRows? wireRows = none := by
  unfold ofRows?
  split
  · split
    · rename_i hnonzero
      exact (by
        obtain ⟨row, hrow, hz⟩ := hzero
        exact (hnonzero row hrow hz).elim)
    · rfl
  · contradiction

theorem ofRows_roundtrip (table : PlayerCounterTable) : ofRows? table.rows = some table := by
  unfold ofRows?
  split
  · split
    · congr 1
    · rename_i hnonzero
      exact (hnonzero table.rows_no_zero).elim
  · rename_i hsorted
    exact (hsorted table.rows_sorted).elim

private theorem insertList_preserves_no_zero (key : PlayerCounterKey)
    (value : PlayerCounter) (valueNonzero : value ≠ 0) :
    ∀ entries : List (PlayerCounterKey × PlayerCounter),
      (∀ row ∈ entries, row.2 ≠ (0 : PlayerCounter)) →
      ∀ row ∈ SortedMap.insertList key value entries, row.2 ≠ (0 : PlayerCounter)
  | [], _ => by
      intro row hrow
      simp only [SortedMap.insertList, List.mem_singleton] at hrow
      subst row
      exact valueNonzero
  | (headKey, headValue) :: tail, canonical => by
      intro row hrow
      have headNonzero : headValue ≠ (0 : PlayerCounter) :=
        canonical (headKey, headValue) (by simp)
      have tailCanonical : ∀ prior ∈ tail, prior.2 ≠ (0 : PlayerCounter) := by
        intro prior hprior
        exact canonical prior (by simp [hprior])
      by_cases hlt : key < headKey
      · simp only [SortedMap.insertList, hlt, if_true, List.mem_cons] at hrow
        rcases hrow with rfl | rfl | htail
        · exact valueNonzero
        · exact headNonzero
        · exact tailCanonical row htail
      · simp only [SortedMap.insertList, hlt, if_false] at hrow
        by_cases heq : key = headKey
        · simp only [heq, if_true, List.mem_cons] at hrow
          rcases hrow with rfl | htail
          · exact valueNonzero
          · exact tailCanonical row htail
        · simp only [heq, if_false, List.mem_cons] at hrow
          rcases hrow with rfl | htail
          · exact headNonzero
          · exact insertList_preserves_no_zero key value valueNonzero tail tailCanonical row htail

private theorem insert_preserves_no_zero (table : PlayerCounterTable)
    (key : PlayerCounterKey) (value : PlayerCounter) (valueNonzero : value ≠ 0) :
    SortedMap.Canonical (0 : PlayerCounter) (table.toMap.toMap.insert key value) := by
  exact insertList_preserves_no_zero key value valueNonzero table.toMap.toMap.entries
    table.toMap.canon

/-- Overwrite or insert a nonzero bounded counter while preserving canonical order. -/
def set (table : PlayerCounterTable) (key : PlayerCounterKey)
    (value : PlayerCounter) (valueNonzero : value ≠ 0) : PlayerCounterTable where
  toMap := {
    toMap := table.toMap.toMap.insert key value
    canon := insert_preserves_no_zero table key value valueNonzero
  }

private theorem lookupList_insertList_same (key : PlayerCounterKey) (value : PlayerCounter) :
    ∀ entries : List (PlayerCounterKey × PlayerCounter),
      lookupList key (SortedMap.insertList key value entries) = some value
  | [] => by simp [SortedMap.insertList, lookupList]
  | (headKey, headValue) :: tail => by
      by_cases hlt : key < headKey
      · simp [SortedMap.insertList, lookupList, hlt]
      · by_cases heq : key = headKey
        · subst headKey
          simp [SortedMap.insertList, lookupList]
        · have hhead : headKey ≠ key := fun h => heq h.symm
          simp [SortedMap.insertList, lookupList, hlt, heq, hhead,
            lookupList_insertList_same key value tail]

private theorem lookupList_insertList_other (query key : PlayerCounterKey)
    (value : PlayerCounter) (different : query ≠ key) :
    ∀ entries : List (PlayerCounterKey × PlayerCounter),
      lookupList query (SortedMap.insertList key value entries) = lookupList query entries
  | [] => by simp [SortedMap.insertList, lookupList, Ne.symm different]
  | (headKey, headValue) :: tail => by
      by_cases hlt : key < headKey
      · simp [SortedMap.insertList, lookupList, hlt, Ne.symm different]
      · by_cases heq : key = headKey
        · subst headKey
          simp [SortedMap.insertList, lookupList, Ne.symm different]
        · by_cases hquery : query = headKey
          · subst query
            simp [SortedMap.insertList, lookupList, hlt, heq]
          · simp [SortedMap.insertList, lookupList, hlt, heq,
              lookupList_insertList_other query key value different tail]

theorem lookup_set (table : PlayerCounterTable) (key : PlayerCounterKey)
    (value : PlayerCounter) (valueNonzero : value ≠ 0) (query : PlayerCounterKey) :
    (table.set key value valueNonzero).lookup query =
      if query = key then value else table.lookup query := by
  by_cases hquery : query = key
  · subst query
    rw [if_pos rfl]
    simp only [set, lookup, CanonMap.get, SortedMap.get, SortedMap.lookup, SortedMap.insert]
    have hs := lookupList_insertList_same key value table.toMap.toMap.entries
    simpa using congrArg (fun result : Option PlayerCounter => result.getD 0) hs
  · rw [if_neg hquery]
    simp only [set, lookup, CanonMap.get, SortedMap.get, SortedMap.lookup, SortedMap.insert]
    have hs := lookupList_insertList_other query key value hquery table.toMap.toMap.entries
    exact congrArg (fun result : Option PlayerCounter => result.getD 0) hs

@[simp] theorem lookup_set_same (table : PlayerCounterTable) (key : PlayerCounterKey)
    (value : PlayerCounter) (valueNonzero : value ≠ 0) :
    (table.set key value valueNonzero).lookup key = value := by
  simp [lookup_set]

theorem lookup_set_other (table : PlayerCounterTable) (key : PlayerCounterKey)
    (value : PlayerCounter) (valueNonzero : value ≠ 0) (other : PlayerCounterKey)
    (different : other ≠ key) :
    (table.set key value valueNonzero).lookup other = table.lookup other := by
  simp [lookup_set, different]

theorem set_agrees_with_function_update (table : PlayerCounterTable)
    (key : PlayerCounterKey) (value : PlayerCounter) (valueNonzero : value ≠ 0) :
    (fun query => (table.set key value valueNonzero).lookup query) =
      Function.update table.lookup key value := by
  funext query
  by_cases h : query = key
  · subst query
    simp [Function.update]
  · simp [lookup_set, h, Function.update]

#assert_axioms rows_sorted
#assert_axioms rows_no_zero
#assert_axioms lookup_empty
#assert_axioms ofRows_rows_exact
#assert_axioms ofRows_refuses_unsorted
#assert_axioms ofRows_refuses_zero
#assert_axioms ofRows_roundtrip
#assert_axioms lookup_set
#assert_axioms lookup_set_same
#assert_axioms lookup_set_other
#assert_axioms set_agrees_with_function_update

end PlayerCounterTable

end Dregg2.Games.PathOfAngels
