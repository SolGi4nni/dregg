/-
# Dregg2.Circuit.Spec.swissdrop — INDEPENDENT full-state spec + executor⟺spec for `swissDropA`.
-/
import Dregg2.Circuit.Spec.swissframe

namespace Dregg2.Circuit.Spec.SwissDrop

open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

private theorem refcount_one_of_pred_zero {n : Nat} (h : n - 1 = 0) (hpos : 0 < n) : n = 1 := by
  rcases n with _ | n
  · exact absurd hpos (Nat.not_lt_zero 0)
  · rcases n with _ | n
    · rfl
    · simp at h

def dropReceipt (actor exporter : CellId) : Turn :=
  { actor := actor, src := exporter, dst := exporter, amt := 0 }

def dropRecord (e : SwissRecord) : SwissRecord :=
  { e with refcount := e.refcount - 1 }

def dropSwissPost (ss : List SwissRecord) (sw : Nat) (e : SwissRecord) : List SwissRecord :=
  if e.refcount = 1 then removeSwiss ss sw
  else replaceSwiss ss sw (dropRecord e)

def dropSwissUpdate (ss : List SwissRecord) (sw : Nat) : Option (List SwissRecord) :=
  match findSwiss ss sw with
  | none   => none
  | some e =>
      if e.refcount = 0 then none
      else if e.refcount - 1 = 0 then some (removeSwiss ss sw)
      else some (replaceSwiss ss sw (dropRecord e))

def DropGuard (s : RecChainedState) (sw : Nat) (actor exporter : CellId) : Prop :=
  stateAuthB s.kernel.caps actor exporter = true
  ∧ ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e ∧ 0 < e.refcount

theorem dropSwissUpdate_some_gc (ss : List SwissRecord) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) (hone : e.refcount = 1) :
    dropSwissUpdate ss sw = some (removeSwiss ss sw) := by
  unfold dropSwissUpdate
  simp only [hf]
  have hz : ¬ e.refcount = 0 := by rw [hone]; decide
  have hp : e.refcount - 1 = 0 := by rw [hone]
  simp only [if_neg hz, if_pos hp]

theorem dropSwissUpdate_some_decrement (ss : List SwissRecord) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) (hgt : 1 < e.refcount) :
    dropSwissUpdate ss sw = some (replaceSwiss ss sw (dropRecord e)) := by
  have hz : ¬ e.refcount = 0 := fun h => by rw [h] at hgt; exact Nat.not_lt_zero 1 hgt
  have hone : ¬ e.refcount - 1 = 0 := fun h =>
    absurd (refcount_one_of_pred_zero h (Nat.lt_trans Nat.zero_lt_one hgt)) (ne_of_gt hgt)
  simp only [dropSwissUpdate, hf, if_neg hz, if_neg hone]

theorem dropSwissUpdate_eq_k (k : RecordKernelState) (sw : Nat) (ss : List SwissRecord) :
    dropSwissUpdate k.swiss sw = some ss ↔
      swissDropK k sw = some { k with swiss := ss } := by
  unfold dropSwissUpdate swissDropK
  cases hf : findSwiss k.swiss sw with
  | none   => simp [hf]
  | some e =>
      by_cases hz : e.refcount = 0
      · simp only [hf, hz]; constructor <;> intro h <;> simp at h
      · simp only [hf, if_neg hz]
        by_cases hone : e.refcount - 1 = 0
        · simp only [if_pos hone]; constructor <;> intro h <;> simp [Option.some.injEq] at h <;> subst h <;> rfl
        · simp only [if_neg hone]; constructor <;> intro h <;> simp [Option.some.injEq] at h <;> subst h <;> rfl

theorem dropSwissPost_eq_update (ss : List SwissRecord) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) (hpos : 0 < e.refcount) :
    dropSwissUpdate ss sw = some (dropSwissPost ss sw e) := by
  rcases e with ⟨_, _, _, _, rc, _⟩
  by_cases hone : rc = 1
  · subst hone
    simpa [dropSwissPost] using dropSwissUpdate_some_gc ss sw _ hf rfl
  · have hgt : 1 < rc := by
      rcases rc with _ | n
      · exact absurd hpos (Nat.not_lt_zero _)
      · rcases n with _ | n
        · exact absurd rfl hone
        · exact Nat.succ_lt_succ (Nat.zero_lt_succ n)
    have hz : ¬ rc = 0 := fun h => by rw [h] at hpos; exact Nat.not_lt_zero _ hpos
    have hpred : ¬ rc - 1 = 0 := fun h =>
      absurd (refcount_one_of_pred_zero h hpos) (ne_of_gt hgt)
    simp only [dropSwissUpdate, dropSwissPost, hf, if_neg hz, if_neg hpred, if_neg hone]

def DropSpec (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (s' : RecChainedState) : Prop :=
  DropGuard s sw actor exporter
  ∧ ∃ k', swissDropK s.kernel sw = some k'
    ∧ s' = { kernel := k', log := dropReceipt actor exporter :: s.log }

theorem dropChain_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (s' : RecChainedState) :
    swissDropChainA s sw actor exporter = some s'
      ↔ DropSpec s sw actor exporter s' := by
  unfold DropSpec swissDropChainA
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth]
    cases hk : swissDropK s.kernel sw with
    | none =>
      simp only [hk]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨_, ⟨k', hk', _⟩⟩; exact absurd hk' (by simp [hk])
    | some k' =>
      simp only [hk]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨⟨hauth, ?_⟩, ⟨k', ⟨rfl, rfl⟩⟩⟩
        unfold swissDropK at hk
        cases hf : findSwiss s.kernel.swiss sw with
        | none => simp [hf] at hk
        | some e =>
          simp only [hf] at hk
          by_cases hz : e.refcount = 0
          · simp only [if_pos hz] at hk; exact absurd hk (by simp)
          · simp only [if_neg hz] at hk
            have hpos : 0 < e.refcount := Nat.pos_of_ne_zero (fun h => hz h)
            exact ⟨e, ⟨rfl, hpos⟩⟩
      · rintro ⟨_, ⟨k'', hk', hs'⟩⟩
        simp only [Option.some.injEq] at hk'
        subst hk'
        rw [hs']
        rfl
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth', _⟩, _⟩; exact absurd hauth' hauth

theorem execFullA_drop_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (s' : RecChainedState) :
    execFullA s (.swissDropA sw actor exporter) = some s'
      ↔ DropSpec s sw actor exporter s' := by
  simp only [execFullA]
  exact dropChain_iff_spec s sw actor exporter s'

theorem drop_spec_gcs_at_one (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (s' : RecChainedState) (e : SwissRecord) (hf : findSwiss s.kernel.swiss sw = some e)
    (hone : e.refcount = 1)
    (h : execFullA s (.swissDropA sw actor exporter) = some s') :
    findSwiss s'.kernel.swiss sw = none := by
  rcases (execFullA_drop_iff_spec s sw actor exporter s').mp h with
    ⟨_, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have hker := congr_arg (·.kernel) hs'
  have hk' : swissDropK s.kernel sw = some s'.kernel :=
    hk.trans (congr_arg some hker.symm)
  exact swissDropK_gc_at_one hf hone hk'

theorem drop_spec_balance_neutral (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (s' : RecChainedState) (h : execFullA s (.swissDropA sw actor exporter) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  rcases (execFullA_drop_iff_spec s sw actor exporter s').mp h with
    ⟨_, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have hkw := swissDropK_only_swiss hk
  have hbal := kernel_swiss_update_bal_accounts hkw
  have hker : s'.kernel = kw := congr_arg RecChainedState.kernel hs'
  rw [hker]
  exact hbal

theorem drop_spec_authorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (s' : RecChainedState) (h : execFullA s (.swissDropA sw actor exporter) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  (execFullA_drop_iff_spec s sw actor exporter s').mp h |>.1.1

theorem drop_rejects_unauthorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    execFullA s (.swissDropA sw actor exporter) = none := by
  simp only [execFullA, swissDropChainA, if_neg hbad]

theorem drop_rejects_absent (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (hf : findSwiss s.kernel.swiss sw = none) :
    execFullA s (.swissDropA sw actor exporter) = none := by
  simp only [execFullA, swissDropChainA]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, swissDropK, hf]
  · rw [if_neg hauth]

theorem drop_rejects_zero_refcount (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (e : SwissRecord) (hf : findSwiss s.kernel.swiss sw = some e) (hz : e.refcount = 0) :
    execFullA s (.swissDropA sw actor exporter) = none := by
  simp only [execFullA, swissDropChainA]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, swissDropK_zero_rejects s.kernel sw e hf hz]
  · rw [if_neg hauth]

theorem drop_no_spec_when_unauthorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (s' : RecChainedState) (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    ¬ execFullA s (.swissDropA sw actor exporter) = some s' := by
  rw [drop_rejects_unauthorized s sw actor exporter hbad]; simp

#assert_axioms dropSwissUpdate_some_gc
#assert_axioms dropSwissUpdate_some_decrement
#assert_axioms dropSwissUpdate_eq_k
#assert_axioms dropSwissPost_eq_update
#assert_axioms dropChain_iff_spec
#assert_axioms execFullA_drop_iff_spec
#assert_axioms drop_spec_gcs_at_one
#assert_axioms drop_spec_balance_neutral
#assert_axioms drop_spec_authorized
#assert_axioms drop_rejects_unauthorized
#assert_axioms drop_rejects_absent
#assert_axioms drop_rejects_zero_refcount
#assert_axioms drop_no_spec_when_unauthorized

end Dregg2.Circuit.Spec.SwissDrop