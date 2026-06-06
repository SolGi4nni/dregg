/-
# Dregg2.Circuit.Spec.swisshandoff — INDEPENDENT full-state spec + executor⟺spec for `swissHandoffA`.
-/
import Dregg2.Circuit.Spec.swissframe

namespace Dregg2.Circuit.Spec.SwissHandoff

open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)

def handoffReceipt (introducer exporter : CellId) : Turn :=
  { actor := introducer, src := exporter, dst := exporter, amt := 0 }

def handoffRecord (e : SwissRecord) (certHash : Nat) : SwissRecord :=
  { e with cert := some certHash, refcount := e.refcount + 1 }

def handoffSwissPost (ss : List SwissRecord) (sw : Nat) (e : SwissRecord) (certHash : Nat) :
    List SwissRecord :=
  replaceSwiss ss sw (handoffRecord e certHash)

def handoffSwissUpdate (ss : List SwissRecord) (sw certHash : Nat) : Option (List SwissRecord) :=
  match findSwiss ss sw with
  | none   => none
  | some e => some (handoffSwissPost ss sw e certHash)

def HandoffGuard (s : RecChainedState) (sw : Nat) (introducer exporter : CellId) : Prop :=
  stateAuthB s.kernel.caps introducer exporter = true
  ∧ ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e

theorem handoffRecord_correct (e : SwissRecord) (certHash : Nat) :
    (handoffRecord e certHash).swiss = e.swiss
    ∧ (handoffRecord e certHash).exporter = e.exporter
    ∧ (handoffRecord e certHash).target = e.target
    ∧ (handoffRecord e certHash).rights = e.rights
    ∧ (handoffRecord e certHash).refcount = e.refcount + 1
    ∧ (handoffRecord e certHash).cert = some certHash := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem handoffRecord_lookup (ss : List SwissRecord) (sw : Nat) (e : SwissRecord) (certHash : Nat)
    (hf : findSwiss ss sw = some e) :
    findSwiss (handoffSwissPost ss sw e certHash) sw = some (handoffRecord e certHash) := by
  have hsw : (handoffRecord e certHash).swiss = sw := by
    rw [(handoffRecord_correct e certHash).1, findSwiss_swiss_eq hf]
  exact findSwiss_replaceSwiss_self ss sw e (handoffRecord e certHash) hf hsw

theorem handoffSwissUpdate_some (ss : List SwissRecord) (sw certHash : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) :
    handoffSwissUpdate ss sw certHash = some (handoffSwissPost ss sw e certHash) := by
  simp only [handoffSwissUpdate, hf]

theorem handoffSwissUpdate_eq_k (k : RecordKernelState) (sw certHash : Nat) (ss : List SwissRecord) :
    handoffSwissUpdate k.swiss sw certHash = some ss ↔
      swissHandoffK k sw certHash = some { k with swiss := ss } := by
  unfold handoffSwissUpdate swissHandoffK
  cases hf : findSwiss k.swiss sw with
  | none   => simp [hf]
  | some e => simp only [hf]; constructor <;> intro h <;> simp [Option.some.injEq] at h <;> subst h <;> rfl

def HandoffSpec (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) : Prop :=
  HandoffGuard s sw introducer exporter
  ∧ ∃ k', swissHandoffK s.kernel sw certHash = some k'
    ∧ s' = { kernel := k', log := handoffReceipt introducer exporter :: s.log }

theorem handoffChain_iff_spec (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) :
    swissHandoffChainA s sw certHash introducer exporter = some s'
      ↔ HandoffSpec s sw certHash introducer exporter s' := by
  unfold HandoffSpec swissHandoffChainA
  by_cases hauth : stateAuthB s.kernel.caps introducer exporter = true
  · rw [if_pos hauth]
    cases hk : swissHandoffK s.kernel sw certHash with
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
        unfold swissHandoffK at hk
        cases hf : findSwiss s.kernel.swiss sw with
        | none => simp [hf] at hk
        | some e => simp only [hf] at hk; exact ⟨e, rfl⟩
      · rintro ⟨_, ⟨k'', hk', hs'⟩⟩
        simp only [Option.some.injEq] at hk'
        subst hk'
        rw [hs']
        rfl
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth', _⟩, _⟩; exact absurd hauth' hauth

theorem execFullA_handoff_iff_spec (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) :
    execFullA s (.swissHandoffA sw certHash introducer exporter) = some s'
      ↔ HandoffSpec s sw certHash introducer exporter s' := by
  simp only [execFullA]
  exact handoffChain_iff_spec s sw certHash introducer exporter s'

theorem handoff_spec_binds_cert (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) (e : SwissRecord) (hf : findSwiss s.kernel.swiss sw = some e)
    (h : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s') :
    findSwiss s'.kernel.swiss sw = some (handoffRecord e certHash) := by
  rcases (execFullA_handoff_iff_spec s sw certHash introducer exporter s').mp h with
    ⟨_, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have hker : s'.kernel = kw := by cases s'; cases hs'; rfl
  rw [hker]
  unfold swissHandoffK at hk
  simp only [hf] at hk
  have heq := (Option.some.inj hk).symm
  have hpost : kw.swiss = handoffSwissPost s.kernel.swiss sw e certHash :=
    congr_arg (fun k : RecordKernelState => k.swiss) heq
  rw [hpost]
  exact handoffRecord_lookup s.kernel.swiss sw e certHash hf

theorem handoff_spec_balance_neutral (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) (h : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  rcases (execFullA_handoff_iff_spec s sw certHash introducer exporter s').mp h with
    ⟨_, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have hkw := swissHandoffK_only_swiss hk
  have hbal := kernel_swiss_update_bal_accounts hkw
  have hker : s'.kernel = kw := congr_arg RecChainedState.kernel hs'
  rw [hker]
  exact hbal

theorem handoff_spec_authorized (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) (h : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s') :
    stateAuthB s.kernel.caps introducer exporter = true :=
  (execFullA_handoff_iff_spec s sw certHash introducer exporter s').mp h |>.1.1

theorem handoff_rejects_unauthorized (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (hbad : stateAuthB s.kernel.caps introducer exporter ≠ true) :
    execFullA s (.swissHandoffA sw certHash introducer exporter) = none := by
  simp only [execFullA, swissHandoffChainA, if_neg hbad]

theorem handoff_rejects_absent (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (hf : findSwiss s.kernel.swiss sw = none) :
    execFullA s (.swissHandoffA sw certHash introducer exporter) = none := by
  simp only [execFullA, swissHandoffChainA]
  by_cases hauth : stateAuthB s.kernel.caps introducer exporter = true
  · rw [if_pos hauth, swissHandoffK, hf]
  · rw [if_neg hauth]

theorem handoff_no_spec_when_unauthorized (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) (hbad : stateAuthB s.kernel.caps introducer exporter ≠ true) :
    ¬ execFullA s (.swissHandoffA sw certHash introducer exporter) = some s' := by
  rw [handoff_rejects_unauthorized s sw certHash introducer exporter hbad]; simp

#assert_axioms handoffRecord_correct
#assert_axioms handoffRecord_lookup
#assert_axioms handoffSwissUpdate_some
#assert_axioms handoffSwissUpdate_eq_k
#assert_axioms handoffChain_iff_spec
#assert_axioms execFullA_handoff_iff_spec
#assert_axioms handoff_spec_binds_cert
#assert_axioms handoff_spec_balance_neutral
#assert_axioms handoff_spec_authorized
#assert_axioms handoff_rejects_unauthorized
#assert_axioms handoff_rejects_absent
#assert_axioms handoff_no_spec_when_unauthorized

end Dregg2.Circuit.Spec.SwissHandoff