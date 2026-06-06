/-
# Dregg2.Circuit.Spec.swissenliven — INDEPENDENT full-state spec + executor⟺spec for `enlivenRefA`.
-/
import Dregg2.Circuit.Spec.swissframe

namespace Dregg2.Circuit.Spec.SwissEnliven

open Dregg2.Circuit.Spec.SwissFrame
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Authority (Auth)

def enlivenReceipt (actor exporter : CellId) : Turn :=
  { actor := actor, src := exporter, dst := exporter, amt := 0 }

def enlivenRecord (e : SwissRecord) : SwissRecord :=
  { e with refcount := e.refcount + 1 }

def enlivenSwissPost (ss : List SwissRecord) (sw : Nat) (e : SwissRecord) : List SwissRecord :=
  replaceSwiss ss sw (enlivenRecord e)

def enlivenSwissUpdate (ss : List SwissRecord) (sw : Nat) (claimed : List Auth) : Option (List SwissRecord) :=
  match findSwiss ss sw with
  | none   => none
  | some e =>
      if rightsNarrowerOrEqual claimed e.rights then
        some (enlivenSwissPost ss sw e)
      else none

def EnlivenGuard (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth) : Prop :=
  stateAuthB s.kernel.caps actor exporter = true
  ∧ ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
      ∧ rightsNarrowerOrEqual claimed e.rights = true

theorem enlivenRecord_correct (e : SwissRecord) :
    (enlivenRecord e).swiss = e.swiss
    ∧ (enlivenRecord e).exporter = e.exporter
    ∧ (enlivenRecord e).target = e.target
    ∧ (enlivenRecord e).rights = e.rights
    ∧ (enlivenRecord e).refcount = e.refcount + 1
    ∧ (enlivenRecord e).cert = e.cert := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem enlivenRecord_lookup (ss : List SwissRecord) (sw : Nat) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) :
    findSwiss (enlivenSwissPost ss sw e) sw = some (enlivenRecord e) := by
  have hsw : (enlivenRecord e).swiss = sw := by
    rw [(enlivenRecord_correct e).1, findSwiss_swiss_eq hf]
  exact findSwiss_replaceSwiss_self ss sw e (enlivenRecord e) hf hsw

theorem enlivenSwissUpdate_some (ss : List SwissRecord) (sw : Nat) (claimed : List Auth) (e : SwissRecord)
    (hf : findSwiss ss sw = some e) (hr : rightsNarrowerOrEqual claimed e.rights) :
    enlivenSwissUpdate ss sw claimed = some (enlivenSwissPost ss sw e) := by
  simp only [enlivenSwissUpdate, hf, if_pos hr]

theorem enlivenSwissUpdate_eq_k (k : RecordKernelState) (sw : Nat) (claimed : List Auth)
    (ss : List SwissRecord) :
    enlivenSwissUpdate k.swiss sw claimed = some ss ↔
      swissEnlivenK k sw claimed = some { k with swiss := ss } := by
  unfold enlivenSwissUpdate swissEnlivenK
  cases hf : findSwiss k.swiss sw with
  | none   => simp [hf]
  | some e =>
      simp only [hf]
      by_cases hr : rightsNarrowerOrEqual claimed e.rights
      · simp only [if_pos hr]; constructor <;> intro h <;> simp [Option.some.injEq] at h <;> subst h <;> rfl
      · simp only [if_neg hr]; constructor <;> intro h <;> simp at h

/-- Existential post-state: guard + kernel witness + log head (queue-atomic style). -/
def EnlivenSpec (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
    (s' : RecChainedState) : Prop :=
  EnlivenGuard s sw actor exporter claimed
  ∧ ∃ k', swissEnlivenK s.kernel sw claimed = some k'
    ∧ s' = { kernel := k', log := enlivenReceipt actor exporter :: s.log }

theorem enlivenChain_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    swissEnlivenChainA s sw actor exporter claimed = some s'
      ↔ EnlivenSpec s sw actor exporter claimed s' := by
  unfold EnlivenSpec swissEnlivenChainA
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth]
    cases hk : swissEnlivenK s.kernel sw claimed with
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
        unfold swissEnlivenK at hk
        cases hf : findSwiss s.kernel.swiss sw with
        | none => simp [hf] at hk
        | some e =>
          simp only [hf] at hk
          by_cases hr : rightsNarrowerOrEqual claimed e.rights
          · simp only [if_pos hr] at hk; exact ⟨e, ⟨rfl, hr⟩⟩
          · simp only [if_neg hr] at hk; exact absurd hk (by simp)
      · rintro ⟨_, ⟨k'', hk', hs'⟩⟩
        simp only [Option.some.injEq] at hk'
        subst hk'
        rw [hs']
        rfl
  · rw [if_neg hauth]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hauth', _⟩, _⟩; exact absurd hauth' hauth

theorem execFullA_enliven_iff_spec (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = some s'
      ↔ EnlivenSpec s sw actor exporter claimed s' := by
  simp only [execFullA]
  exact enlivenChain_iff_spec s sw actor exporter claimed s'

theorem enliven_spec_bumps_refcount (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) (e : SwissRecord)
    (hf : findSwiss s.kernel.swiss sw = some e)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    findSwiss s'.kernel.swiss sw = some (enlivenRecord e) := by
  rcases (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h with
    ⟨⟨_, ⟨e', ⟨hf', _⟩⟩⟩, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have heq : e' = e := Option.some.inj (hf'.symm.trans hf)
  subst heq
  have hker := congr_arg (·.kernel) hs'
  have hk' : swissEnlivenK s.kernel sw claimed = some s'.kernel :=
    hk.trans (congr_arg some hker.symm)
  exact swissEnlivenK_bumps_refcount hf' hk'

theorem enliven_spec_non_amplifying (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    ∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
      ∧ rightsNarrowerOrEqual claimed e.rights = true :=
  (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h |>.1.2

theorem enliven_spec_balance_neutral (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    s'.kernel.bal = s.kernel.bal ∧ s'.kernel.accounts = s.kernel.accounts := by
  rcases (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h with
    ⟨_, ⟨kw, ⟨hk, hs'⟩⟩⟩
  have hkw := swissEnlivenK_only_swiss hk
  have hbal := kernel_swiss_update_bal_accounts hkw
  have hker : s'.kernel = kw := congr_arg RecChainedState.kernel hs'
  rw [hker]
  exact hbal

theorem enliven_spec_authorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s') :
    stateAuthB s.kernel.caps actor exporter = true :=
  (execFullA_enliven_iff_spec s sw actor exporter claimed s').mp h |>.1.1

theorem enliven_rejects_unauthorized (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hbad : stateAuthB s.kernel.caps actor exporter ≠ true) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, swissEnlivenChainA, if_neg hbad]

theorem enliven_rejects_absent (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (hf : findSwiss s.kernel.swiss sw = none) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, swissEnlivenChainA]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, swissEnlivenK_absent_rejects s.kernel sw claimed hf]
  · rw [if_neg hauth]

theorem enliven_rejects_amplifying (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (e : SwissRecord) (hf : findSwiss s.kernel.swiss sw = some e)
    (hbad : rightsNarrowerOrEqual claimed e.rights = false) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = none := by
  simp only [execFullA, swissEnlivenChainA]
  by_cases hauth : stateAuthB s.kernel.caps actor exporter = true
  · rw [if_pos hauth, swissEnlivenK_amplification_rejects s.kernel sw claimed e hf hbad]
  · rw [if_neg hauth]

#assert_axioms enlivenRecord_correct
#assert_axioms enlivenRecord_lookup
#assert_axioms enlivenSwissUpdate_some
#assert_axioms enlivenSwissUpdate_eq_k
#assert_axioms enlivenChain_iff_spec
#assert_axioms execFullA_enliven_iff_spec
#assert_axioms enliven_spec_bumps_refcount
#assert_axioms enliven_spec_non_amplifying
#assert_axioms enliven_spec_balance_neutral
#assert_axioms enliven_spec_authorized
#assert_axioms enliven_rejects_unauthorized
#assert_axioms enliven_rejects_absent
#assert_axioms enliven_rejects_amplifying

end Dregg2.Circuit.Spec.SwissEnliven