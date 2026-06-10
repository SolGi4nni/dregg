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

/-! ## §X — STRENGTHENED full-state spec (projection → INDEPENDENT declarative frame).

`EnlivenSpec` pins the post-state via `s' = { kernel := swissEnlivenK s.kernel sw claimed, log := … }`
— it DELEGATES the kernel to the executor helper, never independently stating WHICH of the 17 fields a
committed enliven may touch (a PROJECTION). `EnlivenSpecFull` is the INDEPENDENT, fully-declarative
full-state spec: the guard holds; post-`swiss` is EXACTLY the declarative refcount-bump image
`enlivenSwissPost`; the log gains exactly the receipt; and EVERY one of the 16 non-`swiss` kernel fields
is LITERALLY unchanged (no `swissEnlivenK` in any clause). -/
def EnlivenSpecFull (s : RecChainedState) (sw : Nat) (actor exporter : CellId) (claimed : List Auth)
    (s' : RecChainedState) : Prop :=
  EnlivenGuard s sw actor exporter claimed
  ∧ (∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
       ∧ rightsNarrowerOrEqual claimed e.rights = true
       ∧ s'.kernel.swiss = enlivenSwissPost s.kernel.swiss sw e)
  ∧ s'.log = enlivenReceipt actor exporter :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-- **`execFullA_enliven_iff_specFull` — EXECUTOR ⟺ the STRENGTHENED full-state spec.** -/
theorem execFullA_enliven_iff_specFull (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    execFullA s (.enlivenRefA sw actor exporter claimed) = some s'
      ↔ EnlivenSpecFull s sw actor exporter claimed s' := by
  rw [execFullA_enliven_iff_spec]
  constructor
  · rintro ⟨hg, ⟨kw, hk, hs'⟩⟩
    obtain ⟨hauth, e, hf, hr⟩ := hg
    have hupd : enlivenSwissUpdate s.kernel.swiss sw claimed = some (enlivenSwissPost s.kernel.swiss sw e) :=
      enlivenSwissUpdate_some s.kernel.swiss sw claimed e hf hr
    have hkeq : kw = { s.kernel with swiss := enlivenSwissPost s.kernel.swiss sw e } := by
      have := (enlivenSwissUpdate_eq_k s.kernel sw claimed (enlivenSwissPost s.kernel.swiss sw e)).mp hupd
      exact Option.some.inj (hk.symm.trans this)
    subst hs'
    refine ⟨⟨hauth, e, hf, hr⟩, ⟨e, hf, hr, ?_⟩, rfl, ?_⟩
    · rw [hkeq]
    · rw [hkeq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hg, ⟨e, hf, hr, hsw⟩, hlog, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13,
      h14, h15, h16, h17⟩
    refine ⟨hg, ⟨{ s.kernel with swiss := enlivenSwissPost s.kernel.swiss sw e }, ?_, ?_⟩⟩
    · exact (enlivenSwissUpdate_eq_k s.kernel sw claimed _).mp (enlivenSwissUpdate_some s.kernel.swiss sw claimed e hf hr)
    · obtain ⟨k', lg'⟩ := s'
      simp only at hsw hlog h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17
      have hke : k' = { s.kernel with swiss := enlivenSwissPost s.kernel.swiss sw e } :=
        recKernel_ext h1 h2 h3 h4 h5 h6 h7 hsw h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hke hlog; rfl

/-- **The strengthening is REAL (EnlivenSpec ≡ EnlivenSpecFull).** -/
theorem enlivenSpec_iff_specFull (s : RecChainedState) (sw : Nat) (actor exporter : CellId)
    (claimed : List Auth) (s' : RecChainedState) :
    EnlivenSpec s sw actor exporter claimed s' ↔ EnlivenSpecFull s sw actor exporter claimed s' :=
  Iff.trans (execFullA_enliven_iff_spec s sw actor exporter claimed s').symm
            (execFullA_enliven_iff_specFull s sw actor exporter claimed s')

/-! ## §X.tooth — the strengthening REJECTS a `sealedBoxes` tampering the weak frame could not see. -/

/-- The STRONG full-state spec REJECTS a post-state that tampers ONLY `sealedBoxes` (an untouched field)
— even though it agrees with the true output on 16 of 17 kernel fields + the log (the near-miss the
old `bal`/`accounts` projection would still accept). The `sealedBoxes` frame conjunct catches the ghost
the executor-delegating spec only avoided by accident of the helper. -/
theorem enlivenSpecFull_rejects_sealedBoxes_tamper (s s' : RecChainedState) (sw : Nat)
    (actor exporter : CellId) (claimed : List Auth)
    (h : execFullA s (.enlivenRefA sw actor exporter claimed) = some s')
    (badBoxes : List SealedBoxRecord) (hne : badBoxes ≠ s.kernel.sealedBoxes) :
    ¬ EnlivenSpecFull s sw actor exporter claimed
        { s' with kernel := { s'.kernel with sealedBoxes := badBoxes } } := by
  -- the strong spec's `sealedBoxes` frame conjunct (`= s.kernel.sealedBoxes`) contradicts `badBoxes`.
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hboxes, _, _⟩
  exact hne hboxes

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
#assert_axioms execFullA_enliven_iff_specFull
#assert_axioms enlivenSpec_iff_specFull
#assert_axioms enlivenSpecFull_rejects_sealedBoxes_tamper

end Dregg2.Circuit.Spec.SwissEnliven