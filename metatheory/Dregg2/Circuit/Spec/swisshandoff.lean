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
  ∧ (findSwiss s.kernel.swiss sw).isSome = true

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
        | some _ => simp [hf, Option.isSome]
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

/-! ## §X — STRENGTHENED full-state spec (projection → INDEPENDENT declarative frame).

`HandoffSpec` pins the post-state via `s' = { kernel := swissHandoffK s.kernel sw certHash, log := … }`
— it DELEGATES the kernel to the executor helper, never independently stating WHICH of the 17 fields a
committed handoff may touch (a PROJECTION). `HandoffSpecFull` is the INDEPENDENT, fully-declarative
full-state spec: the guard holds; post-`swiss` is EXACTLY the declarative cert-bind/refcount-bump image
`handoffSwissPost`; the log gains exactly the receipt; and EVERY one of the 16 non-`swiss` kernel fields
is LITERALLY unchanged (no `swissHandoffK` in any clause). -/
def HandoffSpecFull (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) : Prop :=
  HandoffGuard s sw introducer exporter
  ∧ (∃ e : SwissRecord, findSwiss s.kernel.swiss sw = some e
       ∧ s'.kernel.swiss = handoffSwissPost s.kernel.swiss sw e certHash)
  ∧ s'.log = handoffReceipt introducer exporter :: s.log
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

/-- **`execFullA_handoff_iff_specFull` — EXECUTOR ⟺ the STRENGTHENED full-state spec.** -/
theorem execFullA_handoff_iff_specFull (s : RecChainedState) (sw certHash : Nat)
    (introducer exporter : CellId) (s' : RecChainedState) :
    execFullA s (.swissHandoffA sw certHash introducer exporter) = some s'
      ↔ HandoffSpecFull s sw certHash introducer exporter s' := by
  rw [execFullA_handoff_iff_spec]
  constructor
  · rintro ⟨hg, ⟨kw, hk, hs'⟩⟩
    obtain ⟨hauth, hsome⟩ := hg
    obtain ⟨e, hf⟩ := Option.isSome_iff_exists.mp hsome
    have hupd : handoffSwissUpdate s.kernel.swiss sw certHash
        = some (handoffSwissPost s.kernel.swiss sw e certHash) :=
      handoffSwissUpdate_some s.kernel.swiss sw certHash e hf
    have hkeq : kw = { s.kernel with swiss := handoffSwissPost s.kernel.swiss sw e certHash } := by
      have := (handoffSwissUpdate_eq_k s.kernel sw certHash (handoffSwissPost s.kernel.swiss sw e certHash)).mp hupd
      exact Option.some.inj (hk.symm.trans this)
    subst hs'
    refine ⟨⟨hauth, hsome⟩, ⟨e, hf, ?_⟩, rfl, ?_⟩
    · rw [hkeq]
    · rw [hkeq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rintro ⟨hg, ⟨e, hf, hsw⟩, hlog, h1, h2, h3, h4, h5, h6, h7, h9, h10, h11, h12, h13,
      h14, h15, h16, h17⟩
    refine ⟨hg, ⟨{ s.kernel with swiss := handoffSwissPost s.kernel.swiss sw e certHash }, ?_, ?_⟩⟩
    · exact (handoffSwissUpdate_eq_k s.kernel sw certHash _).mp (handoffSwissUpdate_some s.kernel.swiss sw certHash e hf)
    · obtain ⟨k', lg'⟩ := s'
      simp only at hsw hlog h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17
      have hke : k' = { s.kernel with swiss := handoffSwissPost s.kernel.swiss sw e certHash } :=
        recKernel_ext h1 h2 h3 h4 h5 h6 h7 hsw h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hke hlog; rfl

/-- **The strengthening is REAL (HandoffSpec ≡ HandoffSpecFull).** -/
theorem handoffSpec_iff_specFull (s : RecChainedState) (sw certHash : Nat) (introducer exporter : CellId)
    (s' : RecChainedState) :
    HandoffSpec s sw certHash introducer exporter s' ↔ HandoffSpecFull s sw certHash introducer exporter s' :=
  Iff.trans (execFullA_handoff_iff_spec s sw certHash introducer exporter s').symm
            (execFullA_handoff_iff_specFull s sw certHash introducer exporter s')

/-! ## §X.tooth — the strengthening REJECTS a `delegate` tampering the weak frame could not see. -/

/-- The STRONG full-state spec REJECTS a post-state that tampers ONLY the `delegate` parent-pointer map
(an untouched field) — even though it agrees with the true output on 16 of 17 kernel fields + the log
(the near-miss the old `bal`/`accounts` projection would still accept). The `delegate` frame conjunct
catches the ghost the executor-delegating spec only avoided by accident of the helper. -/
theorem handoffSpecFull_rejects_delegate_tamper (s s' : RecChainedState) (sw certHash : Nat)
    (introducer exporter : CellId)
    (h : execFullA s (.swissHandoffA sw certHash introducer exporter) = some s')
    (badDelegate : CellId → Option CellId) (hne : badDelegate ≠ s.kernel.delegate) :
    ¬ HandoffSpecFull s sw certHash introducer exporter
        { s' with kernel := { s'.kernel with delegate := badDelegate } } := by
  -- the strong spec's `delegate` frame conjunct (`= s.kernel.delegate`) contradicts `badDelegate`.
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hdel, _⟩
  exact hne hdel

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
#assert_axioms execFullA_handoff_iff_specFull
#assert_axioms handoffSpec_iff_specFull
#assert_axioms handoffSpecFull_rejects_delegate_tamper

end Dregg2.Circuit.Spec.SwissHandoff