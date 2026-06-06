/-
# Dregg2.Circuit.Spec.swissframe — shared helpers for swiss-table effect specs.

Swiss kernel steps touch ONLY `kernel.swiss`; chained wrappers prepend a receipt to `log`.
Specs use the queue-atomic existential witness pattern so iff proofs avoid per-field destructuring.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.SwissFrame

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Auth)

/-! ## §0 — kernel extensionality + swiss-only updates preserve the frame. -/

theorem recKernel_ext {k k' : RecordKernelState}
    (h1 : k'.accounts = k.accounts) (h2 : k'.cell = k.cell) (h3 : k'.caps = k.caps)
    (h4 : k'.escrows = k.escrows) (h5 : k'.nullifiers = k.nullifiers) (h6 : k'.revoked = k.revoked)
    (h7 : k'.commitments = k.commitments) (h8 : k'.bal = k.bal) (h9 : k'.queues = k.queues)
    (h10 : k'.swiss = k.swiss) (h11 : k'.slotCaveats = k.slotCaveats)
    (h12 : k'.factories = k.factories) (h13 : k'.lifecycle = k.lifecycle)
    (h14 : k'.deathCert = k.deathCert) (h15 : k'.delegate = k.delegate)
    (h16 : k'.delegations = k.delegations) (h17 : k'.sealedBoxes = k.sealedBoxes) :
    k' = k := by
  cases k; cases k'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rfl

theorem withSwiss_preserves_rest (k : RecordKernelState) (ss : List SwissRecord) :
    let k' := { k with swiss := ss }
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
      ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.queues = k.queues
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
      ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.sealedBoxes = k.sealedBoxes := by
  dsimp
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem withSwiss_bal_accounts (k : RecordKernelState) (ss : List SwissRecord) :
    ({ k with swiss := ss }).bal = k.bal ∧
    ({ k with swiss := ss }).accounts = k.accounts := by
  rcases withSwiss_preserves_rest k ss with
    ⟨hAcc, _, _, _, _, _, _, hBal, _, _, _, _, _, _, _, _⟩
  exact ⟨hBal, hAcc⟩

theorem kernel_swiss_update_bal_accounts {k kw : RecordKernelState}
    (h : kw = { k with swiss := kw.swiss }) :
    kw.bal = k.bal ∧ kw.accounts = k.accounts := by
  rw [h]; exact withSwiss_bal_accounts k kw.swiss

/-- From `some kw = some ({ k with swiss := ss })`, the success state updates only `swiss`. -/
theorem some_withSwiss_inj {k kw : RecordKernelState} {ss : List SwissRecord}
    (h : some kw = some ({ k with swiss := ss })) :
    kw = { k with swiss := kw.swiss } := by
  have heq : kw = { k with swiss := ss } := Option.some.inj h
  have hsw : kw.swiss = ss := congr_arg (·.swiss) heq
  simpa only [hsw] using heq

theorem swissDropK_only_swiss {k kw : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some kw) : kw = { k with swiss := kw.swiss } := by
  unfold swissDropK at h
  cases hf : findSwiss k.swiss sw with
  | none => simp [hf] at h
  | some e =>
    simp only [hf] at h
    by_cases hz : e.refcount = 0
    · simp [hz] at h
    · simp only [if_neg hz] at h
      by_cases hone : e.refcount - 1 = 0
      · rw [if_pos hone] at h
        exact some_withSwiss_inj h.symm
      · rw [if_neg hone] at h
        exact some_withSwiss_inj h.symm

theorem swissHandoffK_only_swiss {k kw : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some kw) : kw = { k with swiss := kw.swiss } := by
  unfold swissHandoffK at h
  cases hf : findSwiss k.swiss sw with
  | none => simp [hf] at h
  | some e =>
    have hsome : some ({ k with swiss := replaceSwiss k.swiss sw ({ e with cert := some certHash, refcount := e.refcount + 1 }) }) = some kw := by
      simpa [swissHandoffK, hf] using h
    have heq : kw =
        { k with swiss := replaceSwiss k.swiss sw ({ e with cert := some certHash, refcount := e.refcount + 1 }) } :=
      (Option.some.inj hsome).symm
    have hsw : kw.swiss =
        replaceSwiss k.swiss sw ({ e with cert := some certHash, refcount := e.refcount + 1 }) :=
      congr_arg (·.swiss) heq
    simpa only [hsw] using heq

theorem swissEnlivenK_only_swiss {k kw : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some kw) : kw = { k with swiss := kw.swiss } := by
  unfold swissEnlivenK at h
  cases hf : findSwiss k.swiss sw with
  | none => simp [hf] at h
  | some e =>
    by_cases hr : rightsNarrowerOrEqual claimed e.rights
    · have hsome : some ({ k with swiss := replaceSwiss k.swiss sw ({ e with refcount := e.refcount + 1 }) }) = some kw := by
        simpa [swissEnlivenK, hf, hr] using h
      have heq : kw = { k with swiss := replaceSwiss k.swiss sw ({ e with refcount := e.refcount + 1 }) } :=
        (Option.some.inj hsome).symm
      have hsw : kw.swiss = replaceSwiss k.swiss sw ({ e with refcount := e.refcount + 1 }) :=
        congr_arg (·.swiss) heq
      simpa only [hsw] using heq
    · simp [swissEnlivenK, hf, hr] at h

theorem swissDropK_eq_withSwiss {k k' : RecordKernelState} {sw : Nat}
    (h : swissDropK k sw = some k') :
    swissDropK k sw = some ({ k with swiss := k'.swiss }) := by
  rw [h]
  exact congr_arg some (swissDropK_only_swiss h)

theorem swissHandoffK_eq_withSwiss {k k' : RecordKernelState} {sw certHash : Nat}
    (h : swissHandoffK k sw certHash = some k') :
    swissHandoffK k sw certHash = some ({ k with swiss := k'.swiss }) := by
  rw [h]
  exact congr_arg some (swissHandoffK_only_swiss h)

theorem swissEnlivenK_eq_withSwiss {k k' : RecordKernelState} {sw : Nat} {claimed : List Auth}
    (h : swissEnlivenK k sw claimed = some k') :
    swissEnlivenK k sw claimed = some ({ k with swiss := k'.swiss }) := by
  rw [h]
  exact congr_arg some (swissEnlivenK_only_swiss h)

#assert_axioms recKernel_ext
#assert_axioms withSwiss_preserves_rest
#assert_axioms withSwiss_bal_accounts
#assert_axioms kernel_swiss_update_bal_accounts
#assert_axioms some_withSwiss_inj
#assert_axioms swissDropK_only_swiss
#assert_axioms swissHandoffK_only_swiss
#assert_axioms swissEnlivenK_only_swiss
#assert_axioms swissDropK_eq_withSwiss
#assert_axioms swissHandoffK_eq_withSwiss
#assert_axioms swissEnlivenK_eq_withSwiss

end Dregg2.Circuit.Spec.SwissFrame