/-
# Dregg2.Circuit.Spec.refreshdelegation — INDEPENDENT full-state spec + executor⟺spec for the Wave-3
  `refreshDelegationA` effect.

`refreshDelegationA` is self-only: the child must hold authority over itself AND have a parent
(`delegate child ≠ none`). On commit it OVERWRITES `delegations child` with a fresh snapshot of the
parent's CURRENT c-list (`parentClist`), prepends a self-targeted receipt, and frames the other 16
kernel fields. Balance-neutral.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.RefreshDelegation

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)

/-! ## §1 — guard, post-map, spec. -/

/-- The self-targeted receipt row a committed refresh prepends. -/
def refreshDelegationReceipt (actor child : CellId) : Turn :=
  { actor := actor, src := child, dst := child, amt := 0 }

/-- **The admissibility guard** for `refreshDelegationA`: self-authority AND the child has a parent. -/
def RefreshDelegationGuard (s : RecChainedState) (actor child : CellId) : Prop :=
  stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true

/-- The declarative post-`delegations` map: snapshot the parent's current c-list at `child`. -/
def refreshDelegationsMap (k : RecordKernelState) (child : CellId) : CellId → List Cap :=
  fun c => if c = child then parentClist k child else k.delegations c

/-- **The full-state declarative spec of a committed `refreshDelegationA`.** (The freshness-RESTORE
epoch re-stamp `delegationEpochAt` is a SCOPED follow-up — refresh leaves it frozen for now; see
`refreshDelegationChainA` in `TurnExecutorFull`.) -/
def RefreshDelegationSpec (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) : Prop :=
  RefreshDelegationGuard s actor child
  ∧ s'.kernel.delegations = refreshDelegationsMap s.kernel child
  ∧ s'.log = refreshDelegationReceipt actor child :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.swiss = s.kernel.swiss
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-! ## §2 — executor ⟺ spec. -/

/-- **`refreshDelegation_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** -/
theorem refreshDelegation_iff_spec (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) :
    execFullA s (.refreshDelegationA actor child) = some s'
      ↔ RefreshDelegationSpec s actor child s' := by
  unfold RefreshDelegationSpec RefreshDelegationGuard refreshDelegationsMap
  simp only [execFullA, refreshDelegationChainA, parentClist]
  by_cases hg : stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hdgs, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      obtain ⟨k', lg'⟩ := s'
      obtain ⟨acc, cellm, caps, nul, rev, com, bal, sw, sc, fac, lc, dc, dg, dgs, sb, dge, dgea⟩ := k'
      simp only at hdgs hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hdgs hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms refreshDelegation_iff_spec

end Dregg2.Circuit.Spec.RefreshDelegation