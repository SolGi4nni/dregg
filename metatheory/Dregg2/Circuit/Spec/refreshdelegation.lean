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

/-- The declarative post-`delegationEpochAt` map: re-stamp the child's epoch tag with the parent's CURRENT
`delegationEpoch` (`parentEpoch`) — the freshness-RESTORE step. -/
def refreshEpochAtMap (k : RecordKernelState) (child : CellId) : CellId → Nat :=
  fun c => if c = child then parentEpoch k child else k.delegationEpochAt c

/-- **The full-state declarative spec of a committed `refreshDelegationA`** — the deployed v1 frozen-face
descriptor's spec (`delegationEpochAt` framed UNCHANGED; consumed by `apex_iff_refreshDelegationSpec`). -/
def RefreshDelegationSpec (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) : Prop :=
  RefreshDelegationGuard s actor child
  ∧ s'.kernel.delegations = refreshDelegationsMap s.kernel child
  ∧ s'.log = refreshDelegationReceipt actor child :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
  ∧ s'.kernel.heaps = s.kernel.heaps
  ∧ s'.kernel.nullifierRoot = s.kernel.nullifierRoot
  ∧ s'.kernel.revokedRoot = s.kernel.revokedRoot

/-- **The STRENGTHENED full-state spec of a committed `refreshDelegationA`** — the EXECUTOR's faithful
face. Identical to `RefreshDelegationSpec` EXCEPT the `delegationEpochAt` clause is no longer framed
UNCHANGED: it carries the FRESHNESS-RESTORE STAMP (`refreshEpochAtMap`), re-syncing the child's epoch tag to
the parent's CURRENT epoch, so a still-authorized child is FRESH after refresh (`delegationStale child =
false`). A refresh that leaves the stamp behind FAILS this clause. -/
def RefreshDelegationFullSpec (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) : Prop :=
  RefreshDelegationGuard s actor child
  ∧ s'.kernel.delegations = refreshDelegationsMap s.kernel child
  ∧ s'.log = refreshDelegationReceipt actor child :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  -- THE FRESHNESS-RESTORE STAMP (no longer framed-unchanged):
  ∧ s'.kernel.delegationEpochAt = refreshEpochAtMap s.kernel child
  ∧ s'.kernel.heaps = s.kernel.heaps
  ∧ s'.kernel.nullifierRoot = s.kernel.nullifierRoot
  ∧ s'.kernel.revokedRoot = s.kernel.revokedRoot

/-! ## §2 — executor ⟺ spec. -/

/-- **`refreshDelegation_iff_spec` — EXECUTOR ⟺ STRENGTHENED FULL SPEC (FULL state, both directions).**
The executor commits a refresh IFF the strengthened post (with the freshness-restore epoch stamp) holds. -/
theorem refreshDelegation_iff_spec (s : RecChainedState) (actor child : CellId) (s' : RecChainedState) :
    execFullA s (.refreshDelegationA actor child) = some s'
      ↔ RefreshDelegationFullSpec s actor child s' := by
  unfold RefreshDelegationFullSpec RefreshDelegationGuard refreshDelegationsMap refreshEpochAtMap
  simp only [execFullA, refreshDelegationChainA, parentClist, parentEpoch]
  by_cases hg : stateAuthB s.kernel.caps actor child = true ∧ (s.kernel.delegate child).isSome = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · rintro ⟨_, hdgs, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      obtain ⟨k', lg'⟩ := s'
      obtain ⟨acc, cellm, caps, nul, rev, com, bal, sc, fac, lc, dc, dg, dgs, dge, dgea, hp, nr, rr⟩ := k'
      simp only at hdgs hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hdgs hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §3 — axiom-hygiene tripwires. -/

#assert_axioms refreshDelegation_iff_spec

end Dregg2.Circuit.Spec.RefreshDelegation