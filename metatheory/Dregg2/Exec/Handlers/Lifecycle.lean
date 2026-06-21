/-
# Dregg2.Exec.Handlers.Lifecycle — the CELL-LIFECYCLE + EMIT handler batch.

The live `execFullA` arms for `cellSealA`/`cellUnsealA`/`cellDestroyA`/`refreshDelegationA`/`emitEventA`
run the proved chained steps (`cellSealChainA` &c. in `TurnExecutorFull`) — editing the `lifecycle`/
`deathCert`/`delegations` side-tables (or appending a log row for emit), NOT a named `cell` record field.

The cutover's `toClosedEffect` had routed this family through the generic `stateWriteH` at pinned field
names (`"lifecycle"`, `"delegation_refresh"`, `"event"`) — marshalling-shaped stubs that write the wrong
component. THIS batch RE-FOUNDs the real kernel steps at the handler layer so the algebra agrees with
`execFullA` AND the circuit specs (`Spec/celllifecycle`, `Spec/refreshdelegation`, `Spec/cellstatelog`).

Verified standalone: `lake build Dregg2.Exec.Handlers.Lifecycle`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Lifecycle

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull
  (acceptsEffects lcLive lcSealed lcDestroyed lcArchived setLifecycle setLifecycle_balNeutral parentClist)
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — Kernel steps mirroring the chained lifecycle arms (balance-neutral). -/

structure CellLifecycleArgs where
  actor : CellId
  cell  : CellId

structure CellDestroyArgs where
  actor     : CellId
  cell      : CellId
  certHash  : Nat

structure RefreshDelegationArgs where
  actor : CellId
  child : CellId

structure EmitEventArgs where
  actor : CellId
  cell  : CellId
  topic : Int
  data  : Int

/-- **Cell SEAL** — Live→Sealed via the `lifecycle` side-table (`setLifecycle`). -/
def cellSealStep (k : RecordKernelState) (a : CellLifecycleArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell then
    some (setLifecycle k a.cell lcSealed)
  else none

/-- **Cell UNSEAL** — Sealed→Live (only a SEALED cell may unseal). -/
def cellUnsealStep (k : RecordKernelState) (a : CellLifecycleArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && (k.lifecycle a.cell == lcSealed) then
    some (setLifecycle k a.cell lcLive)
  else none

/-- **Receipt ARCHIVE** — Live→Archived via the `lifecycle` side-table (`setLifecycle`), the deployed
`apply_receipt_archive` (`c.archive(checkpoint)`). Only a LIVE cell may be archived (`acceptsEffects`). -/
def cellArchiveStep (k : RecordKernelState) (a : CellLifecycleArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell then
    some (setLifecycle k a.cell lcArchived)
  else none

/-- **Cell DESTROY** — bind `certHash` into `deathCert` and flip to Destroyed (non-terminal only). -/
def cellDestroyStep (k : RecordKernelState) (a : CellDestroyArgs) : Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.cell && (k.lifecycle a.cell != lcDestroyed) then
    some { (setLifecycle k a.cell lcDestroyed) with
            deathCert := fun c => if c = a.cell then a.certHash else k.deathCert c }
  else none

/-- **Refresh delegation** — snapshot the parent's CURRENT c-list into `delegations child`. -/
def refreshDelegationStep (k : RecordKernelState) (a : RefreshDelegationArgs) :
    Option RecordKernelState :=
  if stateAuthB k.caps a.actor a.child && (k.delegate a.child).isSome then
    some { k with
            delegations := fun c => if c = a.child then parentClist k a.child
                                    else k.delegations c }
  else none

/-- **Emit event** — kernel-neutral log append (membership gate only; authority-free). -/
def emitEventStep (k : RecordKernelState) (a : EmitEventArgs) : Option RecordKernelState :=
  if a.cell ∈ k.accounts then some k else none

theorem cellSealStep_balNeutral {k k' : RecordKernelState} {a : CellLifecycleArgs}
    (h : cellSealStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold cellSealStep at h
  by_cases hg : stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    exact setLifecycle_balNeutral k a.cell lcSealed b
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem cellUnsealStep_balNeutral {k k' : RecordKernelState} {a : CellLifecycleArgs}
    (h : cellUnsealStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold cellUnsealStep at h
  by_cases hg : stateAuthB k.caps a.actor a.cell && (k.lifecycle a.cell == lcSealed)
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    exact setLifecycle_balNeutral k a.cell lcLive b
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem cellArchiveStep_balNeutral {k k' : RecordKernelState} {a : CellLifecycleArgs}
    (h : cellArchiveStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold cellArchiveStep at h
  by_cases hg : stateAuthB k.caps a.actor a.cell && acceptsEffects k a.cell
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    exact setLifecycle_balNeutral k a.cell lcArchived b
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem cellDestroyStep_balNeutral {k k' : RecordKernelState} {a : CellDestroyArgs}
    (h : cellDestroyStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold cellDestroyStep at h
  by_cases hg : stateAuthB k.caps a.actor a.cell && (k.lifecycle a.cell != lcDestroyed)
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset setLifecycle; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem refreshDelegationStep_balNeutral {k k' : RecordKernelState} {a : RefreshDelegationArgs}
    (h : refreshDelegationStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold refreshDelegationStep at h
  by_cases hg : stateAuthB k.caps a.actor a.child && (k.delegate a.child).isSome
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    unfold recTotalAsset parentClist; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

theorem emitEventStep_balNeutral {k k' : RecordKernelState} {a : EmitEventArgs}
    (h : emitEventStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold emitEventStep at h
  by_cases hmem : a.cell ∈ k.accounts
  · rw [if_pos hmem] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hmem] at h; exact absurd h (by simp)

/-! ## §2 — Registered handlers (the real semantics, not field-write stubs). -/

def cellSealH : EffectHandler CellLifecycleArgs where
  step := cellSealStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold cellSealStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold cellSealStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := cellSealStep_balNeutral h b
    rw [hbal]; ring

def cellArchiveH : EffectHandler CellLifecycleArgs where
  step := cellArchiveStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => acceptsEffects k a.cell
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold cellArchiveStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold cellArchiveStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && acceptsEffects s a.cell
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := cellArchiveStep_balNeutral h b
    rw [hbal]; ring

def cellUnsealH : EffectHandler CellLifecycleArgs where
  step := cellUnsealStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => k.lifecycle a.cell == lcSealed
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold cellUnsealStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && (s.lifecycle a.cell == lcSealed)
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold cellUnsealStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && (s.lifecycle a.cell == lcSealed)
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := cellUnsealStep_balNeutral h b
    rw [hbal]; ring

def cellDestroyH : EffectHandler CellDestroyArgs where
  step := cellDestroyStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.cell
  admission := fun k a => k.lifecycle a.cell != lcDestroyed
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold cellDestroyStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && (s.lifecycle a.cell != lcDestroyed)
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold cellDestroyStep at h
    by_cases hg : stateAuthB s.caps a.actor a.cell && (s.lifecycle a.cell != lcDestroyed)
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := cellDestroyStep_balNeutral h b
    rw [hbal]; ring

def refreshDelegationH : EffectHandler RefreshDelegationArgs where
  step := refreshDelegationStep
  delta := fun _ _ => 0
  auth := fun k a => stateAuthB k.caps a.actor a.child
  admission := fun k a => (k.delegate a.child).isSome
  trace := fun a => { actor := a.actor, src := a.child, dst := a.child, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold refreshDelegationStep at h
    by_cases hg : stateAuthB s.caps a.actor a.child && (s.delegate a.child).isSome
    · simp only [Bool.and_eq_true] at hg; exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold refreshDelegationStep at h
    by_cases hg : stateAuthB s.caps a.actor a.child && (s.delegate a.child).isSome
    · simp only [Bool.and_eq_true] at hg; exact hg.2
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := refreshDelegationStep_balNeutral h b
    rw [hbal]; ring

def emitEventH : EffectHandler EmitEventArgs where
  step := emitEventStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun k a => decide (a.cell ∈ k.accounts)
  trace := fun a => { actor := a.actor, src := a.cell, dst := a.cell, amt := 0 }
  auth_gated := by intro _ _ _ _; rfl
  admission_gated := by
    intro s a s' h
    unfold emitEventStep at h
    by_cases hmem : a.cell ∈ s.accounts
    · rw [if_pos hmem] at h; simp only [Option.some.injEq] at h; subst h
      simp [hmem]
    · rw [if_neg hmem] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    have hbal := emitEventStep_balNeutral h b
    rw [hbal]; ring

/-! ## §3 — Registry + `ClosedEffect` builders. -/

def lifecycleBatchRegistry : Registry :=
  [ ⟨CellLifecycleArgs, cellSealH⟩
  , ⟨CellLifecycleArgs, cellUnsealH⟩
  , ⟨CellDestroyArgs, cellDestroyH⟩
  , ⟨RefreshDelegationArgs, refreshDelegationH⟩
  , ⟨EmitEventArgs, emitEventH⟩ ]

def cellSealEffect (actor cell : CellId) : ClosedEffect :=
  { tag := 0, Args := CellLifecycleArgs, args := { actor := actor, cell := cell },
    handler := cellSealH }

def cellUnsealEffect (actor cell : CellId) : ClosedEffect :=
  { tag := 1, Args := CellLifecycleArgs, args := { actor := actor, cell := cell },
    handler := cellUnsealH }

def cellDestroyEffect (actor cell : CellId) (certHash : Nat) : ClosedEffect :=
  { tag := 2, Args := CellDestroyArgs,
    args := { actor := actor, cell := cell, certHash := certHash }, handler := cellDestroyH }

/-- The DEPLOYED receipt-archive closed effect — the `lifecycle := Archived` side-table move. -/
def cellArchiveEffect (actor cell : CellId) : ClosedEffect :=
  { tag := 5, Args := CellLifecycleArgs, args := { actor := actor, cell := cell },
    handler := cellArchiveH }

def refreshDelegationEffect (actor child : CellId) : ClosedEffect :=
  { tag := 3, Args := RefreshDelegationArgs, args := { actor := actor, child := child },
    handler := refreshDelegationH }

def emitEventEffect (actor cell : CellId) (topic data : Int) : ClosedEffect :=
  { tag := 4, Args := EmitEventArgs,
    args := { actor := actor, cell := cell, topic := topic, data := data }, handler := emitEventH }

/-! ## §4 — TEETH: lifecycle state machine + emit membership gate. -/

def lcFixture : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun c => if c = 0 then [Cap.node 0, Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0
    lifecycle := fun c => if c = 1 then lcSealed else lcLive
    delegate := fun c => if c = 1 then some 0 else none }

-- seal on Live cell 0 succeeds; seal on Sealed cell 1 fails.
#guard ((execEffect (cellSealEffect 0 0) lcFixture).isSome)  --  true
#guard ((execEffect (cellSealEffect 0 1) lcFixture).isSome) == false  --  false
-- unseal on Sealed cell 1 succeeds; unseal on Live cell 0 fails.
#guard ((execEffect (cellUnsealEffect 0 1) lcFixture).isSome)  --  true
#guard ((execEffect (cellUnsealEffect 0 0) lcFixture).isSome) == false  --  false
-- destroy on non-terminal succeeds; re-destroy after destroy fails.
#guard ((execEffect (cellDestroyEffect 0 0 42) lcFixture).isSome)  --  true
#guard (((execEffect (cellDestroyEffect 0 0 42) lcFixture).bind
         (fun k => execEffect (cellDestroyEffect 0 0 99) k)).isSome) == false  --  false
-- refresh needs a parent delegate pointer.
#guard ((execEffect (refreshDelegationEffect 1 1) lcFixture).isSome)  --  true
#guard ((execEffect (refreshDelegationEffect 0 0) lcFixture).isSome) == false  --  false
-- emit needs membership (authority-free).
#guard ((execEffect (emitEventEffect 0 0 7 42) lcFixture).isSome)  --  true
#guard ((execEffect (emitEventEffect 0 99 7 42) lcFixture).isSome) == false  --  false

#assert_axioms cellSealH
#assert_axioms cellUnsealH
#assert_axioms cellDestroyH
#assert_axioms refreshDelegationH
#assert_axioms emitEventH

end Dregg2.Exec.Handlers.Lifecycle