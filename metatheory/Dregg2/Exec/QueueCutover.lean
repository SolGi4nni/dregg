/-
# Dregg2.Exec.QueueCutover — queue atomic-batch kernel↔chain alignment (deferred frontier close).

Connects the bare-kernel handler fold `queueAtomicTxChainK` (in `Handlers/Queue`) to the chained executor
fold `queueAtomicTxChainA` (in `TurnExecutorFull`). When the per-op chained gate bundle holds at each step
of the fold, the two folds agree on the resulting kernel — discharging the `hchain` hypothesis in
`handler_refines_execFullA_queueAtomicTx`.

Standalone: `lake build Dregg2.Exec.QueueCutover`.
-/
import Dregg2.Exec.Handlers.Queue
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.QueueCutover

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handlers.Queue
  (QueueTxOpK queueTxOpStepK queueAtomicTxChainK enqueueStep dequeueBindStep)
open Dregg2.Exec.TurnExecutorFull
  (QueueTxOpA queueTxOpStepA queueAtomicTxChainA queueEnqueueChainA queueDequeueChainA
   acceptsEffects)
open Dregg2.Exec.EffectsState (stateAuthB)

/-! ## §1 — `txOpToK`: project chained atomic sub-ops onto the bare-kernel discriminant.

The chained `QueueTxOpA` carries the queue-owner `cell` slot; the handler batch reuses the bare-kernel
enqueue/dequeue steps. Enqueue projection sets `owner := actor` (the honest park-for-self path in the
batch); dequeue drops the receipt-only `deposit`/`cell` metadata. -/

/-- Project an executor `QueueTxOpA` onto the handler's bare-kernel `QueueTxOpK` sub-op. -/
def txOpToK : QueueTxOpA → QueueTxOpK
  | .enqueue id m actor _cell depId dAsset deposit =>
      .enqueue id m actor actor depId dAsset deposit
  | .dequeue id actor _cell depId =>
      .dequeue id actor depId

/-- Project a chained atomic-batch op list onto the bare-kernel list (the `toClosedEffect` image). -/
def txOpsToK (ops : List QueueTxOpA) : List QueueTxOpK := ops.map txOpToK

/-! ## §2 — Per-op chain gate bundle (the authority/liveness/binding conjuncts `queueTxOpStepA` checks). -/

/-- The chained executor's per-op gate bundle at state `s` (the conjuncts in `queueEnqueueChainA` /
`queueDequeueChainA`). For enqueue, `actor = cell` aligns the `txOpToK` owner projection with the
chained kernel op. -/
def queueTxOpA_chainGate (s : RecChainedState) (op : QueueTxOpA) : Prop :=
  match op with
  | .enqueue id m actor cell depId dAsset deposit =>
      actor = cell ∧
      (stateAuthB s.kernel.caps actor cell = true ∧ acceptsEffects s.kernel cell = true)
  | .dequeue id actor cell depId =>
      stateAuthB s.kernel.caps actor cell = true ∧
      acceptsEffects s.kernel cell = true ∧
      dequeueBindB s.kernel actor depId = true ∧
      queueDequeueHeadB s.kernel id actor depId = true

/-- An inductive witness that the chained gate bundle holds at EVERY step of an atomic batch fold that
commits via `queueTxOpStepA`. -/
inductive QueueAtomicTxGateFold : RecChainedState → List QueueTxOpA → RecChainedState → Prop
  | nil (s : RecChainedState) : QueueAtomicTxGateFold s [] s
  | cons (s s₁ s' : RecChainedState) (op : QueueTxOpA) (rest : List QueueTxOpA)
      (hg : queueTxOpA_chainGate s op)
      (hstep : queueTxOpStepA s op = some s₁)
      (ih : QueueAtomicTxGateFold s₁ rest s') :
      QueueAtomicTxGateFold s (op :: rest) s'

/-! ## §3 — Per-op kernel agreement (the gate-commutation lemma). -/

/-- **`queueTxOpStepK_kernel_eq_of_chainGate`** — when the chained gate bundle holds and the chained
sub-op commits, the bare-kernel sub-op on `txOpToK op` reaches the SAME kernel. -/
theorem queueTxOpStepK_kernel_eq_of_chainGate {s s' : RecChainedState} {op : QueueTxOpA}
    (hg : queueTxOpA_chainGate s op)
    (hA : queueTxOpStepA s op = some s') :
    queueTxOpStepK s.kernel (txOpToK op) = some s'.kernel := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      obtain ⟨hac, ⟨hauth, hlive⟩⟩ := hg
      simp only [queueTxOpStepA, queueEnqueueChainA] at hA
      rw [if_pos ⟨hauth, hlive⟩] at hA
      cases hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit with
      | none => simp [hk] at hA
      | some k' =>
          simp only [hk, Option.some.injEq] at hA; subst hA
          simpa [queueTxOpStepK, txOpToK, enqueueStep,
            if_pos (by simpa [hac] using And.intro hauth hlive), hac] using hk
  | dequeue id actor cell depId =>
      obtain ⟨hauth, hlive, hbind, hhead⟩ := hg
      simp only [queueTxOpStepA, queueDequeueChainA] at hA
      rw [if_pos ⟨hauth, hlive, hbind, hhead⟩] at hA
      cases hk : queueDequeueRefundK s.kernel id actor depId with
      | none => simp [hk] at hA
      | some pr =>
          simp only [hk, Option.some.injEq] at hA
          obtain ⟨k', mh⟩ := pr; subst hA
          simp only [queueTxOpStepK, txOpToK, dequeueBindStep]
          rw [if_pos ⟨hbind, hhead⟩, hk, Option.map_some]

/-- **`queueTxOpStepA_of_chainGate_and_K`** — converse: when the gate bundle holds and the bare-kernel
sub-op on `txOpToK op` commits, the chained sub-op commits with the SAME kernel. -/
theorem queueTxOpStepA_of_chainGate_and_K {s : RecChainedState} {op : QueueTxOpA} {k' : RecordKernelState}
    (hg : queueTxOpA_chainGate s op)
    (hK : queueTxOpStepK s.kernel (txOpToK op) = some k') :
    ∃ s₁, queueTxOpStepA s op = some s₁ ∧ s₁.kernel = k' := by
  cases op with
  | enqueue id m actor cell depId dAsset deposit =>
      obtain ⟨hac, ⟨hauth, hlive⟩⟩ := hg
      have hk : queueEnqueueDepositK s.kernel id m actor cell depId dAsset deposit = some k' := by
        simpa [hac, queueTxOpStepK, txOpToK, enqueueStep,
          if_pos (by simpa [hac] using And.intro hauth hlive)] using hK
      refine ⟨{ kernel := k',
                log := { actor := actor, src := actor, dst := cell, amt := deposit } :: s.log },
              ?_, rfl⟩
      simp only [queueTxOpStepA, queueEnqueueChainA,
        if_pos (And.intro hauth hlive), hk]
  | dequeue id actor cell depId =>
      obtain ⟨hauth, hlive, hbind, hhead⟩ := hg
      have hgate : Dregg2.Exec.Handlers.Queue.dequeueBindB s.kernel { id := id, actor := actor, depId := depId } = true ∧
          queueDequeueHeadB s.kernel id actor depId = true := by
        dsimp [Dregg2.Exec.Handlers.Queue.dequeueBindB]; exact And.intro hbind hhead
      cases hk : queueDequeueRefundK s.kernel id actor depId with
      | none =>
          simp [queueTxOpStepK, txOpToK, dequeueBindStep, if_pos hgate, hk, Option.map_none] at hK
      | some pr =>
          obtain ⟨k₁, mh⟩ := pr
          have hEq : k₁ = k' := by
            simpa [queueTxOpStepK, txOpToK, dequeueBindStep, if_pos hgate, hk, Option.map_some] using hK
          subst hEq
          refine ⟨{ kernel := k₁,
                    log := { actor := actor, src := cell, dst := actor,
                             amt := dequeueRefundAmount s.kernel depId } :: s.log },
                  ?_, rfl⟩
          simp only [queueTxOpStepA, queueDequeueChainA,
            if_pos (And.intro hauth (And.intro hlive (And.intro hbind hhead))), hk]

/-! ## §4 — Batch-fold kernel agreement (the `queueAtomicTxChainK` ↔ `queueAtomicTxChainA` bridge). -/

/-- **`queueAtomicTxChainA_of_gateFold`** — a gate-fold witness implies the chained atomic batch
commits to the threaded end state. -/
theorem queueAtomicTxChainA_of_gateFold :
    ∀ {s s' : RecChainedState} {ops : List QueueTxOpA},
      QueueAtomicTxGateFold s ops s' → queueAtomicTxChainA s ops = some s' := by
  intro s s' ops hg
  induction hg with
  | nil => rfl
  | cons s s₁ s' op rest _ hstep _ ih_chain =>
      simp only [queueAtomicTxChainA, hstep, ih_chain]

/-- **`queueAtomicTxChainK_of_gateFold`** — under the same gate-fold witness, the bare-kernel batch on
`txOpsToK ops` reaches the SAME final kernel. -/
theorem queueAtomicTxChainK_of_gateFold :
    ∀ {s s' : RecChainedState} {ops : List QueueTxOpA},
      QueueAtomicTxGateFold s ops s' →
        queueAtomicTxChainK s.kernel (txOpsToK ops) = some s'.kernel := by
  intro s s' ops hg
  induction hg with
  | nil => rfl
  | cons s s₁ s' op rest hg_gate hstep _ ih_chain =>
      dsimp [queueAtomicTxChainK, txOpsToK]
      rw [queueTxOpStepK_kernel_eq_of_chainGate hg_gate hstep]
      exact ih_chain

/-- **`queueAtomicTxChainA_of_K_and_gateFold`** — bare-kernel batch success + gate-fold witness ⇒ chained
batch success with the same final kernel (discharges `hchain` from handler commits). -/
theorem queueAtomicTxChainA_of_K_and_gateFold {s s' : RecChainedState} {ops : List QueueTxOpA}
    (hg : QueueAtomicTxGateFold s ops s')
    (_hK : queueAtomicTxChainK s.kernel (txOpsToK ops) = some s'.kernel) :
    queueAtomicTxChainA s ops = some s' :=
  queueAtomicTxChainA_of_gateFold hg

/-- Corollary: package the `hchain` existential for `handler_refines_execFullA_queueAtomicTx`. -/
theorem queueAtomicTx_hchain_of_gateFold {s s' : RecChainedState} {ops : List QueueTxOpA}
    (hg : QueueAtomicTxGateFold s ops s') :
    ∃ s₁, queueAtomicTxChainA s ops = some s₁ ∧ s₁.kernel = s'.kernel :=
  ⟨s', queueAtomicTxChainA_of_gateFold hg, rfl⟩

/-! ## §5 — Axiom-hygiene pins. -/

#assert_axioms queueTxOpStepK_kernel_eq_of_chainGate
#assert_axioms queueTxOpStepA_of_chainGate_and_K
#assert_axioms queueAtomicTxChainA_of_gateFold
#assert_axioms queueAtomicTxChainK_of_gateFold
#assert_axioms queueAtomicTxChainA_of_K_and_gateFold

end Dregg2.Exec.QueueCutover