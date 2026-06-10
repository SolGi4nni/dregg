/-
# Dregg2.Exec.Handlers.Bridge — the bridge-batch handler file (F1b: the bridge-LFC handlers are GONE).

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler`. F1b deleted the kernel
escrow holding-store (`RecordKernelState.escrows`) and the bridge lock/finalize/cancel kernel ops
(`bridgeLockKAsset`/`bridgeFinalizeKAsset`/`bridgeCancelKAsset`) that parked into it — so the
bridge-LFC handler cluster (`bridgeLockA`/`bridgeFinalizeA`/`bridgeCancelA`, including the R12
`delta < 0` disclosed-outflow milestone and the `bridgeAuthOK` creator gate) is GONE WITH IT. The
bridge lock/finalize/cancel semantics (park, disclosed outflow, timeout refund, creator authority)
live in the proven bridge-cell contract (`Apps/BridgeCell.lean`) over factory-born cells' OWN `bal`
columns; the inbound `bridgeMintA` (the §8 portal inflow) survives in `TurnExecutorFull`.

What remains registered here:

  * **pipelinedSend** (dregg1 `apply_pipelined_send`, the apply-time NEUTRAL marker): the `EventualRef`
    resolution already ran in the pipeline; the apply-time effect is a pure CLOCK RECEIPT row — it leaves
    the kernel state LITERALLY unchanged. TOTAL (always commits), `delta = 0`, `conserves` is `rfl`-grade.

Pure, computable, `#eval`-able. Verified standalone:
`lake build Dregg2.Exec.Handlers.Bridge`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Bridge

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle)

/-! ## §4 — `pipelinedSendA`: the apply-time NEUTRAL clock receipt (TOTAL, `delta = 0`).

dregg1's `apply_pipelined_send` (`apply.rs:2657`) is a HARD ERROR if the `EventualRef` is still unresolved
— the producer fills it in the PIPELINE step, and the resolved action ALREADY ran. So the apply-time effect
is a pure CLOCK RECEIPT row: it leaves the kernel ledger state LITERALLY unchanged (in the full executor it
appends `escrowReceiptA actor` to the LOG; the LEDGER is untouched). At the kernel-state level the step is
the IDENTITY: `some k`. TOTAL (always commits — a clock row never fails), `delta = 0`, `conserves` is
`rfl`-grade (`recTotalAsset` reads `bal`, unchanged). The catalog's `Neutral`
coloring is honest here (`effectLinearity .pipelinedSend = Neutral`). -/

/-- Pipelined-send arguments: the actor whose clock receipt is emitted. -/
structure PipelinedSendArgs where
  /-- The actor the apply-time clock receipt names (the resolved action already ran). -/
  actor : CellId

/-- The pipelined-send step: the apply-time NEUTRAL marker — the kernel ledger state is unchanged. -/
def pipelinedSendStep (k : RecordKernelState) (_ : PipelinedSendArgs) : Option RecordKernelState :=
  some k

/-- **`pipelinedSendA` — the registered apply-time NEUTRAL pipelined-send handler.** TOTAL (always commits
— a clock receipt never fails); `delta = 0` (the kernel ledger state is identity); `conserves` is the
`rfl`-grade identity frame. `auth`/`admission` are default-true (the EventualRef resolution + producer
authority happened in the PIPELINE step; the apply-time row is pure book-keeping). -/
def pipelinedSendA : EffectHandler PipelinedSendArgs where
  step := pipelinedSendStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold pipelinedSendStep at h
    simp only [Option.some.injEq] at h; subst h
    ring

/-! ## §5 — The bridge batch registry (F1b: pipelined-send only).

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler`. -/

/-- The bridge batch registry (F1b: the LFC handlers live in the bridge-cell contract now). -/
def bridgeBatchRegistry : Registry :=
  [ ⟨PipelinedSendArgs, pipelinedSendA⟩ ]

/-- Build a closed pipelined-send effect (tag `0`; apply-time neutral). -/
def pipelinedSendEffect (actor : CellId) : ClosedEffect :=
  { tag := 0, Args := PipelinedSendArgs, args := { actor := actor }, handler := pipelinedSendA }

/-! ## §6 — TEETH: the apply-time NEUTRAL pipelined-send, evaluated.

(F1b: the R12 `delta < 0` lock/finalize/cancel fixtures left with the kernel holding-store — the
bridge-cell contract `Apps/BridgeCell.lean` carries the disclosed-outflow + creator-gate teeth now.) -/

/-- The base fixture: cells 0,1 accounts; cell 0 holds 100 of asset 1; cell 0 holds a `node 1` self-cap;
both Live. -/
def br0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

-- §TEETH (PIPELINED-SEND total + neutral): always commits, leaves the per-asset measure unchanged.
#guard ((execEffect (pipelinedSendEffect 0) br0).map (fun k => recTotalAsset k 1)) == some 100  --  some 100
#guard (turnDelta [pipelinedSendEffect 0] 1) == 0  --  0

/-! ## §7 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs), and the
lock-authority helper is pinned directly. A `sorryAx` anywhere in the composed lemmas fails the pin AND the
build — so these pins certify that bridge lock/finalize/cancel/pipelined-send soundness (including the
`delta < 0` finalize accounting) rests only on the kernel triple. -/

#assert_axioms pipelinedSendA

/-! ## §DEFER — scope of this batch.

F1b: the §8 confirmation-receipt portal, the bridge TIMEOUT gate, and the relayer-finalize path all
moved WITH the lock/finalize/cancel semantics into the bridge-cell contract (`Apps/BridgeCell.lean`);
the inbound `bridgeMintA` portal stays in `TurnExecutorFull`. The only handler registered here is the
apply-time-neutral `pipelinedSendA` (the EventualRef resolution + producer authority happened in the
PIPELINE step; the apply-time row is pure book-keeping).
-/

end Dregg2.Exec.Handlers.Bridge
