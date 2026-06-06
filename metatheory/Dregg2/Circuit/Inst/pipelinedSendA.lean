/-
# Dregg2.Circuit.Inst.pipelinedSendA — the v1 (`EffectCommit`) instance for the apply-time-neutral
`pipelinedSendA` clock tick.

`pipelinedSendA` over `RecChainedState`: the live executor's arm prepends exactly one NEUTRAL receipt
(`pipelinedSendReceipt` / `escrowReceiptA`) to the log and LITERALLY freezes the entire kernel (all 17
fields). The effect is TOTAL — no fail-closed gate at apply time. The INDEPENDENT bespoke apex is
`PipelinedSendSpec` in `Dregg2/Circuit/Spec/queuepipelinedsend.lean`.

SPECIAL: kernel frozen, ONLY log changes:
  * `touched = ∅` (empty `Finset`);
  * `expectedLeaf = fun s _ c => s.kernel.cell c` (identity; unused when `T` empty);
  * `logUpdate = some (fun s a => pipelinedSendReceipt a :: s.log)`;
  * `guardProp := True` (TOTAL — always commits).

THE VALIDATION: `pipelinedSendA_full_sound ⇒ PipelinedSendSpec` THROUGH the v1 framework.

ADDITIVE: imports `EffectCommit` + the queue-pipelined-send spec; edits neither. Follows the
`emitEventA`/`noteCreateA` v1 template (single `propBit` guard, And-reassoc frame bridge).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.queuepipelinedsend

namespace Dregg2.Circuit.Inst.PipelinedSendA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.QueuePipelinedSend
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The apply-time pipelined-send is TOTAL — `guardProp = True`. We commit it as ONE `propBit` column at
wire `0` (guardWidth = 1); `propBit True = 1` always. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `pipelinedSendE` instance (touched set = `∅`, log-only). -/

/-- The pipelined-send effect arguments: the acting principal. -/
structure PipelinedSendArgs where
  actor : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The pipelined-send guard as a `Prop` (TOTAL — always `True`). -/
def pipelinedSendGuardProp (_s : RecChainedState) (_args : PipelinedSendArgs) : Prop :=
  True

instance (s : RecChainedState) (args : PipelinedSendArgs) :
    Decidable (pipelinedSendGuardProp s args) := by
  unfold pipelinedSendGuardProp; exact inferInstanceAs (Decidable True)

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def pipelinedSendGuardEncode (s : RecChainedState) (args : PipelinedSendArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (pipelinedSendGuardProp s args) else 0

/-- The pipelined-send guard sub-system: the single `propBit` gate. -/
def pipelinedSendGuardGates : ConstraintSystem := [cBitGuard]

/-- **`pipelinedSendGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem pipelinedSendGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied pipelinedSendGuardGates a ↔ satisfied pipelinedSendGuardGates b := by
  unfold satisfied pipelinedSendGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`pipelinedSendE`** — the `EffectSpec` for `pipelinedSendA`, supplied to the v1 framework. -/
def pipelinedSendE : EffectSpec RecChainedState PipelinedSendArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := some (fun s a => pipelinedSendReceipt a.actor :: s.log)
  guardGates   := pipelinedSendGuardGates
  guardProp    := pipelinedSendGuardProp
  guardWidth   := 1
  guardEncode  := pipelinedSendGuardEncode
  guardLocal   := pipelinedSendGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes pipelinedSendE`** — the single bit gate decodes to `True`. -/
theorem pipelinedSendGuardDecodes : GuardDecodes pipelinedSendE := by
  intro s args s' hsat
  change satisfied pipelinedSendGuardGates (pipelinedSendGuardEncode s args s') at hsat
  show pipelinedSendGuardProp s args
  have hg := hsat cBitGuard (by simp [pipelinedSendGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, pipelinedSendGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes pipelinedSendE`** — `True` encodes to the satisfied bit gate. -/
theorem pipelinedSendGuardEncodes : GuardEncodes pipelinedSendE := by
  intro s args s' _hg
  show satisfied pipelinedSendGuardGates (pipelinedSendGuardEncode s args s')
  intro c hc
  simp only [pipelinedSendGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, pipelinedSendGuardEncode, if_pos]
  exact propBit_eq_one.mpr trivial

/-! ### §1b — the apex ↔ `PipelinedSendSpec` bridge. -/

/-- With `T = ∅`, the framework's `touchedCellMap` is the identity on `cell`. -/
theorem pipelinedSend_touchedCellMap_eq (k : RecordKernelState) :
    touchedCellMap k.cell ∅ (fun c => k.cell c) = k.cell := by
  funext c
  unfold touchedCellMap
  rw [if_neg (Finset.notMem_empty c)]

/-- **`apex_iff_pipelinedSendSpec`** — the framework's derived `apex` for `pipelinedSendE` is EXACTLY
`PipelinedSendSpec`. The guard is trivial (`True`); the post-cell clause with `T = ∅` gives
`s'.kernel.cell = s.kernel.cell`; the log clause is the `pipelinedSendReceipt`-prepended chain; the
16-field `kernelFrame` REASSOCIATES to `PipelinedSendSpec`'s 17 kernel-frame clauses. -/
theorem apex_iff_pipelinedSendSpec (s : RecChainedState) (args : PipelinedSendArgs)
    (s' : RecChainedState) :
    pipelinedSendE.apex s args s' ↔ PipelinedSendSpec s args.actor s' := by
  show (pipelinedSendGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell ∅ (fun c => s.kernel.cell c)
        ∧ s'.log = pipelinedSendReceipt args.actor :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔
      PipelinedSendSpec s args.actor s'
  rw [pipelinedSend_touchedCellMap_eq]
  unfold PipelinedSendSpec pipelinedSendGuardProp kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨_, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- PipelinedSendSpec order: log accounts cell caps escrows nullifiers revoked commitments bal queues …
    exact ⟨hlog, hAcc, hcell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hlog, hAcc, hcell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨trivial, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `pipelinedSendA_full_sound` through the framework. -/

/-- **`pipelinedSendA_full_sound` — the VALIDATION (`pipelinedSendA` through the v1 framework).** A
satisfying generic full-state witness for `pipelinedSendE` proves the complete declarative
`PipelinedSendSpec`. -/
theorem pipelinedSendA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : PipelinedSendArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S pipelinedSendE (encodeE S pipelinedSendE s args s')) :
    PipelinedSendSpec s args.actor s' := by
  have hapex : pipelinedSendE.apex s args s' :=
    effect_circuit_full_sound S pipelinedSendE hN hL hRest hLog pipelinedSendGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_pipelinedSendSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def pipelinedSendEWire : EffectSpec RecChainedState PipelinedSendArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := pipelinedSendGuardGates
  guardProp    := pipelinedSendGuardProp
  guardWidth   := 1
  guardEncode  := pipelinedSendGuardEncode
  guardLocal   := pipelinedSendGuardLocal
  guardWidth_le := by decide

def pipelinedSendAAirName : String := "dregg-pipelinedSendA-v1"

def pipelinedSendAEmitted : EmittedDescriptor := emittedEffect pipelinedSendAAirName pipelinedSendEWire

#guard pipelinedSendAEmitted.name == pipelinedSendAAirName

/-! ## §2 — axiom-hygiene tripwires. -/

#assert_axioms pipelinedSendGuardLocal
#assert_axioms pipelinedSendGuardDecodes
#assert_axioms pipelinedSendGuardEncodes
#assert_axioms apex_iff_pipelinedSendSpec
#assert_axioms pipelinedSendA_full_sound

end Dregg2.Circuit.Inst.PipelinedSendA