/-
# Dregg2.Circuit.Inst.receiptArchiveA — the v1 (`EffectCommit`) instance for the cell-state-audit
effect `receiptArchiveA`.

`receiptArchiveA` is the live executor's receipt-archive lifecycle commitment
(`stateStep s lifecycleField actor cell (.int 1)`): a SINGLE-cell `"lifecycle"` RECORD-slot write over
`RecChainedState`, a GROWING log (one self-targeted receipt row), and a frozen 16-field kernel frame.
The INDEPENDENT bespoke apex is `ReceiptArchiveSpec` in `Dregg2/Circuit/Spec/cellstateaudit.lean`.

THE VALIDATION: `receiptArchiveA_full_sound ⇒ ReceiptArchiveSpec` THROUGH the v1 framework. A satisfying
full-state witness for `receiptArchiveE` proves the complete declarative `ReceiptArchiveSpec` by composing
`effect_circuit_full_sound` with the apex bridge.

ADDITIVE: imports `EffectCommit` + the cell-state-audit spec; edits neither. Follows the `setFieldE`
template (`EffectInstances.lean`) for the touched-cell / growing-log shape, and the single-`propBit` guard
column (`mintA.lean`) for the 3-conjunct `auditGuard`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Inst.ReceiptArchiveA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The spec exposes its guard as a `Prop` (`auditGuard`), not a per-gate circuit, so we commit it as ONE
`propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical mechanism to
`mintA`; the bit gate is guard-agnostic, so the 3-conjunct `auditGuard` fits the same shape.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `receiptArchiveE` instance (touched set = `{cell}`).

`receiptArchiveA` over `RecChainedState`: the touched set is the SINGLE target cell `{cell}`, the expected
leaf map is `auditCellMap … lifecycleField`, and the log GROWS by the self-targeted receipt row. -/

/-- The receipt-archive effect arguments: actor and target cell. -/
structure ReceiptArchiveArgs where
  actor : CellId
  cell  : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The receipt-archive guard as a `Prop` (the spec's `auditGuard`). -/
def receiptArchiveGuardProp (s : RecChainedState) (args : ReceiptArchiveArgs) : Prop :=
  auditGuard s args.actor args.cell

instance (s : RecChainedState) (args : ReceiptArchiveArgs) : Decidable (receiptArchiveGuardProp s args) := by
  unfold receiptArchiveGuardProp auditGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def receiptArchiveGuardEncode (s : RecChainedState) (args : ReceiptArchiveArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (receiptArchiveGuardProp s args) else 0

/-- The receipt-archive guard sub-system: the single `propBit` gate. -/
def receiptArchiveGuardGates : ConstraintSystem := [cBitGuard]

/-- **`receiptArchiveGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem receiptArchiveGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied receiptArchiveGuardGates a ↔ satisfied receiptArchiveGuardGates b := by
  unfold satisfied receiptArchiveGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`receiptArchiveE`** — the `EffectSpec` for `receiptArchiveA`, supplied to the v1 framework. -/
def receiptArchiveE : EffectSpec RecChainedState ReceiptArchiveArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => auditCellMap s.kernel args.cell lifecycleField
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := receiptArchiveGuardGates
  guardProp    := receiptArchiveGuardProp
  guardWidth   := 1
  guardEncode  := receiptArchiveGuardEncode
  guardLocal   := receiptArchiveGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes receiptArchiveE`** — the single bit gate on the guard witness decodes to
`auditGuard`. -/
theorem receiptArchiveGuardDecodes : GuardDecodes receiptArchiveE := by
  intro s args s' hsat
  change satisfied receiptArchiveGuardGates (receiptArchiveGuardEncode s args s') at hsat
  show receiptArchiveGuardProp s args
  have hg := hsat cBitGuard (by simp [receiptArchiveGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, receiptArchiveGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes receiptArchiveE`** — `auditGuard` encodes to the satisfied bit gate. -/
theorem receiptArchiveGuardEncodes : GuardEncodes receiptArchiveE := by
  intro s args s' hg
  show satisfied receiptArchiveGuardGates (receiptArchiveGuardEncode s args s')
  intro c hc
  simp only [receiptArchiveGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, receiptArchiveGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `ReceiptArchiveSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `auditCellMap … lifecycleField` IS that map
itself: off `{cell}`, `auditCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}` guard is
redundant. The funext that makes the apex's post-cell clause equal `ReceiptArchiveSpec`'s. -/
theorem receiptArchive_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) :
    touchedCellMap k.cell {cell} (auditCellMap k cell lifecycleField) = auditCellMap k cell lifecycleField := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [auditCellMap, if_neg hc]

/-- **`apex_iff_ReceiptArchiveSpec`** — the framework's derived `apex` for `receiptArchiveE` is EXACTLY
`ReceiptArchiveSpec`. The guard conjunct coincides (`auditGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `auditCellMap … lifecycleField`; the log clause is the one-row chain
extension; the 16-field `kernelFrame` REASSOCIATES to `ReceiptArchiveSpec`'s 16 frame clauses (whose
`bal` sits four slots later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_ReceiptArchiveSpec (s : RecChainedState) (args : ReceiptArchiveArgs)
    (s' : RecChainedState) :
    receiptArchiveE.apex s args s' ↔ ReceiptArchiveSpec s args.actor args.cell s' := by
  show (receiptArchiveGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell}
                (auditCellMap s.kernel args.cell lifecycleField)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ ReceiptArchiveSpec s args.actor args.cell s'
  rw [receiptArchive_touchedCellMap_eq]
  unfold ReceiptArchiveSpec receiptArchiveGuardProp auditGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- ReceiptArchiveSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `receiptArchiveA_full_sound` through the framework. -/

/-- **`receiptArchiveA_full_sound` — the VALIDATION (`receiptArchiveA` through the v1 framework).** A
satisfying generic full-state witness for `receiptArchiveE` proves the complete declarative
`ReceiptArchiveSpec`. -/
theorem receiptArchiveA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : ReceiptArchiveArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S receiptArchiveE (encodeE S receiptArchiveE s args s')) :
    ReceiptArchiveSpec s args.actor args.cell s' := by
  have hapex : receiptArchiveE.apex s args s' :=
    effect_circuit_full_sound S receiptArchiveE hN hL hRest hLog receiptArchiveGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_ReceiptArchiveSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def receiptArchiveEWire : EffectSpec RecChainedState ReceiptArchiveArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := receiptArchiveGuardGates
  guardProp    := receiptArchiveGuardProp
  guardWidth   := 1
  guardEncode  := receiptArchiveGuardEncode
  guardLocal   := receiptArchiveGuardLocal
  guardWidth_le := by decide

def receiptArchiveAAirName : String := "dregg-receiptArchiveA-v1"

def receiptArchiveAEmitted : EmittedDescriptor := emittedEffect receiptArchiveAAirName receiptArchiveEWire

#guard receiptArchiveAEmitted.name == receiptArchiveAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms receiptArchiveGuardLocal
#assert_axioms receiptArchiveGuardDecodes
#assert_axioms receiptArchiveGuardEncodes
#assert_axioms apex_iff_ReceiptArchiveSpec
#assert_axioms receiptArchiveA_full_sound

end Dregg2.Circuit.Inst.ReceiptArchiveA