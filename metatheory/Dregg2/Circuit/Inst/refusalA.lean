/-
# Dregg2.Circuit.Inst.refusalA — the v1 (`EffectCommit`) instance for the
  CELL-STATE-AUDIT effect `refusalA`.

`refusalA` over `RecChainedState`: the live executor's `.refusalA` arm dispatches to
`stateStep s refusalField actor cell (.int 1)`, which (on its three-leg admissibility guard) writes ONLY
`cell`'s `"refusal"` audit slot to `1`, prepends one self-targeted receipt row to the log, and freezes
the 16 non-`cell` kernel fields. The touched set is the SINGLE target cell `{cell}`; the expected leaf
map is `auditCellMap … refusalField`; the guard is the three-leg `auditGuard` (authority ∧ membership ∧
liveness).

This is the v1 analog of `EffectInstances.setFieldE` (single touched cell, growing log, `touchedCellMap`
apex, And-reassoc frame bridge) with the `mintA` single-`propBit` guard column (the spec exposes its
guard as a `Prop`, not per-gate circuit bits).

THE VALIDATION: `refusalA_full_sound ⇒ RefusalSpec` THROUGH the framework. A satisfying v1 full-state
witness for `refusalE` proves the complete declarative `RefusalSpec` (the apex truth in
`Dregg2/Circuit/Spec/cellstateaudit.lean`, whose executor corner is `execFullA_refusalA_iff_spec`).

ADDITIVE: imports `EffectCommit` + the cell-state-audit spec; edits NEITHER. Follows
`EffectInstances.setFieldE` + the `mintA` `propBit` guard pattern + the recipe in
`Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Inst.RefusalA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateAudit
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit`, copied from `mintA`).

The cell-state-audit spec exposes its guard as a `Prop` (`auditGuard`), not a per-gate circuit, so we
commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `refusalE` instance (touched set = `{cell}`).

`refusalA` over `RecChainedState`: the touched set is the singleton `{cell}`; the expected leaf map is
`auditCellMap … refusalField`; the log GROWS by the one self-targeted receipt row; the frame is the 16
non-`cell` kernel fields (`kernelFrame` via the apex). -/

/-- The refusal-audit effect arguments: actor, target cell. -/
structure RefusalArgs where
  actor : CellId
  cell  : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The refusal-audit guard as a `Prop` (the spec's `auditGuard`). -/
def refusalGuardProp (s : RecChainedState) (args : RefusalArgs) : Prop :=
  auditGuard s args.actor args.cell

instance (s : RecChainedState) (args : RefusalArgs) : Decidable (refusalGuardProp s args) := by
  unfold refusalGuardProp auditGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The refusal-audit guard's witness generator: the single `propBit` column at wire `0`. -/
def refusalGuardEncode (s : RecChainedState) (args : RefusalArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (refusalGuardProp s args) else 0

/-- The refusal-audit guard sub-system: the single `propBit` gate. -/
def refusalGuardGates : ConstraintSystem := [cBitGuard]

/-- **`refusalGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem refusalGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied refusalGuardGates a ↔ satisfied refusalGuardGates b := by
  unfold satisfied refusalGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`refusalE`** — the `EffectSpec` for `refusalA`, supplied to the v1 framework. -/
def refusalE : EffectSpec RecChainedState RefusalArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args c => auditCellMap s.kernel args.cell refusalField c
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := refusalGuardGates
  guardProp    := refusalGuardProp
  guardWidth   := 1
  guardEncode  := refusalGuardEncode
  guardLocal   := refusalGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes refusalE`** — the single bit gate on the guard witness decodes to `auditGuard`. -/
theorem refusalGuardDecodes : GuardDecodes refusalE := by
  rintro s args s' hsat
  change satisfied refusalGuardGates (refusalGuardEncode s args s') at hsat
  show refusalGuardProp s args
  have hg := hsat cBitGuard (by simp [refusalGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refusalGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes refusalE`** — `auditGuard` encodes to the satisfied bit gate. -/
theorem refusalGuardEncodes : GuardEncodes refusalE := by
  rintro s args s' hg
  show satisfied refusalGuardGates (refusalGuardEncode s args s')
  intro c hc
  simp only [refusalGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, refusalGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `RefusalSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `auditCellMap … refusalField` IS that map
itself: off `{cell}`, `auditCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}` guard
is redundant. The funext that makes the apex's post-cell clause equal `RefusalSpec`'s. -/
theorem refusal_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) :
    touchedCellMap k.cell {cell} (auditCellMap k cell refusalField) =
      auditCellMap k cell refusalField := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [auditCellMap, if_neg hc]

/-- **`apex_iff_refusalSpec`** — the framework's derived `apex` for `refusalE` is EXACTLY `RefusalSpec`.
The guard conjunct coincides (`auditGuard`); the post-cell clause is the `touchedCellMap` collapsed to
`auditCellMap … refusalField`; the log clause is the one-row chain extension; the 16-field `kernelFrame`
REASSOCIATES to `RefusalSpec`'s 16 frame clauses (whose `bal` sits four slots later than `kernelFrame`
lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_refusalSpec (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState) :
    refusalE.apex s args s' ↔ RefusalSpec s args.actor args.cell s' := by
  show (refusalGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell}
                (fun c => auditCellMap s.kernel args.cell refusalField c)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ RefusalSpec s args.actor args.cell s'
  rw [refusal_touchedCellMap_eq]
  unfold RefusalSpec refusalGuardProp auditGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- RefusalSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `refusalA_full_sound` through the framework. -/

/-- **`refusalA_full_sound` — the VALIDATION (`refusalA` through the framework).** A satisfying v1
full-state witness for `refusalE` proves the complete declarative `RefusalSpec`. Portals:
`compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`, `logHashInjective` (the growing log
exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
theorem refusalA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : RefusalArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S refusalE (encodeE S refusalE s args s')) :
    RefusalSpec s args.actor args.cell s' := by
  have hapex : refusalE.apex s args s' :=
    effect_circuit_full_sound S refusalE hN hL hRest hLog refusalGuardDecodes s args s' hwf hwf' h
  exact (apex_iff_refusalSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def refusalEWire : EffectSpec RecChainedState RefusalArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := refusalGuardGates
  guardProp    := refusalGuardProp
  guardWidth   := 1
  guardEncode  := refusalGuardEncode
  guardLocal   := refusalGuardLocal
  guardWidth_le := by decide

def refusalAAirName : String := "dregg-refusalA-v1"

def refusalAEmitted : EmittedDescriptor := emittedEffect refusalAAirName refusalEWire

#guard refusalAEmitted.name == refusalAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms refusalGuardLocal
#assert_axioms refusalGuardDecodes
#assert_axioms refusalGuardEncodes
#assert_axioms apex_iff_refusalSpec
#assert_axioms refusalA_full_sound

end Dregg2.Circuit.Inst.RefusalA