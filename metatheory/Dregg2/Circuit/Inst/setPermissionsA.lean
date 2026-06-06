/-
# Dregg2.Circuit.Inst.setPermissionsA — the v1 (`EffectCommit`) instance for the
  CELL-STATE-PERMISSIONS effect `setPermissionsA`.

`setPermissionsA` over `RecChainedState`: the live executor's `.setPermissionsA` arm dispatches to
`stateStep s permsField actor cell (.int p)`, which (on its three-leg admissibility guard) writes ONLY
`cell`'s `permissions` slot to `p`, prepends one self-targeted receipt row to the log, and freezes
the 16 non-`cell` kernel fields. The touched set is the SINGLE target cell `{cell}`; the expected
leaf map is `setPermsCellMap`; the guard is the three-leg `setPermsGuard` (authority ∧ membership ∧
liveness).

This is the v1 analog of `EffectInstances.setFieldE` (single touched cell, growing log, `touchedCellMap`
apex, And-reassoc frame bridge) with the `mintA` single-`propBit` guard column (the spec exposes its
guard as a `Prop`, not per-gate circuit bits).

THE VALIDATION: `setPermissionsA_full_sound ⇒ SetPermissionsSpec` THROUGH the framework. A satisfying
v1 full-state witness for `setPermissionsE` proves the complete declarative `SetPermissionsSpec` (the
apex truth in `Dregg2/Circuit/Spec/cellstatepermissions.lean`, whose executor corner is
`execFullA_setPermissions_iff_spec`).

ADDITIVE: imports `EffectCommit` + the cell-state-permissions spec; edits NEITHER. Follows
`EffectInstances.setFieldE` + the `mintA` `propBit` guard pattern + the recipe in
`Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstatepermissions

namespace Dregg2.Circuit.Inst.SetPermissionsA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStatePermissions
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit`, copied from `mintA`).

The cell-state-permissions spec exposes its guard as a `Prop` (`setPermsGuard`), not a per-gate
circuit, so we commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via
`propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `setPermissionsE` instance (touched set = `{cell}`).

`setPermissionsA` over `RecChainedState`: the touched set is the singleton `{cell}`; the expected
leaf map is `setPermsCellMap`; the log GROWS by the one self-targeted receipt row; the frame is the
16 non-`cell` kernel fields (`kernelFrame` via the apex). -/

/-- The set-permissions effect arguments: actor, target cell, new permissions value. -/
structure SetPermissionsArgs where
  actor : CellId
  cell  : CellId
  p     : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The set-permissions guard as a `Prop` (the spec's `setPermsGuard`). -/
def setPermissionsGuardProp (s : RecChainedState) (args : SetPermissionsArgs) : Prop :=
  setPermsGuard s args.actor args.cell

instance (s : RecChainedState) (args : SetPermissionsArgs) : Decidable (setPermissionsGuardProp s args) := by
  unfold setPermissionsGuardProp setPermsGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set-permissions guard's witness generator: the single `propBit` column at wire `0`. -/
def setPermissionsGuardEncode (s : RecChainedState) (args : SetPermissionsArgs)
    (_s' : RecChainedState) : Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (setPermissionsGuardProp s args) else 0

/-- The set-permissions guard sub-system: the single `propBit` gate. -/
def setPermissionsGuardGates : ConstraintSystem := [cBitGuard]

/-- **`setPermissionsGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem setPermissionsGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied setPermissionsGuardGates a ↔ satisfied setPermissionsGuardGates b := by
  unfold satisfied setPermissionsGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`setPermissionsE`** — the `EffectSpec` for `setPermissionsA`, supplied to the v1 framework. -/
def setPermissionsE : EffectSpec RecChainedState SetPermissionsArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => setPermsCellMap s.kernel args.cell args.p
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := setPermissionsGuardGates
  guardProp    := setPermissionsGuardProp
  guardWidth   := 1
  guardEncode  := setPermissionsGuardEncode
  guardLocal   := setPermissionsGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes setPermissionsE`** — the single bit gate on the guard witness decodes to
`setPermsGuard`. -/
theorem setPermissionsGuardDecodes : GuardDecodes setPermissionsE := by
  rintro s args s' hsat
  change satisfied setPermissionsGuardGates (setPermissionsGuardEncode s args s') at hsat
  show setPermissionsGuardProp s args
  have hg := hsat cBitGuard (by simp [setPermissionsGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setPermissionsGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes setPermissionsE`** — `setPermsGuard` encodes to the satisfied bit gate. -/
theorem setPermissionsGuardEncodes : GuardEncodes setPermissionsE := by
  rintro s args s' hg
  show satisfied setPermissionsGuardGates (setPermissionsGuardEncode s args s')
  intro c hc
  simp only [setPermissionsGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setPermissionsGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `SetPermissionsSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `setPermsCellMap` IS `setPermsCellMap`
itself: off `{cell}`, `setPermsCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}`
guard is redundant. The funext that makes the apex's post-cell clause equal `SetPermissionsSpec`'s. -/
theorem setPermissions_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) (p : Int) :
    touchedCellMap k.cell {cell} (setPermsCellMap k cell p) = setPermsCellMap k cell p := by
  funext c
  unfold touchedCellMap setPermsCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [if_neg hc]

/-- **`apex_iff_setPermissionsSpec`** — the framework's derived `apex` for `setPermissionsE` is
EXACTLY `SetPermissionsSpec`. The guard conjunct coincides (`setPermsGuard`); the post-cell clause is
the `touchedCellMap` collapsed to `setPermsCellMap`; the log clause is the one-row chain extension;
the 16-field `kernelFrame` REASSOCIATES to `SetPermissionsSpec`'s 16 frame clauses (whose `bal` sits
four slots later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_setPermissionsSpec (s : RecChainedState) (args : SetPermissionsArgs)
    (s' : RecChainedState) :
    setPermissionsE.apex s args s' ↔ SetPermissionsSpec s args.actor args.cell args.p s' := by
  show (setPermissionsGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell}
                (setPermsCellMap s.kernel args.cell args.p)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ SetPermissionsSpec s args.actor args.cell args.p s'
  have htcm := setPermissions_touchedCellMap_eq s.kernel args.cell args.p
  rw [htcm]
  unfold SetPermissionsSpec setPermissionsGuardProp setPermsGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- SetPermissionsSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `setPermissionsA_full_sound` through the framework. -/

/-- **`setPermissionsA_full_sound` — the VALIDATION (`setPermissionsA` through the framework).** A
satisfying v1 full-state witness for `setPermissionsE` proves the complete declarative
`SetPermissionsSpec`. Portals: `compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`,
`logHashInjective` (the growing log exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
theorem setPermissionsA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetPermissionsArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setPermissionsE (encodeE S setPermissionsE s args s')) :
    SetPermissionsSpec s args.actor args.cell args.p s' := by
  have hapex : setPermissionsE.apex s args s' :=
    effect_circuit_full_sound S setPermissionsE hN hL hRest hLog setPermissionsGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_setPermissionsSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def setPermissionsEWire : EffectSpec RecChainedState SetPermissionsArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := setPermissionsGuardGates
  guardProp    := setPermissionsGuardProp
  guardWidth   := 1
  guardEncode  := setPermissionsGuardEncode
  guardLocal   := setPermissionsGuardLocal
  guardWidth_le := by decide

def setPermissionsAAirName : String := "dregg-setPermissionsA-v1"

def setPermissionsAEmitted : EmittedDescriptor := emittedEffect setPermissionsAAirName setPermissionsEWire

#guard setPermissionsAEmitted.name == setPermissionsAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms setPermissionsGuardLocal
#assert_axioms setPermissionsGuardDecodes
#assert_axioms setPermissionsGuardEncodes
#assert_axioms apex_iff_setPermissionsSpec
#assert_axioms setPermissionsA_full_sound

end Dregg2.Circuit.Inst.SetPermissionsA