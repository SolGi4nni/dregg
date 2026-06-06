/-
# Dregg2.Circuit.Inst.setVKA — the v1 (`EffectCommit`) instance for the
  CELL-STATE-VK effect `setVKA`.

`setVKA` over `RecChainedState`: the live executor's `.setVKA` arm dispatches to
`stateStep s vkField actor cell (.int vk)`, which (on its three-leg admissibility guard) writes ONLY
`cell`'s `verification_key` slot to `vk`, prepends one self-targeted receipt row to the log, and
freezes the 16 non-`cell` kernel fields. The touched set is the SINGLE target cell `{cell}`; the
expected leaf map is `setVKCellMap`; the guard is the three-leg `setVKGuard` (authority ∧ membership ∧
liveness).

This is the v1 analog of `EffectInstances.setFieldE` (single touched cell, growing log, `touchedCellMap`
apex, And-reassoc frame bridge) with the `mintA` single-`propBit` guard column (the spec exposes its
guard as a `Prop`, not per-gate circuit bits).

THE VALIDATION: `setVKA_full_sound ⇒ SetVKSpec` THROUGH the framework. A satisfying v1 full-state
witness for `setVKE` proves the complete declarative `SetVKSpec` (the apex truth in
`Dregg2/Circuit/Spec/cellstatevk.lean`, whose executor corner is `execFullA_setVK_iff_spec`).

ADDITIVE: imports `EffectCommit` + the cell-state-vk spec; edits NEITHER. Follows
`EffectInstances.setFieldE` + the `mintA` `propBit` guard pattern + the recipe in
`Dregg2/Circuit/CONTRIBUTING.md`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Circuit.Spec.cellstatevk

namespace Dregg2.Circuit.Inst.SetVKA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateVK
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit`, copied from `mintA`).

The cell-state-vk spec exposes its guard as a `Prop` (`setVKGuard`), not a per-gate circuit, so we
commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `setVKE` instance (touched set = `{cell}`).

`setVKA` over `RecChainedState`: the touched set is the singleton `{cell}`; the expected leaf map is
`setVKCellMap`; the log GROWS by the one self-targeted receipt row; the frame is the 16 non-`cell`
kernel fields (`kernelFrame` via the apex). -/

/-- The set-VK effect arguments: actor, target cell, new verification key. -/
structure SetVKArgs where
  actor : CellId
  cell  : CellId
  vk    : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The set-VK guard as a `Prop` (the spec's `setVKGuard`). -/
def setVKGuardProp (s : RecChainedState) (args : SetVKArgs) : Prop :=
  setVKGuard s args.actor args.cell

instance (s : RecChainedState) (args : SetVKArgs) : Decidable (setVKGuardProp s args) := by
  unfold setVKGuardProp setVKGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set-VK guard's witness generator: the single `propBit` column at wire `0`. -/
def setVKGuardEncode (s : RecChainedState) (args : SetVKArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (setVKGuardProp s args) else 0

/-- The set-VK guard sub-system: the single `propBit` gate. -/
def setVKGuardGates : ConstraintSystem := [cBitGuard]

/-- **`setVKGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem setVKGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied setVKGuardGates a ↔ satisfied setVKGuardGates b := by
  unfold satisfied setVKGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`setVKE`** — the `EffectSpec` for `setVKA`, supplied to the v1 framework. -/
def setVKE : EffectSpec RecChainedState SetVKArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => setVKCellMap s.kernel args.cell args.vk
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := setVKGuardGates
  guardProp    := setVKGuardProp
  guardWidth   := 1
  guardEncode  := setVKGuardEncode
  guardLocal   := setVKGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes setVKE`** — the single bit gate on the guard witness decodes to `setVKGuard`. -/
theorem setVKGuardDecodes : GuardDecodes setVKE := by
  rintro s args s' hsat
  change satisfied setVKGuardGates (setVKGuardEncode s args s') at hsat
  show setVKGuardProp s args
  have hg := hsat cBitGuard (by simp [setVKGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setVKGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes setVKE`** — `setVKGuard` encodes to the satisfied bit gate. -/
theorem setVKGuardEncodes : GuardEncodes setVKE := by
  rintro s args s' hg
  show satisfied setVKGuardGates (setVKGuardEncode s args s')
  intro c hc
  simp only [setVKGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setVKGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `SetVKSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `setVKCellMap` IS `setVKCellMap` itself: off
`{cell}`, `setVKCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}` guard is
redundant. The funext that makes the apex's post-cell clause equal `SetVKSpec`'s. -/
theorem setVK_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) (vk : Int) :
    touchedCellMap k.cell {cell} (setVKCellMap k cell vk) = setVKCellMap k cell vk := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [setVKCellMap, if_neg hc]

/-- **`apex_iff_setVKSpec`** — the framework's derived `apex` for `setVKE` is EXACTLY `SetVKSpec`.
The guard conjunct coincides (`setVKGuard`); the post-cell clause is the `touchedCellMap` collapsed
to `setVKCellMap`; the log clause is the one-row chain extension; the 16-field `kernelFrame`
REASSOCIATES to `SetVKSpec`'s 16 frame clauses (whose `bal` sits four slots later than `kernelFrame`
lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_setVKSpec (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState) :
    setVKE.apex s args s' ↔ SetVKSpec s args.actor args.cell args.vk s' := by
  show (setVKGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell} (setVKCellMap s.kernel args.cell args.vk)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ SetVKSpec s args.actor args.cell args.vk s'
  rw [setVK_touchedCellMap_eq]
  unfold SetVKSpec setVKGuardProp setVKGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- SetVKSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `setVKA_full_sound` through the framework. -/

/-- **`setVKA_full_sound` — the VALIDATION (`setVKA` through the framework).** A satisfying v1
full-state witness for `setVKE` proves the complete declarative `SetVKSpec`. Portals:
`compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`, `logHashInjective` (the growing log
exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
theorem setVKA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetVKArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setVKE (encodeE S setVKE s args s')) :
    SetVKSpec s args.actor args.cell args.vk s' := by
  have hapex : setVKE.apex s args s' :=
    effect_circuit_full_sound S setVKE hN hL hRest hLog setVKGuardDecodes s args s' hwf hwf' h
  exact (apex_iff_setVKSpec s args s').mp hapex

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms setVKGuardLocal
#assert_axioms setVKGuardDecodes
#assert_axioms setVKGuardEncodes
#assert_axioms apex_iff_setVKSpec
#assert_axioms setVKA_full_sound

end Dregg2.Circuit.Inst.SetVKA