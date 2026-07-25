/-
# Dregg2.Circuit.Inst.setProgramA — the v1 (`EffectCommit`) instance for the
  CELL-STATE-PROGRAM effect `setProgramA`.

`setProgramA` over `RecChainedState`: the live executor's `.setProgramA` arm dispatches to
`stateStep s programField actor cell (.int prog)`, which (on its three-leg admissibility guard) writes
ONLY `cell`'s `program` slot to `prog`, prepends one self-targeted receipt row to the log, and freezes
the 16 non-`cell` kernel fields. The touched set is the SINGLE target cell `{cell}`; the expected leaf
map is `setProgramCellMap`; the guard is the three-leg `setProgramGuard` (authority ∧ membership ∧
liveness).

This is the v1 analog of `Inst.SetVKA.setVKE` (SetProgram is the program-digest analog of setVK's
vk-digest — both single-slot record-pin writes, same kernel shape; `SetProgramSpec` mirrors `SetVKSpec`
clause-for-clause), specialized to the `program` slot (`programField`).

THE VALIDATION: `setProgramA_full_sound ⇒ SetProgramSpec` THROUGH the framework. A satisfying v1
full-state witness for `setProgramE` proves the complete declarative `SetProgramSpec` (the apex truth in
`Dregg2/Circuit/Spec/cellstateprogram.lean`, whose executor corner is `execFullA_setProgram_iff_spec`).

ADDITIVE: imports `EffectCommit` + the cell-state-program spec; edits NEITHER.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstateprogram

namespace Dregg2.Circuit.Inst.SetProgramA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateProgram
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit`).

The cell-state-program spec exposes its guard as a `Prop` (`setProgramGuard`), not a per-gate circuit,
so we commit it as ONE `propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `setProgramE` instance (touched set = `{cell}`). -/

/-- The set-program effect arguments: actor, target cell, new program (caveat-table digest). -/
structure SetProgramArgs where
  actor : CellId
  cell  : CellId
  prog  : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The set-program guard as a `Prop` (the spec's `setProgramGuard`). -/
def setProgramGuardProp (s : RecChainedState) (args : SetProgramArgs) : Prop :=
  setProgramGuard s args.actor args.cell

instance (s : RecChainedState) (args : SetProgramArgs) : Decidable (setProgramGuardProp s args) := by
  unfold setProgramGuardProp setProgramGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The set-program guard's witness generator: the single `propBit` column at wire `0`. -/
def setProgramGuardEncode (s : RecChainedState) (args : SetProgramArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (setProgramGuardProp s args) else 0

/-- The set-program guard sub-system: the single `propBit` gate. -/
def setProgramGuardGates : ConstraintSystem := [cBitGuard]

/-- **`setProgramGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem setProgramGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied setProgramGuardGates a ↔ satisfied setProgramGuardGates b := by
  unfold satisfied setProgramGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`setProgramE`** — the `EffectSpec` for `setProgramA`, supplied to the v1 framework. -/
def setProgramE : EffectSpec RecChainedState SetProgramArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => setProgramCellMap s.kernel args.cell args.prog
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := setProgramGuardGates
  guardProp    := setProgramGuardProp
  guardWidth   := 1
  guardEncode  := setProgramGuardEncode
  guardLocal   := setProgramGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes setProgramE`** — the single bit gate on the guard witness decodes to
`setProgramGuard`. -/
theorem setProgramGuardDecodes : GuardDecodes setProgramE := by
  rintro s args s' hsat
  change satisfied setProgramGuardGates (setProgramGuardEncode s args s') at hsat
  show setProgramGuardProp s args
  have hg := hsat cBitGuard (by simp [setProgramGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setProgramGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes setProgramE`** — `setProgramGuard` encodes to the satisfied bit gate. -/
theorem setProgramGuardEncodes : GuardEncodes setProgramE := by
  rintro s args s' hg
  show satisfied setProgramGuardGates (setProgramGuardEncode s args s')
  intro c hc
  simp only [setProgramGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, setProgramGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `SetProgramSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `setProgramCellMap` IS `setProgramCellMap`
itself: off `{cell}`, `setProgramCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}`
guard is redundant. -/
theorem setProgram_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) (prog : Int) :
    touchedCellMap k.cell {cell} (setProgramCellMap k cell prog) = setProgramCellMap k cell prog := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [setProgramCellMap, if_neg hc]

/-- **`apex_iff_setProgramSpec`** — the framework's derived `apex` for `setProgramE` is EXACTLY
`SetProgramSpec`. The guard conjunct coincides (`setProgramGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `setProgramCellMap`; the log clause is the one-row chain extension; the
16-field `kernelFrame` REASSOCIATES to `SetProgramSpec`'s 16 frame clauses (whose `bal` sits four slots
later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_setProgramSpec (s : RecChainedState) (args : SetProgramArgs) (s' : RecChainedState) :
    setProgramE.apex s args s' ↔ SetProgramSpec s args.actor args.cell args.prog s' := by
  show (setProgramGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell} (setProgramCellMap s.kernel args.cell args.prog)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ SetProgramSpec s args.actor args.cell args.prog s'
  rw [setProgram_touchedCellMap_eq]
  unfold SetProgramSpec setProgramGuardProp setProgramGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- SetProgramSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hNul, hRev, hCom, hQ, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `setProgramA_full_sound` through the framework. -/

/-- **`setProgramA_full_sound` — the VALIDATION (`setProgramA` through the framework).** A satisfying
v1 full-state witness for `setProgramE` proves the complete declarative `SetProgramSpec`. Portals:
`compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`, `logHashInjective` (the growing log
exercises `cELog` non-trivially) + `AccountsWF` on both kernels. -/
theorem setProgramA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : SetProgramArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S setProgramE (encodeE S setProgramE s args s')) :
    SetProgramSpec s args.actor args.cell args.prog s' := by
  have hapex : setProgramE.apex s args s' :=
    effect_circuit_full_sound S setProgramE hN hL hRest setProgramGuardDecodes s args s' hwf hwf'
      (Dregg2.Circuit.LogCommitRegrounded.noLogColl_of_inj hLog) h
  exact (apex_iff_setProgramSpec s args s').mp hapex

/-! ## EMISSION — Lean→Plonky3 wire. -/

def setProgramEWire : EffectSpec RecChainedState SetProgramArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := setProgramGuardGates
  guardProp    := setProgramGuardProp
  guardWidth   := 1
  guardEncode  := setProgramGuardEncode
  guardLocal   := setProgramGuardLocal
  guardWidth_le := by decide

def setProgramAAirName : String := "dregg-setProgramA-v1"

def setProgramAEmitted : EmittedDescriptor := emittedEffect setProgramAAirName setProgramEWire

#guard setProgramAEmitted.name == setProgramAAirName

/-! ## §2 — axiom-hygiene tripwires. -/

#assert_axioms setProgramGuardLocal
#assert_axioms setProgramGuardDecodes
#assert_axioms setProgramGuardEncodes
#assert_axioms apex_iff_setProgramSpec
#assert_axioms setProgramA_full_sound

end Dregg2.Circuit.Inst.SetProgramA
