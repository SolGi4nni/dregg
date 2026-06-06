/-
# Dregg2.Circuit.Inst.makeSovereignA — the v1 (`EffectCommit`) instance for the sovereign-commitment
effect `makeSovereignA`.

`makeSovereignA` over `RecChainedState`: the live executor's value-rebind step drops the target cell's
host-readable record behind a 32-byte commitment (`sovereignRebind`), prepends a self-targeted receipt
row to the log, and freezes the 16 non-`cell` kernel fields. The INDEPENDENT bespoke apex is
`MakeSovereignSpec` in `Dregg2/Circuit/Spec/sovereigncommitment.lean`.

THE VALIDATION: `makeSovereignA_full_sound ⇒ MakeSovereignSpec` THROUGH the v1 framework. A satisfying
full-state witness for `makeSovereignE` proves the complete declarative `MakeSovereignSpec` by composing
`effect_circuit_full_sound` with the apex bridge.

ADDITIVE: imports `EffectCommit` + the sovereign-commitment spec; edits neither. Follows the
`incrementNonceA` template (single touched cell, single `propBit` guard, And-reassoc frame bridge).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.sovereigncommitment

namespace Dregg2.Circuit.Inst.MakeSovereignA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.SovereignCommitment
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The spec exposes its guard as a `Prop` (`MakeSovereignGuard` — the SINGLE `stateAuthB` conjunct, NOT a
3-leg membership/lifecycle gate), not a per-gate circuit, so we commit it as ONE `propBit` column at
wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `makeSovereignE` instance (touched set = `{cell}`).

`makeSovereignA` over `RecChainedState`: the touched set is the SINGLE target cell `{cell}`, the expected
leaf map is `sovereignRebind` (commitment-only rebind at target), and the log GROWS by the
self-targeted receipt row. -/

/-- The make-sovereign effect arguments: actor and target cell. -/
structure MakeSovereignArgs where
  actor : CellId
  cell  : CellId

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The make-sovereign guard as a `Prop` (the spec's `MakeSovereignGuard`). -/
def makeSovereignGuardProp (s : RecChainedState) (args : MakeSovereignArgs) : Prop :=
  MakeSovereignGuard s args.actor args.cell

instance (s : RecChainedState) (args : MakeSovereignArgs) : Decidable (makeSovereignGuardProp s args) := by
  unfold makeSovereignGuardProp MakeSovereignGuard; exact inferInstanceAs (Decidable (_ = _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def makeSovereignGuardEncode (s : RecChainedState) (args : MakeSovereignArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (makeSovereignGuardProp s args) else 0

/-- The make-sovereign guard sub-system: the single `propBit` gate. -/
def makeSovereignGuardGates : ConstraintSystem := [cBitGuard]

/-- **`makeSovereignGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem makeSovereignGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied makeSovereignGuardGates a ↔ satisfied makeSovereignGuardGates b := by
  unfold satisfied makeSovereignGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`makeSovereignE`** — the `EffectSpec` for `makeSovereignA`, supplied to the v1 framework. -/
def makeSovereignE : EffectSpec RecChainedState MakeSovereignArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => sovereignRebind s.kernel.cell args.cell
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := makeSovereignGuardGates
  guardProp    := makeSovereignGuardProp
  guardWidth   := 1
  guardEncode  := makeSovereignGuardEncode
  guardLocal   := makeSovereignGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes makeSovereignE`** — the single bit gate on the guard witness decodes to
`MakeSovereignGuard`. -/
theorem makeSovereignGuardDecodes : GuardDecodes makeSovereignE := by
  intro s args s' hsat
  change satisfied makeSovereignGuardGates (makeSovereignGuardEncode s args s') at hsat
  show makeSovereignGuardProp s args
  have hg := hsat cBitGuard (by simp [makeSovereignGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, makeSovereignGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes makeSovereignE`** — `MakeSovereignGuard` encodes to the satisfied bit gate. -/
theorem makeSovereignGuardEncodes : GuardEncodes makeSovereignE := by
  intro s args s' hg
  show satisfied makeSovereignGuardGates (makeSovereignGuardEncode s args s')
  intro c hc
  simp only [makeSovereignGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, makeSovereignGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `MakeSovereignSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `sovereignRebind` IS `sovereignRebind` itself:
off `{cell}`, `sovereignRebind` is the identity (its `else` branch), so the `if c ∈ {cell}` guard is
redundant. The funext that makes the apex's post-cell clause equal `MakeSovereignSpec`'s. -/
theorem makeSovereign_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) :
    touchedCellMap k.cell {cell} (sovereignRebind k.cell cell) = sovereignRebind k.cell cell := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [sovereignRebind, if_neg hc]

/-- **`apex_iff_makeSovereignSpec`** — the framework's derived `apex` for `makeSovereignE` is EXACTLY
`MakeSovereignSpec`. The guard conjunct coincides (`MakeSovereignGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `sovereignRebind`; the log clause is the one-row self-targeted chain
extension; the 16-field `kernelFrame` REASSOCIATES to `MakeSovereignSpec`'s 16 frame clauses (whose
`bal` sits four slots later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_makeSovereignSpec (s : RecChainedState) (args : MakeSovereignArgs)
    (s' : RecChainedState) :
    makeSovereignE.apex s args s' ↔ MakeSovereignSpec s args.actor args.cell s' := by
  show (makeSovereignGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell}
                (sovereignRebind s.kernel.cell args.cell)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ MakeSovereignSpec s args.actor args.cell s'
  rw [makeSovereign_touchedCellMap_eq]
  unfold MakeSovereignSpec makeSovereignGuardProp kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- MakeSovereignSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `makeSovereignA_full_sound` through the framework. -/

/-- **`makeSovereignA_full_sound` — the VALIDATION (`makeSovereignA` through the v1 framework).** A
satisfying generic full-state witness for `makeSovereignE` proves the complete declarative
`MakeSovereignSpec`. -/
theorem makeSovereignA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : MakeSovereignArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S makeSovereignE (encodeE S makeSovereignE s args s')) :
    MakeSovereignSpec s args.actor args.cell s' := by
  have hapex : makeSovereignE.apex s args s' :=
    effect_circuit_full_sound S makeSovereignE hN hL hRest hLog makeSovereignGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_makeSovereignSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def makeSovereignEWire : EffectSpec RecChainedState MakeSovereignArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := makeSovereignGuardGates
  guardProp    := makeSovereignGuardProp
  guardWidth   := 1
  guardEncode  := makeSovereignGuardEncode
  guardLocal   := makeSovereignGuardLocal
  guardWidth_le := by decide

def makeSovereignAAirName : String := "dregg-makeSovereignA-v1"

def makeSovereignAEmitted : EmittedDescriptor := emittedEffect makeSovereignAAirName makeSovereignEWire

#guard makeSovereignAEmitted.name == makeSovereignAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms makeSovereignGuardLocal
#assert_axioms makeSovereignGuardDecodes
#assert_axioms makeSovereignGuardEncodes
#assert_axioms apex_iff_makeSovereignSpec
#assert_axioms makeSovereignA_full_sound

end Dregg2.Circuit.Inst.MakeSovereignA