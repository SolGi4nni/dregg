/-
# Dregg2.Circuit.Inst.incrementNonceA — the v1 (`EffectCommit`) instance for the cell-state-monotone
effect `incrementNonceA`.

`incrementNonceA` is the live executor's monotone nonce bump (`stateStep s nonceField actor cell (.int n)`):
a SINGLE-cell `nonce` field write over `RecChainedState`, a GROWING log (one self-targeted receipt row),
and a frozen 16-field kernel frame. The INDEPENDENT bespoke apex is `IncrementNonceSpec` in
`Dregg2/Circuit/Spec/cellstatemonotone.lean`.

THE VALIDATION: `incrementNonceA_full_sound ⇒ IncrementNonceSpec` THROUGH the v1 framework. A satisfying
full-state witness for `incrementNonceE` proves the complete declarative `IncrementNonceSpec` by composing
`effect_circuit_full_sound` with the apex bridge.

ADDITIVE: imports `EffectCommit` + the cell-state-monotone spec; edits neither. Follows the `setFieldE`
template (`EffectInstances.lean`) for the touched-cell / growing-log shape, and the single-`propBit` guard
column (`mintA.lean`) for the 3-conjunct `incNonceGuard`.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstatemonotone

namespace Dregg2.Circuit.Inst.IncrementNonceA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateMonotone
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The spec exposes its guard as a `Prop` (`incNonceGuard`), not a per-gate circuit, so we commit it as ONE
`propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. (Identical mechanism to
`mintA`; the bit gate is guard-agnostic, so the 3-conjunct `incNonceGuard` fits the same shape.) -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `incrementNonceE` instance (touched set = `{cell}`).

`incrementNonceA` over `RecChainedState`: the touched set is the SINGLE target cell `{cell}`, the expected
leaf map is `incNonceCellMap`, and the log GROWS by the self-targeted receipt row. -/

/-- The increment-nonce effect arguments: actor, target cell, new nonce value. -/
structure IncrementNonceArgs where
  actor : CellId
  cell  : CellId
  n     : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The increment-nonce guard as a `Prop` (the spec's `incNonceGuard`). -/
def incrementNonceGuardProp (s : RecChainedState) (args : IncrementNonceArgs) : Prop :=
  incNonceGuard s args.actor args.cell

instance (s : RecChainedState) (args : IncrementNonceArgs) : Decidable (incrementNonceGuardProp s args) := by
  unfold incrementNonceGuardProp incNonceGuard; exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def incrementNonceGuardEncode (s : RecChainedState) (args : IncrementNonceArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (incrementNonceGuardProp s args) else 0

/-- The increment-nonce guard sub-system: the single `propBit` gate. -/
def incrementNonceGuardGates : ConstraintSystem := [cBitGuard]

/-- **`incrementNonceGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem incrementNonceGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied incrementNonceGuardGates a ↔ satisfied incrementNonceGuardGates b := by
  unfold satisfied incrementNonceGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`incrementNonceE`** — the `EffectSpec` for `incrementNonceA`, supplied to the v1 framework. -/
def incrementNonceE : EffectSpec RecChainedState IncrementNonceArgs where
  view         := chainView
  touched      := fun _ args => {args.cell}
  expectedLeaf := fun s args => incNonceCellMap s.kernel args.cell args.n
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log)
  guardGates   := incrementNonceGuardGates
  guardProp    := incrementNonceGuardProp
  guardWidth   := 1
  guardEncode  := incrementNonceGuardEncode
  guardLocal   := incrementNonceGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes incrementNonceE`** — the single bit gate on the guard witness decodes to
`incNonceGuard`. -/
theorem incrementNonceGuardDecodes : GuardDecodes incrementNonceE := by
  intro s args s' hsat
  change satisfied incrementNonceGuardGates (incrementNonceGuardEncode s args s') at hsat
  show incrementNonceGuardProp s args
  have hg := hsat cBitGuard (by simp [incrementNonceGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, incrementNonceGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes incrementNonceE`** — `incNonceGuard` encodes to the satisfied bit gate. -/
theorem incrementNonceGuardEncodes : GuardEncodes incrementNonceE := by
  intro s args s' hg
  show satisfied incrementNonceGuardGates (incrementNonceGuardEncode s args s')
  intro c hc
  simp only [incrementNonceGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, incrementNonceGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `IncrementNonceSpec` bridge. -/

/-- The framework's `touchedCellMap` over `{cell}` with `incNonceCellMap` IS `incNonceCellMap` itself:
off `{cell}`, `incNonceCellMap` is the identity (its `else` branch), so the `if c ∈ {cell}` guard is
redundant. The funext that makes the apex's post-cell clause equal `IncrementNonceSpec`'s. -/
theorem incrementNonce_touchedCellMap_eq (k : RecordKernelState) (cell : CellId) (n : Int) :
    touchedCellMap k.cell {cell} (incNonceCellMap k cell n) = incNonceCellMap k cell n := by
  funext c
  unfold touchedCellMap
  by_cases hc : c ∈ ({cell} : Finset CellId)
  · rw [if_pos hc]
  · rw [if_neg hc]
    simp only [Finset.mem_singleton] at hc
    simp only [incNonceCellMap, if_neg hc]

/-- **`apex_iff_incrementNonceSpec`** — the framework's derived `apex` for `incrementNonceE` is EXACTLY
`IncrementNonceSpec`. The guard conjunct coincides (`incNonceGuard`); the post-cell clause is the
`touchedCellMap` collapsed to `incNonceCellMap`; the log clause is the one-row chain extension; the
16-field `kernelFrame` REASSOCIATES to `IncrementNonceSpec`'s 16 frame clauses (whose `bal` sits four
slots later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_incrementNonceSpec (s : RecChainedState) (args : IncrementNonceArgs)
    (s' : RecChainedState) :
    incrementNonceE.apex s args s' ↔ IncrementNonceSpec s args.actor args.cell args.n s' := by
  show (incrementNonceGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell {args.cell}
                (incNonceCellMap s.kernel args.cell args.n)
        ∧ s'.log = { actor := args.actor, src := args.cell, dst := args.cell, amt := 0 } :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔ IncrementNonceSpec s args.actor args.cell args.n s'
  rw [incrementNonce_touchedCellMap_eq]
  unfold IncrementNonceSpec incrementNonceGuardProp kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- IncrementNonceSpec order: accounts caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hcell, hlog, hAcc, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `incrementNonceA_full_sound` through the framework. -/

/-- **`incrementNonceA_full_sound` — the VALIDATION (`incrementNonceA` through the v1 framework).** A
satisfying generic full-state witness for `incrementNonceE` proves the complete declarative
`IncrementNonceSpec`. -/
theorem incrementNonceA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IncrementNonceArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S incrementNonceE (encodeE S incrementNonceE s args s')) :
    IncrementNonceSpec s args.actor args.cell args.n s' := by
  have hapex : incrementNonceE.apex s args s' :=
    effect_circuit_full_sound S incrementNonceE hN hL hRest hLog incrementNonceGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_incrementNonceSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def incrementNonceEWire : EffectSpec RecChainedState IncrementNonceArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := incrementNonceGuardGates
  guardProp    := incrementNonceGuardProp
  guardWidth   := 1
  guardEncode  := incrementNonceGuardEncode
  guardLocal   := incrementNonceGuardLocal
  guardWidth_le := by decide

def incrementNonceAAirName : String := "dregg-incrementNonceA-v1"

def incrementNonceAEmitted : EmittedDescriptor := emittedEffect incrementNonceAAirName incrementNonceEWire

#guard incrementNonceAEmitted.name == incrementNonceAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms incrementNonceGuardLocal
#assert_axioms incrementNonceGuardDecodes
#assert_axioms incrementNonceGuardEncodes
#assert_axioms apex_iff_incrementNonceSpec
#assert_axioms incrementNonceA_full_sound

end Dregg2.Circuit.Inst.IncrementNonceA