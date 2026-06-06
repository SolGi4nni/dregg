/-
# Dregg2.Circuit.Inst.emitEventA — the v1 (`EffectCommit`) instance for the cell-state-log effect
`emitEventA`.

`emitEventA` over `RecChainedState`: the live executor's `.emitEventA` arm dispatches to `emitStep`,
which prepends exactly one `emitReceipt` row to the log and LITERALLY freezes the entire kernel (all 17
fields, including `cell`). The `topic`/`data` payload ride the args for guard/log bookkeeping only — they
do NOT affect post-state in the spec. The INDEPENDENT bespoke apex is `EmitEventSpec` in
`Dregg2/Circuit/Spec/cellstatelog.lean`.

SPECIAL: kernel frozen, ONLY log changes:
  * `touched = ∅` (empty `Finset`) — no cell writes;
  * `expectedLeaf = fun s _ c => s.kernel.cell c` (identity; unused when `T` empty);
  * `logUpdate = some (fun s a => emitReceipt a.actor a.cell :: s.log)`;
  * `guardProp = emitGuard s a.cell` (cell ∈ accounts);
  * single `propBit` guard column (`guardWidth = 1`).

THE VALIDATION: `emitEventA_full_sound ⇒ EmitEventSpec` THROUGH the v1 framework. A satisfying
full-state witness for `emitEventE` proves the complete declarative `EmitEventSpec` by composing
`effect_circuit_full_sound` with the apex bridge (post-cell clause with `T = ∅` gives
`s'.kernel.cell = s.kernel.cell`; `kernelFrame` supplies the 16 non-`cell` fields).

ADDITIVE: imports `EffectCommit` + the cell-state-log spec; edits neither. Follows the
`incrementNonceA`/`setPermissionsA` v1 template (single `propBit` guard, And-reassoc frame bridge).

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Circuit.EffectCommit
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.cellstatelog

namespace Dregg2.Circuit.Inst.EmitEventA

open Dregg2.Circuit
open Dregg2.Circuit.EffectCommit
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.Spec.CellStateLog
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.dupNamespace false

/-! ## §0 — the single-bit guard sub-system (`propBit` at wire `0`).

The spec exposes its guard as a `Prop` (`emitGuard`), not a per-gate circuit, so we commit it as ONE
`propBit` column at wire `0` (guardWidth = 1) and decode via `propBit = 1 ↔ p`. -/

/-- The guard wire (the single `propBit` column). -/
abbrev vBitGuard : Var := 0

/-- The single guard gate: `propBit (guardProp) = 1`. -/
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

/-- `propBit p = 1 ↔ p` (the decode lemma). -/
theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-! ## §1 — the `emitEventE` instance (touched set = `∅`, log-only).

`emitEventA` over `RecChainedState`: the touched set is EMPTY (kernel frozen); the expected leaf map is
the identity (unused when `T` empty); the log GROWS by the `emitReceipt` row. -/

/-- The emit-event effect arguments: actor, target cell, topic, data. -/
structure EmitEventArgs where
  actor : CellId
  cell  : CellId
  topic : ℤ
  data  : ℤ

/-- The `StateView` for the chained executor: read the kernel and its receipt log. -/
def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The emit-event guard as a `Prop` (the spec's `emitGuard`). -/
def emitEventGuardProp (s : RecChainedState) (args : EmitEventArgs) : Prop :=
  emitGuard s args.cell

instance (s : RecChainedState) (args : EmitEventArgs) : Decidable (emitEventGuardProp s args) := by
  unfold emitEventGuardProp emitGuard; exact inferInstanceAs (Decidable (_ ∈ _))

/-- The guard's witness generator: lay the single `propBit` column at wire `0`. -/
def emitEventGuardEncode (s : RecChainedState) (args : EmitEventArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (emitEventGuardProp s args) else 0

/-- The emit-event guard sub-system: the single `propBit` gate. -/
def emitEventGuardGates : ConstraintSystem := [cBitGuard]

/-- **`emitEventGuardLocal`** — the single guard gate reads only wire `0 < 1`. -/
theorem emitEventGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied emitEventGuardGates a ↔ satisfied emitEventGuardGates b := by
  unfold satisfied emitEventGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- **`emitEventE`** — the `EffectSpec` for `emitEventA`, supplied to the v1 framework. -/
def emitEventE : EffectSpec RecChainedState EmitEventArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := some (fun s a => emitReceipt a.actor a.cell :: s.log)
  guardGates   := emitEventGuardGates
  guardProp    := emitEventGuardProp
  guardWidth   := 1
  guardEncode  := emitEventGuardEncode
  guardLocal   := emitEventGuardLocal
  guardWidth_le := by decide

/-! ### §1a — the per-effect guard obligations. -/

/-- **`GuardDecodes emitEventE`** — the single bit gate on the guard witness decodes to `emitGuard`. -/
theorem emitEventGuardDecodes : GuardDecodes emitEventE := by
  intro s args s' hsat
  change satisfied emitEventGuardGates (emitEventGuardEncode s args s') at hsat
  show emitEventGuardProp s args
  have hg := hsat cBitGuard (by simp [emitEventGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, emitEventGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

/-- **`GuardEncodes emitEventE`** — `emitGuard` encodes to the satisfied bit gate. -/
theorem emitEventGuardEncodes : GuardEncodes emitEventE := by
  intro s args s' hg
  show satisfied emitEventGuardGates (emitEventGuardEncode s args s')
  intro c hc
  simp only [emitEventGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, emitEventGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

/-! ### §1b — the apex ↔ `EmitEventSpec` bridge. -/

/-- With `T = ∅`, the framework's `touchedCellMap` is the identity on `cell` (nothing is touched, so
every cell keeps its pre-value). The post-cell clause therefore pins `s'.kernel.cell = s.kernel.cell`. -/
theorem emitEvent_touchedCellMap_eq (k : RecordKernelState) :
    touchedCellMap k.cell ∅ (fun c => k.cell c) = k.cell := by
  funext c
  unfold touchedCellMap
  rw [if_neg (Finset.notMem_empty c)]

/-- **`apex_iff_emitEventSpec`** — the framework's derived `apex` for `emitEventE` is EXACTLY
`EmitEventSpec`. The guard conjunct coincides (`emitGuard`); the post-cell clause with `T = ∅` gives
`s'.kernel.cell = s.kernel.cell`; the log clause is the `emitReceipt`-prepended chain; the 16-field
`kernelFrame` REASSOCIATES to `EmitEventSpec`'s 16 non-`cell` frame clauses (whose `bal` sits four
slots later than `kernelFrame` lists it — hence a genuine reassoc, not a defeq). -/
theorem apex_iff_emitEventSpec (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState) :
    emitEventE.apex s args s' ↔
      EmitEventSpec s args.actor args.cell args.topic args.data s' := by
  show (emitEventGuardProp s args
        ∧ s'.kernel.cell
            = touchedCellMap s.kernel.cell ∅ (fun c => s.kernel.cell c)
        ∧ s'.log = emitReceipt args.actor args.cell :: s.log
        ∧ kernelFrame s.kernel s'.kernel) ↔
      EmitEventSpec s args.actor args.cell args.topic args.data s'
  rw [emitEvent_touchedCellMap_eq]
  unfold EmitEventSpec emitEventGuardProp emitGuard kernelFrame
  constructor
  · -- kernelFrame order: accounts caps bal escrows nullifiers revoked commitments queues swiss …
    rintro ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    -- EmitEventSpec order: accounts cell caps escrows nullifiers revoked commitments bal queues swiss …
    exact ⟨hg, hlog, hAcc, hcell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
  · rintro ⟨hg, hlog, hAcc, hcell, hCaps, hEsc, hNul, hRev, hCom, hBal, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩
    exact ⟨hg, hcell, hlog, hAcc, hCaps, hBal, hEsc, hNul, hRev, hCom, hQ, hSw, hSC, hFac, hLif,
      hDC, hDel, hDgs, hSB⟩

/-! ### §1c — THE VALIDATION: `emitEventA_full_sound` through the framework. -/

/-- **`emitEventA_full_sound` — the VALIDATION (`emitEventA` through the v1 framework).** A satisfying
generic full-state witness for `emitEventE` proves the complete declarative `EmitEventSpec`. -/
theorem emitEventA_full_sound
    (S : CommitSurface)
    (hN : compressNInjective S.compressN) (hL : cellLeafInjective S.CH)
    (hRest : RestHashIffFrame S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : EmitEventArgs) (s' : RecChainedState)
    (hwf : AccountsWF s.kernel) (hwf' : AccountsWF s'.kernel)
    (h : satisfiedE S emitEventE (encodeE S emitEventE s args s')) :
    EmitEventSpec s args.actor args.cell args.topic args.data s' := by
  have hapex : emitEventE.apex s args s' :=
    effect_circuit_full_sound S emitEventE hN hL hRest hLog emitEventGuardDecodes s args s'
      hwf hwf' h
  exact (apex_iff_emitEventSpec s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire (auto-generated Wave 2). -/

def emitEventEWire : EffectSpec RecChainedState EmitEventArgs where
  view         := chainView
  touched      := fun _ _ => ∅
  expectedLeaf := fun s _ c => s.kernel.cell c
  logUpdate    := none
  guardGates   := emitEventGuardGates
  guardProp    := emitEventGuardProp
  guardWidth   := 1
  guardEncode  := emitEventGuardEncode
  guardLocal   := emitEventGuardLocal
  guardWidth_le := by decide

def emitEventAAirName : String := "dregg-emitEventA-v1"

def emitEventAEmitted : EmittedDescriptor := emittedEffect emitEventAAirName emitEventEWire

#guard emitEventAEmitted.name == emitEventAAirName

/-! ## §2 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms emitEventGuardLocal
#assert_axioms emitEventGuardDecodes
#assert_axioms emitEventGuardEncodes
#assert_axioms apex_iff_emitEventSpec
#assert_axioms emitEventA_full_sound

end Dregg2.Circuit.Inst.EmitEventA