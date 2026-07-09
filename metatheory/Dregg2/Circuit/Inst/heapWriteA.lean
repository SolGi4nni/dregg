/-
# Dregg2.Circuit.Inst.heapWriteA — the v2-dual (`EffectCommit2Dual`) instance for THE HEAP write
(REFINEMENT-DESIGN Decision 1; THE ROTATION's `FullActionA.heapWriteA`).

Touches TWO components: `cell` (the `heap_root` register write at exactly `target`) and `heaps`
(the sorted `addr ↦ v` splice at exactly `target`). The guard is the `write`-verb gate stack at the
pinned `heap_root` slot (`SetFieldGuard`: caveats ∧ authority ∧ membership ∧ liveness). THE
VALIDATION: `heapWriteA_full_sound ⇒ HeapWriteSpec` (the leaf `Spec/heapwrite`, whose executor
corner is `execFullA_heapWriteA_iff_spec`) THROUGH the dual framework.

The IN-ROW digest recompute face (the cap-root gate family reuse: the address site
`addr = H[coll,key]` and the leaf site `leaf = H[addr,v]`, anti-ghost under `Poseidon2SpongeCR`)
is `Emit/EffectVmEmitHeapRoot`; THIS module is the full-state commitment instance the registry maps
`heapWriteA` to.

ADDITIVE: imports `EffectCommit2Dual` + `Spec/heapwrite`; edits neither.
-/
import Dregg2.Circuit.EffectCommit2Dual
import Dregg2.Exec.CircuitEmit
import Dregg2.Circuit.Spec.heapwrite

namespace Dregg2.Circuit.Inst.HeapWriteA

open Dregg2.Circuit
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.EffectCommit (StateView)
open Dregg2.Circuit.EffectCommit2
open Dregg2.Exec.CircuitEmit
open Dregg2.Circuit.EffectCommit2Dual
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Circuit.Spec.HeapWrite
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Substrate

set_option linter.dupNamespace false

abbrev vBitGuard : Var := 0
def cBitGuard : Constraint := { lhs := .var vBitGuard, rhs := .const 1 }

theorem propBit_eq_one {p : Prop} [Decidable p] : Circuit.propBit p = 1 ↔ p := by
  unfold Circuit.propBit; split <;> simp_all

/-- **`RestIffNoCellHeaps RH`** — the rest portal omitting the two touched components (`cell`,
`heaps`): equal rest hashes ⟺ the 14 remaining kernel fields agree (BIDIRECTIONAL). The same
realizable Poseidon-CR bar as every `RestIffNo*`. -/
def RestIffNoCellHeaps (RH : RecordKernelState → ℤ) : Prop :=
  ∀ k k' : RecordKernelState, RH k = RH k' ↔
    (k'.accounts = k.accounts ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)

/-- The heap-write arguments: actor, target, and the wire-carried digests
(`addr = H[coll,key]`, value, post-root). -/
structure HeapWriteArgs where
  actor   : CellId
  target  : CellId
  addr    : Int
  value   : Int
  newRoot : Int

def chainView : StateView RecChainedState :=
  { toKernel := (·.kernel), getLog := (·.log) }

/-- The heap-write guard: the `write`-verb gate stack at the pinned `heap_root` slot
(`SetFieldGuard` = caveats ∧ authority ∧ membership ∧ liveness). -/
def heapWriteGuardProp (s : RecChainedState) (args : HeapWriteArgs) : Prop :=
  SetFieldGuard s args.actor args.target Dregg2.Substrate.HeapKernel.heapRootField args.newRoot

instance (s : RecChainedState) (args : HeapWriteArgs) : Decidable (heapWriteGuardProp s args) := by
  unfold heapWriteGuardProp SetFieldGuard
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def heapWriteGuardEncode (s : RecChainedState) (args : HeapWriteArgs) (_s' : RecChainedState) :
    Assignment :=
  fun w => if w = vBitGuard then Circuit.propBit (heapWriteGuardProp s args) else 0

def heapWriteGuardGates : ConstraintSystem := [cBitGuard]

theorem heapWriteGuardLocal (a b : Assignment) (hab : ∀ w, w < 1 → a w = b w) :
    satisfied heapWriteGuardGates a ↔ satisfied heapWriteGuardGates b := by
  unfold satisfied heapWriteGuardGates
  have h0 := hab 0 (by decide)
  constructor <;> intro h c hc <;>
    · have hcc := h c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl
      simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, h0] at hcc ⊢
      exact hcc

/-- The `cell` component: the `heap_root` register write at `target` (the declarative
`setFieldCellMap` post map). -/
def cellComponent (D : (CellId → Value) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState HeapWriteArgs :=
  funcComponent (β := CellId → Value) (·.cell) D hD
    (fun s args => setFieldCellMap s.kernel.cell args.target
      Dregg2.Substrate.HeapKernel.heapRootField args.newRoot)

/-- The `heaps` component: the sorted `addr ↦ v` splice at `target` (the declarative
`heapWriteHeapsMap` post map). -/
def heapsComponent (D : (CellId → Heap.FeltHeap) → ℤ) (hD : Function.Injective D) :
    ActiveComponent RecChainedState HeapWriteArgs :=
  funcComponent (β := CellId → Heap.FeltHeap) (·.heaps) D hD
    (fun s args => heapWriteHeapsMap s.kernel.heaps args.target args.addr args.value)

def heapWriteE (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH) :
    EffectSpec2Dual RecChainedState HeapWriteArgs where
  view         := chainView
  active1      := cellComponent DCell hDCell
  active2      := heapsComponent DH hDH
  logUpdate    := some (fun s args =>
    { actor := args.actor, src := args.target, dst := args.target, amt := 0 } :: s.log)
  restFrame    := fun k k' =>
    (k'.accounts = k.accounts ∧ k'.caps = k.caps
      ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
      ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal
      ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories
      ∧ k'.lifecycle = k.lifecycle ∧ k'.deathCert = k.deathCert
      ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
      ∧ k'.delegationEpoch = k.delegationEpoch
      ∧ k'.delegationEpochAt = k.delegationEpochAt
      ∧ k'.nullifierRoot = k.nullifierRoot ∧ k'.revokedRoot = k.revokedRoot)
  guardGates   := heapWriteGuardGates
  guardProp    := heapWriteGuardProp
  guardWidth   := 1
  guardEncode  := heapWriteGuardEncode
  guardLocal   := heapWriteGuardLocal
  guardWidth_le := by decide

theorem heapWriteGuardDecodes (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH) :
    GuardDecodes2Dual (heapWriteE DCell hDCell DH hDH) := by
  intro s args s' hsat
  change satisfied heapWriteGuardGates (heapWriteGuardEncode s args s') at hsat
  show heapWriteGuardProp s args
  have hg := hsat cBitGuard (by simp [heapWriteGuardGates])
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, heapWriteGuardEncode, if_pos] at hg
  exact propBit_eq_one.mp hg

theorem heapWriteGuardEncodes (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH) :
    GuardEncodes2Dual (heapWriteE DCell hDCell DH hDH) := by
  intro s args s' hg
  show satisfied heapWriteGuardGates (heapWriteGuardEncode s args s')
  intro c hc
  simp only [heapWriteGuardGates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl
  simp only [Constraint.holds, cBitGuard, vBitGuard, Expr.eval, heapWriteGuardEncode, if_pos]
  exact propBit_eq_one.mpr hg

theorem heapWriteRestFrameDecodes (S : Surface2) (DCell : (CellId → Value) → ℤ)
    (hDCell : Function.Injective DCell) (DH : (CellId → Heap.FeltHeap) → ℤ)
    (hDH : Function.Injective DH) (hRest : RestIffNoCellHeaps S.RH) :
    RestFrameDecodes2Dual S (heapWriteE DCell hDCell DH hDH) := fun k k' h => (hRest k k').mp h

/-- **`apex_iff_heapWriteSpec`** — the dual framework's derived apex for `heapWriteE` is EXACTLY the
leaf `HeapWriteSpec` (a direct conjunct repack; the restFrame field order matches the leaf's). -/
theorem apex_iff_heapWriteSpec (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH)
    (s : RecChainedState) (args : HeapWriteArgs) (s' : RecChainedState) :
    (heapWriteE DCell hDCell DH hDH).apex s args s' ↔
      HeapWriteSpec s args.actor args.target args.addr args.value args.newRoot s' := by
  show (heapWriteGuardProp s args
        ∧ s'.kernel.cell = setFieldCellMap s.kernel.cell args.target
            Dregg2.Substrate.HeapKernel.heapRootField args.newRoot
        ∧ s'.kernel.heaps = heapWriteHeapsMap s.kernel.heaps args.target args.addr args.value
        ∧ s'.log = { actor := args.actor, src := args.target, dst := args.target, amt := 0 } :: s.log
        ∧ ((heapWriteE DCell hDCell DH hDH).restFrame s.kernel s'.kernel))
       ↔ HeapWriteSpec s args.actor args.target args.addr args.value args.newRoot s'
  unfold HeapWriteSpec heapWriteGuardProp heapWriteE
  constructor
  · rintro ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hDE, hDEA, hNR, hRR⟩
    exact ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hDE, hDEA, hNR, hRR⟩
  · rintro ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hDE, hDEA, hNR, hRR⟩
    exact ⟨hg, hcell, hheaps, hlog, hAcc, hCaps, hNul, hRev, hCom, hBal, hSC, hFac, hLif,
      hDC, hDel, hDgs, hDE, hDEA, hNR, hRR⟩

/-- **`heapWriteA_full_sound` — THE VALIDATION (the heap write through the dual framework).** A
satisfying v2-dual full-state witness for `heapWriteE` proves the complete declarative leaf
`HeapWriteSpec`. Portals: `RestIffNoCellHeaps RH` (the two-touched-components rest frame),
`logHashInjective LH` (the growing log), and the two injective whole-map digests (`DCell`, `DH` —
the realizable Poseidon-Merkle bar). The circuit corner of the heap-write triangle; the executor
corner is `execFullA_heapWriteA_iff_spec`. -/
theorem heapWriteA_full_sound
    (S : Surface2) (DCell : (CellId → Value) → ℤ) (hDCell : Function.Injective DCell)
    (DH : (CellId → Heap.FeltHeap) → ℤ) (hDH : Function.Injective DH)
    (hRest : RestIffNoCellHeaps S.RH) (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : HeapWriteArgs) (s' : RecChainedState)
    (h : satisfiedE2Dual S (heapWriteE DCell hDCell DH hDH)
        (encodeE2Dual S (heapWriteE DCell hDCell DH hDH) s args s')) :
    HeapWriteSpec s args.actor args.target args.addr args.value args.newRoot s' := by
  have hapex : (heapWriteE DCell hDCell DH hDH).apex s args s' :=
    effect2dual_circuit_full_sound S (heapWriteE DCell hDCell DH hDH)
      (heapWriteRestFrameDecodes S DCell hDCell DH hDH hRest) hLog
      (heapWriteGuardDecodes DCell hDCell DH hDH) s args s' h
  exact (apex_iff_heapWriteSpec DCell hDCell DH hDH s args s').mp hapex


/-! ## EMISSION — Lean→Plonky3 wire. -/

def heapWriteEWire : EffectSpec2Dual RecChainedState HeapWriteArgs where
  view         := chainView
  active1      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  active2      :=
    { digest := fun _ => 0, expected := fun _ _ => 0
    , postClause := fun _ _ _ => True
    , binds := fun _ _ _ _ => trivial, encodes := fun _ _ _ _ => rfl }
  logUpdate    := none
  restFrame    := fun _ _ => True
  guardGates   := heapWriteGuardGates
  guardProp    := heapWriteGuardProp
  guardWidth   := 1
  guardEncode  := heapWriteGuardEncode
  guardLocal   := heapWriteGuardLocal
  guardWidth_le := by decide

def heapWriteAAirName : String := "dregg-heapWriteA-v1"

def heapWriteAEmitted : EmittedDescriptor := emittedEffect2Dual heapWriteAAirName heapWriteEWire

#guard heapWriteAEmitted.name == heapWriteAAirName

#assert_axioms heapWriteGuardLocal
#assert_axioms heapWriteGuardDecodes
#assert_axioms heapWriteGuardEncodes
#assert_axioms apex_iff_heapWriteSpec
#assert_axioms heapWriteA_full_sound

end Dregg2.Circuit.Inst.HeapWriteA
