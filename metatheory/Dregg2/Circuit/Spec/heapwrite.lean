/-
# Dregg2.Circuit.Spec.heapwrite — the FULL-STATE declarative spec of the HEAP WRITE
(REFINEMENT-DESIGN Decision 1; THE ROTATION's `FullActionA.heapWriteA` leaf).

The heap write is the `write`-verb's heap face (`Substrate.HeapKernel`): the caveat-gated write of
the carried post-root `newRoot` into the `heap_root` register PLUS the sorted insert-or-update
splice of the carried `addr ↦ v` into the target's `heaps` leaf list. The wire carries the computed
digests (`addr = H[coll, key]`, `newRoot` = the openable sorted-Poseidon2 post-root) under the cap
`slot_hash` discipline; the `(coll, key) ↦ addr` and `newRoot = root(leaves)` relations are the
circuit/cell obligations (`Emit/EffectVmEmitHeapRoot`, `circuit::heap_root`), NOT re-derived here.

The spec is INDEPENDENT and exhaustive: guard ∧ the two touched components (`cell` at exactly the
`heap_root` slot of `target`; `heaps` at exactly the `target` entry) ∧ the one-row chain extension ∧
the 14 remaining kernel fields LITERALLY unchanged. `execFullA_heapWriteA_iff_spec` is the executor
corner of the triangle, both directions.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. ADDITIVE: imports the
cell-state-field leaf (whose `SetFieldGuard`/`setFieldCellMap` the register leg reuses verbatim).
-/
import Dregg2.Circuit.Spec.cellstatefield

namespace Dregg2.Circuit.Spec.HeapWrite

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState
open Dregg2.Circuit.Spec.CellStateField
open Dregg2.Substrate

/-! ## §1 — the declarative touched-component maps. -/

/-- The declarative post-`heaps` map: the sorted insert-or-update of `addr ↦ v` at `target`,
every other cell's heap untouched (the per-cell frame, by shape). -/
def heapWriteHeapsMap (base : CellId → Heap.FeltHeap) (target : CellId) (addr v : Int) :
    CellId → Heap.FeltHeap :=
  fun c => if c = target then Heap.set (base target) addr v else base c

/-- The touched heap reads back the written value; other cells' heaps are untouched — the
declarative validation of the map (the `writeFieldCellMap_correct` analog). -/
theorem heapWriteHeapsMap_correct (base : CellId → Heap.FeltHeap) (target : CellId)
    (addr v : Int) :
    Heap.get (heapWriteHeapsMap base target addr v target) addr = some v
    ∧ (∀ c, c ≠ target → heapWriteHeapsMap base target addr v c = base c) := by
  refine ⟨?_, ?_⟩
  · simp only [heapWriteHeapsMap, if_pos]
    exact Heap.get_set_self (base target) addr v
  · intro c hc; simp only [heapWriteHeapsMap, if_neg hc]

/-! ## §2 — THE FULL-STATE DECLARATIVE SPEC (the independent reference). -/

/-- **`HeapWriteSpec` — the full-state declarative spec of a committed `heapWriteA`.** The
`SetFieldGuard` at the pinned `heap_root` slot holds (authority ∧ membership ∧ liveness ∧ the
slot's caveats admit the root write); the post `cell` map is the declarative `heap_root` register
write; the post `heaps` map is the sorted splice; the chain grows by exactly one self-targeted
row; and EVERY remaining kernel field is LITERALLY unchanged. -/
def HeapWriteSpec (s : RecChainedState) (actor target : CellId) (addr v newRoot : Int)
    (s' : RecChainedState) : Prop :=
  SetFieldGuard s actor target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  -- the THREE touched components: the register write, the heap splice, the chain extension.
  ∧ s'.kernel.cell
      = setFieldCellMap s.kernel.cell target Dregg2.Substrate.HeapKernel.heapRootField newRoot
  ∧ s'.kernel.heaps = heapWriteHeapsMap s.kernel.heaps target addr v
  ∧ s'.log = { actor := actor, src := target, dst := target, amt := 0 } :: s.log
  -- THE FRAME: the 14 remaining kernel fields, literally unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-! ## §3 — executor ⟺ spec (FULL state, both directions). -/

/-- The `heapWriteA` arm of `execFullA` is DEFINITIONALLY the wire-face guarded heap step. -/
theorem execFullA_heapWriteA_eq (s : RecChainedState) (actor target : CellId)
    (addr v newRoot : Int) :
    execFullA s (.heapWriteA actor target addr v newRoot)
      = Substrate.HeapKernel.heapStepGuardedW s actor target addr v newRoot := rfl

/-- `heapStepGuardedW` commits IFF the `SetFieldGuard` at `heap_root` holds — and then the
post-state is exactly the register write + heap splice + chain extension (the decidable seam both
directions reuse; the `stateStepGuarded_iff_guard_and_post` shape, one splice up). -/
theorem heapStepGuardedW_iff_guard_and_post (s : RecChainedState) (actor target : CellId)
    (addr v newRoot : Int) (s' : RecChainedState) :
    Substrate.HeapKernel.heapStepGuardedW s actor target addr v newRoot = some s'
      ↔ (SetFieldGuard s actor target Dregg2.Substrate.HeapKernel.heapRootField newRoot
          ∧ s' = { kernel :=
                     { writeField s.kernel Dregg2.Substrate.HeapKernel.heapRootField target
                         (.int newRoot) with
                       heaps := heapWriteHeapsMap s.kernel.heaps target addr v },
                   log := { actor := actor, src := target, dst := target, amt := 0 } :: s.log }) := by
  constructor
  · intro h
    obtain ⟨s₁, hw, hs''⟩ := Substrate.HeapKernel.heapStepGuardedW_factors h
    obtain ⟨hg, hs₁⟩ := (stateStepGuarded_iff_guard_and_post s actor target
        Dregg2.Substrate.HeapKernel.heapRootField newRoot s₁ (by decide)).mp hw
    subst hs₁
    exact ⟨hg, hs''.trans rfl⟩
  · rintro ⟨hg, hs'⟩
    have hw := (stateStepGuarded_iff_guard_and_post s actor target
        Dregg2.Substrate.HeapKernel.heapRootField newRoot
        { kernel := writeField s.kernel Dregg2.Substrate.HeapKernel.heapRootField target
                      (.int newRoot),
          log := { actor := actor, src := target, dst := target, amt := 0 } :: s.log }
        (by decide)).mpr
      ⟨hg, rfl⟩
    unfold Substrate.HeapKernel.heapStepGuardedW
    rw [hw, hs']
    rfl

/-- **`execFullA_heapWriteA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live
executor commits a `heapWriteA` into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction validates the arm against the independent spec (a silently-mutated frame field fails the
proof); the `←` reconstructs the committed state from the spec, η-style. -/
theorem execFullA_heapWriteA_iff_spec (s : RecChainedState) (actor target : CellId)
    (addr v newRoot : Int) (s' : RecChainedState) :
    execFullA s (.heapWriteA actor target addr v newRoot) = some s'
      ↔ HeapWriteSpec s actor target addr v newRoot s' := by
  rw [execFullA_heapWriteA_eq, heapStepGuardedW_iff_guard_and_post]
  constructor
  · rintro ⟨hg, hs'⟩
    subst hs'
    refine ⟨hg, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl⟩
    exact (setFieldCellMap_eq_writeField s.kernel target
      Dregg2.Substrate.HeapKernel.heapRootField newRoot).symm
  · rintro ⟨hg, hcell, hheaps, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14⟩
    refine ⟨hg, ?_⟩
    obtain ⟨k', lg'⟩ := s'
    obtain ⟨acc, cl, cps, nul, rev, cmt, bl, sc, fac, lc, dc, dg, dgs, dge, dgea, hp⟩ := k'
    simp only at hcell hheaps hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    subst hlog hheaps h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    rw [setFieldCellMap_eq_writeField] at hcell
    subst hcell
    rfl

/-! ## §4 — spec-side corollaries (the touched components read off the SPEC, not the executor). -/

/-- The touched heap address reads back the written value, off the spec. -/
theorem heapWriteSpec_writes_addr
    {s s' : RecChainedState} {actor target : CellId} {addr v newRoot : Int}
    (h : HeapWriteSpec s actor target addr v newRoot s') :
    Heap.get (s'.kernel.heaps target) addr = some v := by
  rw [h.2.2.1]
  exact (heapWriteHeapsMap_correct s.kernel.heaps target addr v).1

/-- Other cells' heaps are untouched, off the spec. -/
theorem heapWriteSpec_heap_frame
    {s s' : RecChainedState} {actor target : CellId} {addr v newRoot : Int}
    (h : HeapWriteSpec s actor target addr v newRoot s') :
    ∀ c, c ≠ target → s'.kernel.heaps c = s.kernel.heaps c := by
  intro c hc
  rw [h.2.2.1]
  exact (heapWriteHeapsMap_correct s.kernel.heaps target addr v).2 c hc

/-- The committed `heap_root` register reads back the carried `newRoot`, off the spec. -/
theorem heapWriteSpec_root_pinned
    {s s' : RecChainedState} {actor target : CellId} {addr v newRoot : Int}
    (h : HeapWriteSpec s actor target addr v newRoot s') :
    fieldOf Dregg2.Substrate.HeapKernel.heapRootField (s'.kernel.cell target) = newRoot := by
  rw [h.2.1]
  exact (writeFieldCellMap_correct s.kernel.cell target
    Dregg2.Substrate.HeapKernel.heapRootField newRoot).1

/-- Authority obligation, off the spec. -/
theorem heapWriteSpec_authorized
    {s s' : RecChainedState} {actor target : CellId} {addr v newRoot : Int}
    (h : HeapWriteSpec s actor target addr v newRoot s') :
    stateAuthB s.kernel.caps actor target = true := h.1.2.1

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms heapWriteHeapsMap_correct
#assert_axioms heapStepGuardedW_iff_guard_and_post
#assert_axioms execFullA_heapWriteA_iff_spec
#assert_axioms heapWriteSpec_writes_addr
#assert_axioms heapWriteSpec_heap_frame
#assert_axioms heapWriteSpec_root_pinned
#assert_axioms heapWriteSpec_authorized

end Dregg2.Circuit.Spec.HeapWrite
