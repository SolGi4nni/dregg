/-
# Dregg2.Circuit.FloorsNonVacuousWaveMiscNotes — the MISC/NOTES/HEAP `*TraceReadout` carriers are
  NON-VACUOUS.

Companion to `FloorsNonVacuousWave` (the `CellSealTraceReadout` template) and
`FloorsNonVacuousWaveLifecycle`. Each of the five Class-A refinement rungs
(`makeSovereign`/`setFieldDyn`/`noteSpend`/`noteCreate`/`heapWrite` `_descriptorRefines_sat`) takes a
`<E>TraceReadout` as a PREMISE; a secretly-uninhabitable premise makes its consuming rung VACUOUSLY
satisfiable. This module exhibits a CONCRETE inhabiting term per readout (a two-row trace whose
designated active row carries the selector hot + the committed limb the decode-seam reads, a
near-`pre = post` boundary so every untouched frame field is `rfl`, and the guard discharged at a
self-targeted live cell), so each `<E>TraceReadout` is `Nonempty` and its rung is NON-vacuous.

Per readout the decode seam is realized by setting the kernel field to the value the chosen column
carries — exactly the trace-fill identity the deployed prover establishes by construction:
  * `makeSovereign` — the committed AFTER mode limb is `1` and `post.cell := sovereignRebind pre.cell cell`
    (the `if`-indicator is then `1`, matching the limb);
  * `setFieldDyn` — the AFTER `fields_root` limb and the declared-param column are both `0` (`v := 0`),
    and `post.cell := setFieldCellMap pre.cell cell f 0` reads slot `f` back as `0`;
  * `noteSpend`/`noteCreate` — `growthDecodes` is an IMPLICATION whose conclusion is satisfied by
    `post.nullifiers := nf :: pre.nullifiers` / `post.commitments := cm :: pre.commitments`, so the
    field is `fun _ => rfl`;
  * `heapWrite` — `newRoot := 0` is the AFTER register column (`= 0`), `post.cell`/`post.heaps` are
    the required maps.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every inhabitation is a CONSTRUCTED term;
no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuousWave
import Dregg2.Circuit.RotatedKernelRefinementMisc
import Dregg2.Circuit.RotatedKernelRefinementNotes
import Dregg2.Circuit.RotatedKernelRefinementExercise

namespace Dregg2.Circuit.FloorsNonVacuousWaveMiscNotes

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt zeroAsg)
open Dregg2.Circuit.FloorsNonVacuous (permOutZ)
open Dregg2.Circuit.FloorsNonVacuousWave (readoutTrace readoutTrace_rows_len readoutTrace_loc0)
open Dregg2.Circuit.RotatedKernelRefinementMisc
open Dregg2.Circuit.RotatedKernelRefinementNotes
open Dregg2.Circuit.RotatedKernelRefinementExercise
open Dregg2.Exec (RecChainedState CellId FieldName Value)
open Dregg2.Exec.TurnExecutorFull (sovereignRebind escrowReceiptA)
open Dregg2.Circuit.Spec.CellStateField (setFieldCellMap)
open Dregg2.Circuit.Spec.HeapWrite (heapWriteHeapsMap)
open Dregg2.Substrate.HeapKernel (heapRootField)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (setFieldDynV1Face)

/-! ## §1 — `MakeSovereignTraceReadout` INHABITED.

The active row 0 carries `SEL_MAKE_SOVEREIGN_RT = 1` and the AFTER mode limb (`afterModeCol … = 274`)
carries `1`. The boundary sets `post.cell := sovereignRebind pre.cell cell`, so the `modeLimbDecodes`
indicator `(if post.cell = sovereignRebind pre.cell cell then 1 else 0)` is `1`, matching the limb. The
guard is ONLY self-authority (`MakeSovereignGuard`, no membership / no lifecycle). `actor = cell = 0`. -/

open Dregg2.Circuit.Emit.EffectVmEmitMakeSovereign (SEL_MAKE_SOVEREIGN_RT makeSovereignRuntimeVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (afterModeCol)

/-- The active row for makeSovereign: hot at `SEL_MAKE_SOVEREIGN_RT (= 12)`; the AFTER mode limb
(`afterModeCol … = 274 ≠ 12`) reads `1` (the sovereign-rebind indicator). -/
def makeSovRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_MAKE_SOVEREIGN_RT then 1
           else if c = afterModeCol makeSovereignRuntimeVmDescriptor.traceWidth then 1 else 0

def makeSovPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: the whole `cell`-map rebind (`sovereignRebind`) + the self-targeted receipt advance. -/
def makeSovPost : RecChainedState :=
  { kernel := { makeSovPre.kernel with cell := sovereignRebind makeSovPre.kernel.cell 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: makeSovPre.log }

/-- **`MakeSovereignTraceReadout` is INHABITED.** -/
def makeSov_readout :
    MakeSovereignTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace makeSovRow0) makeSovPre makeSovPost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [makeSovRow0]
  modeLimbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterModeCol makeSovereignRuntimeVmDescriptor.traceWidth = SEL_MAKE_SOVEREIGN_RT)
        = False := by decide
    have hmove : makeSovPost.kernel.cell = sovereignRebind makeSovPre.kernel.cell 0 := rfl
    simp only [makeSovRow0, hcol, if_false, if_pos hmove]
    rfl
  guard := by
    show Dregg2.Exec.EffectsState.stateAuthB _ 0 0 = true
      ∧ Dregg2.Exec.TurnExecutorFull.acceptsEffects _ 0 = true
    exact ⟨by decide, by decide⟩
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem makeSov_readout_inhabited :
    Nonempty (MakeSovereignTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace makeSovRow0) makeSovPre makeSovPost 0 0) :=
  ⟨makeSov_readout⟩

#assert_axioms makeSov_readout

/-! ## §2 — `SetFieldDynTraceReadout` INHABITED.

The active row 0 carries `SEL_SET_FIELD = 1`; the AFTER `fields_root` limb (`= 275`) and the
declared-param column (`= 188`) both read `0`. With `f := "x"`, `v := 0`, the boundary sets
`post.cell := setFieldCellMap pre.cell cell "x" 0`, which reads slot `"x"` back as `0` — matching the
AFTER limb. The guard discharges at the live account `0` (empty caveats admit; `actor = cell = 0`
self-authority; `0 ∈ {0}`; lifecycle Live). -/

open Dregg2.Circuit.Emit.EffectVmEmitSetField (SEL_SET_FIELD)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (afterFieldsRootCol declaredFieldsRootCol)

/-- The active row for setFieldDyn: hot at `SEL_SET_FIELD (= 2)`; the AFTER `fields_root` limb and the
declared-param column read `0` (the default). -/
def setFieldRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_SET_FIELD then 1 else 0

def setFieldPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: the whole `cell`-map move (`setFieldCellMap … "x" 0`) + the self-targeted receipt advance. -/
def setFieldPost : RecChainedState :=
  { kernel := { setFieldPre.kernel with cell := setFieldCellMap setFieldPre.kernel.cell 0 "x" 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: setFieldPre.log }

/-- **`SetFieldDynTraceReadout` is INHABITED.** (`f := "x"`, `v := 0`.) -/
def setField_readout :
    SetFieldDynTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace setFieldRow0) setFieldPre setFieldPost 0 0 "x" 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [setFieldRow0]
  fieldsLimbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterFieldsRootCol setFieldDynV1Face.traceWidth = SEL_SET_FIELD) = False := by decide
    simp only [setFieldRow0, hcol, if_false, setFieldPost, setFieldPre]
    rfl
  paramDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (declaredFieldsRootCol = SEL_SET_FIELD) = False := by decide
    simp only [setFieldRow0, hcol, if_false]
  cellMapMove := rfl
  guard := by refine ⟨by decide, by decide, by decide, by decide⟩
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem setField_readout_inhabited :
    Nonempty (SetFieldDynTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace setFieldRow0) setFieldPre setFieldPost 0 0 "x" 0) :=
  ⟨setField_readout⟩

#assert_axioms setField_readout

/-! ## §3 — `NoteSpendTraceReadout` INHABITED.

The active row 0 carries `SEL_NOTE_SPEND = 1`. `growthDecodes` is an IMPLICATION whose conclusion is
`post.nullifiers = nf :: pre.nullifiers`; we set `post.nullifiers := nf :: pre.nullifiers` so the
conclusion holds unconditionally (`fun _ => rfl`). `freshness : nf ∉ pre.nullifiers` holds because
`pre.nullifiers = []` (any `nf`, here `nf := 0`). `proof : spendProof = true` with `spendProof := true`.
`post` differs from `pre` only on `nullifiers` (and the log). -/

open Dregg2.Circuit.Emit.EffectVmEmitNoteSpend (SEL_NOTE_SPEND)

def noteSpendRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_NOTE_SPEND then 1 else 0

def noteSpendPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: nullifier set-insert (`0 :: []`) + the noteSpend receipt advance. -/
def noteSpendPost : RecChainedState :=
  { kernel := { noteSpendPre.kernel with nullifiers := 0 :: noteSpendPre.kernel.nullifiers },
    log := escrowReceiptA 0 :: noteSpendPre.log }

/-- **`NoteSpendTraceReadout` is INHABITED.** (`nf := 0`, `actor := 0`, `spendProof := true`.) -/
def noteSpend_readout :
    NoteSpendTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace noteSpendRow0) noteSpendPre noteSpendPost 0 0 true where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [noteSpendRow0]
  growthDecodes := fun _ => rfl
  freshness := by decide
  proof := rfl
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem noteSpend_readout_inhabited :
    Nonempty (NoteSpendTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace noteSpendRow0) noteSpendPre noteSpendPost 0 0 true) :=
  ⟨noteSpend_readout⟩

#assert_axioms noteSpend_readout

/-! ## §4 — `NoteCreateTraceReadout` INHABITED.

Like noteSpend: the active row 0 carries `SEL_NOTE_CREATE = 1`; `growthDecodes` is an IMPLICATION whose
conclusion is `post.commitments = cm :: pre.commitments`, satisfied by `post.commitments := cm ::
pre.commitments` (`fun _ => rfl`). No guard, no freshness. `post` differs from `pre` only on
`commitments` (and the log). -/

open Dregg2.Circuit.Emit.EffectVmEmitNoteCreate (SEL_NOTE_CREATE)

def noteCreateRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_NOTE_CREATE then 1 else 0

def noteCreatePre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: commitment set-insert (`0 :: []`) + the noteCreate receipt advance. -/
def noteCreatePost : RecChainedState :=
  { kernel := { noteCreatePre.kernel with commitments := 0 :: noteCreatePre.kernel.commitments },
    log := escrowReceiptA 0 :: noteCreatePre.log }

/-- **`NoteCreateTraceReadout` is INHABITED.** (`cm := 0`, `actor := 0`.) -/
def noteCreate_readout :
    NoteCreateTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace noteCreateRow0) noteCreatePre noteCreatePost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [noteCreateRow0]
  growthDecodes := fun _ => rfl
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem noteCreate_readout_inhabited :
    Nonempty (NoteCreateTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      (readoutTrace noteCreateRow0) noteCreatePre noteCreatePost 0 0) :=
  ⟨noteCreate_readout⟩

#assert_axioms noteCreate_readout

/-! ## §5 — `HeapWriteTraceReadout` INHABITED.

The active row 0 reads `HEAP_ROOT_AFTER (= 87)` as `0` (the default), so `newRoot := 0 = (envAt t row).loc
HEAP_ROOT_AFTER`. The boundary sets `post.cell := setFieldCellMap pre.cell target heapRootField 0` and
`post.heaps := heapWriteHeapsMap pre.heaps target 0 0`. The guard is `SetFieldGuard pre actor target
heapRootField 0` at the live account `0` (`actor = target = 0`, `addr := 0`, `v := 0`). -/

open Dregg2.Circuit.Emit.EffectVmEmitHeapRoot (HEAP_ROOT_AFTER)

/-- The active row for heapWrite: `HEAP_ROOT_AFTER (= 87)` reads `0` (the default), so the carried
`newRoot := 0` IS that column. -/
def heapWriteRow0 : Dregg2.Circuit.Assignment := fun _ => 0

def heapWritePre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: the `heap_root` register write (`setFieldCellMap … heapRootField 0`) + the heap splice
(`heapWriteHeapsMap … 0 0`) + the self-targeted receipt advance. -/
def heapWritePost : RecChainedState :=
  { kernel := { heapWritePre.kernel with
      cell := setFieldCellMap heapWritePre.kernel.cell 0 heapRootField 0,
      heaps := heapWriteHeapsMap heapWritePre.kernel.heaps 0 0 0 },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: heapWritePre.log }

/-- **`HeapWriteTraceReadout` is INHABITED.** (`actor := target := 0`, `addr := v := newRoot := 0`.) -/
def heapWrite_readout :
    HeapWriteTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace heapWriteRow0) heapWritePre heapWritePost 0 0 0 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  newRootIsAfter := by rw [readoutTrace_loc0]; rfl
  cellMapMove := rfl
  heapsSplice := rfl
  guard := by refine ⟨by decide, by decide, by decide, by decide⟩
  logAdv := rfl
  frAccounts := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frLifecycle := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem heapWrite_readout_inhabited :
    Nonempty (HeapWriteTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace heapWriteRow0) heapWritePre heapWritePost 0 0 0 0 0) :=
  ⟨heapWrite_readout⟩

#assert_axioms heapWrite_readout

end Dregg2.Circuit.FloorsNonVacuousWaveMiscNotes
