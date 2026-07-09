/-
# Dregg2.Circuit.FloorsNonVacuousWaveLifecycle — the LIFECYCLE/AUDIT `*TraceReadout` carriers are
  NON-VACUOUS.

Companion to `FloorsNonVacuousWave` (the `CellSealTraceReadout` template). Each of the four
lifecycle/audit refinement rungs (`cellUnseal`/`cellDestroy`/`refusal`/`receiptArchive`
`_descriptorRefines_sat`) takes a `<E>TraceReadout` as a PREMISE; a secretly-uninhabitable premise
makes its consuming rung VACUOUSLY satisfiable. This module exhibits a CONCRETE inhabiting term per
readout (a two-row trace whose designated row carries the selector hot + the committed limb the
decode-seam reads, the faithful chip/range table half via `readoutTrace_side`, a near-`pre = post`
boundary so every frame field is `rfl`, and the guard discharged at a self-targeted live/sealed cell),
so each `<E>TraceReadout` is `Nonempty` and its rung is NON-vacuous.

The committed-root seams (`deathCertRoot` / `auditSlotRoot` / `piAnchored`) are realized by choosing
`compressN := fun _ => 0`: every list digest collapses to `0`, so the trace's all-zero wrap row + the
all-zero `pub` carry the root EXACTLY (the trace-fill identity the deployed prover establishes by
construction).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Every inhabitation is a CONSTRUCTED term;
no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuousWave
import Dregg2.Circuit.RotatedKernelRefinementLifecycle

namespace Dregg2.Circuit.FloorsNonVacuousWaveLifecycle

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2 (VmTrace envAt zeroAsg)
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.FloorsNonVacuous (permOutZ)
open Dregg2.Circuit.FloorsNonVacuousWave (readoutTrace readoutTrace_rows_len readoutTrace_loc0
  readoutTrace_side)
open Dregg2.Circuit.RotatedKernelRefinementLifecycle
open Dregg2.Circuit.Spec.CellLifecycle (CellUnsealGuard CellDestroyGuard cellLifecycleReceipt)
open Dregg2.Circuit.Spec.CellStateAudit (auditGuard auditCellMap)
open Dregg2.Exec (RecChainedState CellId FieldName RecordKernelState)
open Dregg2.Exec.TurnExecutorFull (refusalField)

/-! ## §0 — the trivial committer `compressN := fun _ => 0`.

Every `listDigest LE compressN xs = compressN (xs.map LE) = 0`, so `deathCertRoot`, `auditSlotRoot`,
and `listDigest auditLeaf compressN [1]` are ALL `0` — exactly the value the trace's all-zero wrap row
and all-zero `pub` carry. -/

/-- The constant-zero committer. (Not injective — the readouts are pure premises, so they carry NO
`compressNInjective`; only the consuming rungs do.) -/
def cZero : List ℤ → ℤ := fun _ => 0

theorem cZero_deathCertRoot (k : RecordKernelState) (cell : CellId) :
    deathCertRoot cZero k cell = 0 := rfl

theorem cZero_auditSlotRoot (k : RecordKernelState) (cell : CellId)
    (f : FieldName) : auditSlotRoot cZero k cell f = 0 := rfl

/-- The wrap (LAST) row of `readoutTrace r0` reads `zeroAsg` at every column. -/
theorem readoutTrace_loc1 (r0 : Dregg2.Circuit.Assignment) :
    (envAt (readoutTrace r0) 1).loc = zeroAsg := rfl

/-- The `pub` of `readoutTrace r0` is the all-zero assignment. -/
theorem readoutTrace_pub (r0 : Dregg2.Circuit.Assignment) :
    (envAt (readoutTrace r0) 1).pub = fun _ => 0 := rfl

/-! ## §1 — `CellUnsealTraceReadout` INHABITED.

The active row carries `SEL_CELLUNSEAL = 1` and the AFTER disc limb `= 1`. The boundary is `pre = post`
with `lifecycle = fun _ => 1` (Sealed everywhere): the guard's `lifecycle cell == lcSealed` holds, the
disc-limb seam reads `post.lifecycle cell = 1`, every frame field is `rfl`, and the log advances by the
receipt. Self-authority at `actor = cell = 0`. -/

open Dregg2.Circuit.Emit.EffectVmEmitCellUnseal (SEL_CELLUNSEAL cellUnsealVmDescriptor)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (afterDiscCol)

/-- The active-row assignment for cellUnseal: hot at `SEL_CELLUNSEAL (= 50)`, the AFTER disc limb
(`afterDiscCol … = 271 ≠ 50`) carries `1` (the Sealed discriminant). -/
def cellUnsealRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_CELLUNSEAL then 1
           else if c = afterDiscCol cellUnsealVmDescriptor.traceWidth then 1 else 0

/-- The Sealed self-targeted boundary: `lifecycle = fun _ => 1` (Sealed). `actor = cell = 0`. -/
def cellUnsealPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [],
                lifecycle := fun _ => 1 }, log := [] }

def cellUnsealPost : RecChainedState :=
  { cellUnsealPre with log := cellLifecycleReceipt 0 0 :: cellUnsealPre.log }

/-- **`CellUnsealTraceReadout` is INHABITED.** -/
def cellUnseal_readout :
    CellUnsealTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace cellUnsealRow0) cellUnsealPre cellUnsealPost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [cellUnsealRow0]
  discLimbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterDiscCol cellUnsealVmDescriptor.traceWidth = SEL_CELLUNSEAL) = False := by decide
    simp only [cellUnsealRow0, hcol, if_false, cellUnsealPost, cellUnsealPre]
    rfl
  frameOther := fun _ _ => rfl
  guard := by constructor <;> decide
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem cellUnseal_readout_inhabited :
    Nonempty (CellUnsealTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace cellUnsealRow0) cellUnsealPre cellUnsealPost 0 0) :=
  ⟨cellUnseal_readout⟩

#assert_axioms cellUnseal_readout

/-! ## §2 — `CellDestroyTraceReadout` INHABITED.

Two seams. The ACTIVE row 0 (`0 + 1 = 1 ≠ 2`) carries `SEL_CELLDESTROY = 1` and AFTER disc `= 0`
(the post lifecycle discriminant, Live). The LAST row 1 (`1 + 1 = 2`) is the all-zero wrap: with
`compressN := cZero` the post death-cert root is `0` (matching the zero record limb), and `certHash := 0`
with `pre = post` makes the `piAnchored` RHS `deathCertRoot cZero {pre with deathCert[cell]:=0} cell = 0`
(also matching the zero `pub`). Guard: self-authority + `lifecycle cell ≠ Destroyed` (Live). -/

open Dregg2.Circuit.Emit.EffectVmEmitCellDestroy (SEL_CELLDESTROY cellDestroyVmDescriptor)

/-- The active row for cellDestroy: hot at `SEL_CELLDESTROY (= 47)`; the AFTER disc limb
(`afterDiscCol … = 271 ≠ 47`) reads `0` (Live discriminant). -/
def cellDestroyRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_CELLDESTROY then 1 else 0

/-- The Live self-targeted boundary; all defaults (`lifecycle = fun _ => 0`, `deathCert = fun _ => 0`). -/
def cellDestroyPre : RecChainedState :=
  { kernel := { accounts := ∅, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def cellDestroyPost : RecChainedState :=
  { cellDestroyPre with log := cellLifecycleReceipt 0 0 :: cellDestroyPre.log }

/-- **`CellDestroyTraceReadout` is INHABITED.** (`certHash := 0`, `compressN := cZero`.) -/
def cellDestroy_readout :
    CellDestroyTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace cellDestroyRow0) cellDestroyPre cellDestroyPost 0 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [cellDestroyRow0]
  discLimbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterDiscCol cellDestroyVmDescriptor.traceWidth = SEL_CELLDESTROY) = False := by decide
    simp only [cellDestroyRow0, hcol, if_false, cellDestroyPost, cellDestroyPre]
    rfl
  lcFrameOther := fun _ _ => rfl
  lastRow := 1
  hlastRow := by rw [readoutTrace_rows_len]; omega
  hlastRowIsLast := by rw [readoutTrace_rows_len]
  recordLimbDecodes := by rw [readoutTrace_loc1]; rfl
  piAnchored := by rw [readoutTrace_pub]; rfl
  dcFrameOther := fun _ _ => rfl
  guard := by constructor <;> decide
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem cellDestroy_readout_inhabited :
    Nonempty (CellDestroyTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace cellDestroyRow0) cellDestroyPre cellDestroyPost 0 0 0) :=
  ⟨cellDestroy_readout⟩

#assert_axioms cellDestroy_readout

/-! ## §3 — `RefusalTraceReadout` INHABITED.

ONLY a LAST row (no active row). The LAST row 1 is the all-zero wrap: with `compressN := cZero` the post
audit-slot root over `refusalField` is `0` (matching the zero record limb), and the `piAnchored` RHS
`listDigest auditLeaf cZero [1] = 0` (matching the zero `pub`). The boundary differs from `pre` ONLY at
the `cell` map (`cellMapMove`); every other field is framed `rfl`. Guard: self-authority + membership +
liveness at the live account `0`. -/

open Dregg2.Circuit.Emit.EffectVmEmitRefusal (refusalVmDescriptor SEL_REFUSAL)

/-- The active-row assignment for refusal: hot at `SEL_REFUSAL (= 52)` — the row the appended
audit-slot `.write` map-op gate fires on. (The committed record-pin seams read the LAST/wrap row 1,
which is all-zero independent of this active row.) -/
def refusalRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_REFUSAL then 1 else 0

/-- The pre-boundary for refusal: `0` is a live account. -/
def refusalPre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- The post: the whole `cell`-map move (`auditCellMap` over `refusalField`) + the receipt advance. -/
def refusalPost : RecChainedState :=
  { kernel := { refusalPre.kernel with cell := auditCellMap refusalPre.kernel 0 refusalField },
    log := { actor := 0, src := 0, dst := 0, amt := 0 } :: refusalPre.log }

/-- **`RefusalTraceReadout` is INHABITED.** (`compressN := cZero`.) -/
def refusal_readout :
    RefusalTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace refusalRow0) refusalPre refusalPost 0 0 where
  lastRow := 1
  hlastRow := by rw [readoutTrace_rows_len]; omega
  hlastRowIsLast := by rw [readoutTrace_rows_len]
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [refusalRow0]
  recordLimbDecodes := by rw [readoutTrace_loc1]; rfl
  piAnchored := by rw [readoutTrace_pub]; rfl
  cellMapMoveDecodes := fun _ => rfl
  guard := by refine ⟨by decide, ?_, by decide⟩; decide
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

theorem refusal_readout_inhabited :
    Nonempty (RefusalTraceReadout cZero (fun ins => (permOutZ ins).headD 0)
      (readoutTrace refusalRow0) refusalPre refusalPost 0 0) :=
  ⟨refusal_readout⟩

#assert_axioms refusal_readout

/-! ## §4 — `ReceiptArchiveTraceReadout` INHABITED.

Like cellUnseal: the ACTIVE row 0 carries `SEL_RECEIPT_ARCHIVE_RT = 1` and AFTER disc `= 0` (the post
lifecycle discriminant, Live). `pre = post` (off the log) with `lifecycle = fun _ => 0` (Live), so the
disc-limb seam reads `post.lifecycle cell = 0`. Guard: self-authority + membership + liveness at the
live account `0`. -/

open Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive (SEL_RECEIPT_ARCHIVE_RT
  receiptArchiveActorVmDescriptor)

/-- The active row for receiptArchive: hot at `SEL_RECEIPT_ARCHIVE_RT (= 51)`; the AFTER disc limb
(`afterDiscCol … = 271 ≠ 51`) reads `0` (Live discriminant). -/
def receiptArchiveRow0 : Dregg2.Circuit.Assignment :=
  fun c => if c = SEL_RECEIPT_ARCHIVE_RT then 1 else 0

/-- The Live live-account self-targeted boundary. -/
def receiptArchivePre : RecChainedState :=
  { kernel := { accounts := {0}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

def receiptArchivePost : RecChainedState :=
  { receiptArchivePre with log := { actor := 0, src := 0, dst := 0, amt := 0 } :: receiptArchivePre.log }

/-- **`ReceiptArchiveTraceReadout` is INHABITED.** -/
def receiptArchive_readout :
    ReceiptArchiveTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace receiptArchiveRow0) receiptArchivePre receiptArchivePost 0 0 where
  row := 0
  hrow := by rw [readoutTrace_rows_len]; omega
  hrowNotLast := by rw [readoutTrace_rows_len]; omega
  hsel := by rw [readoutTrace_loc0]; simp [receiptArchiveRow0]
  discLimbDecodes := by
    rw [readoutTrace_loc0]
    have hcol : (afterDiscCol receiptArchiveActorVmDescriptor.traceWidth = SEL_RECEIPT_ARCHIVE_RT)
        = False := by decide
    simp only [receiptArchiveRow0, hcol, if_false, receiptArchivePost, receiptArchivePre]
    rfl
  frameOther := fun _ _ => rfl
  guard := by refine ⟨by decide, ?_, by decide⟩; decide
  logAdv := rfl
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
  frBal := rfl
  frSlotCaveats := rfl
  frFactories := rfl
  frDeathCert := rfl
  frDelegate := rfl
  frDelegations := rfl
  frDelegationEpoch := rfl
  frDelegationEpochAt := rfl
  frHeaps := rfl
  frNullifierRoot := rfl
  frRevokedRoot := rfl

theorem receiptArchive_readout_inhabited :
    Nonempty (ReceiptArchiveTraceReadout (fun ins => (permOutZ ins).headD 0)
      (readoutTrace receiptArchiveRow0) receiptArchivePre receiptArchivePost 0 0) :=
  ⟨receiptArchive_readout⟩

#assert_axioms receiptArchive_readout

end Dregg2.Circuit.FloorsNonVacuousWaveLifecycle
