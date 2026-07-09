/-
# Dregg2.Circuit.FloorsNonVacuousWaveTransfer — `TransferTraceReadout` is NON-VACUOUS.

The transfer rung's circuit-witness column+frame extraction `TransferTraceReadout` (ClosureTransfer) is
the most structured per-effect readout: two designated rows with their full `RowEncodes` decodes, the
direction/amount tags, `RotTableSide` faithfulness, the side guards (non-neg / distinct / both-live /
accepts), the 16-field frame, and the receipt-log advance. We exhibit a CONCRETE inhabiting term.

The two rows are built so every `RowEncodes` column read is `rfl` (each decoded `CellState`/param field is
DEFINED as the row's column value), with the debit row carrying `direction = 1` and the credit row
`direction = 0`. The boundary is `pre = post` over a kernel with `accounts = {0, 1}` and both cells Live,
`tr = ⟨0, 0, 1, 0⟩` (actor 0, src 0 ≠ dst 1, amount 0 ≥ 0). So every guard discharges by `decide` /
`rfl`, every frame is `rfl`, and `RotTableSide` rides the faithful tables. Hence `TransferTraceReadout` is
`Nonempty`: the transfer rung's premise is satisfiable, not secretly empty.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.FloorsNonVacuousWave
import Dregg2.Circuit.ClosureTransfer

namespace Dregg2.Circuit.FloorsNonVacuousWaveTransfer

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.RotatedKernelRefinement (RotTableSide)
open Dregg2.Circuit.FloorsNonVacuous (faithfulTf permOutZ permOut0 permOutZ_width
  genuineChipTbl_sound faithfulTf_poseidon2 faithfulTf_range)
open Dregg2.Circuit.ClosureTransfer (TransferTraceReadout)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (IsTransferRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState TransferParams RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Exec (RecChainedState RecordKernelState)
open Dregg2.Exec.TurnExecutorFull (acceptsEffects)

set_option autoImplicit false

/-! ## §1 — the two designated rows.

`txRow dir` is a row carrying `s_transfer = 1`, `s_noop = 0`, and `direction = dir` (the param-block
direction column), zero elsewhere. The debit row is `txRow 1`, the credit row `txRow 0`. Every other
state/param/commit column is `0`, so each decoded record field (read off the row) is `0`. -/

def txRow (dir : ℤ) : Dregg2.Circuit.Assignment := fun c =>
  if c = sel.TRANSFER then 1
  else if c = sel.NOOP then 0
  else if c = prmCol param.DIRECTION then dir
  else 0

/-- The three-row transfer trace: row 0 the debit (`direction = 1`), row 1 the credit
(`direction = 0`), row 2 the wrap/pad. Both designated rows are transition rows
(`0 + 1 = 1 ≠ 3`, `1 + 1 = 2 ≠ 3`). The auxiliary tables ARE the faithful tables. -/
def txTrace : VmTrace where
  rows := [txRow 1, txRow 0, zeroAsg]
  pub  := fun _ => 0
  tf   := faithfulTf

theorem txTrace_len : txTrace.rows.length = 3 := rfl
theorem txTrace_tf : txTrace.tf = faithfulTf := rfl
theorem txTrace_loc0 : (envAt txTrace 0).loc = txRow 1 := rfl
theorem txTrace_loc1 : (envAt txTrace 1).loc = txRow 0 := rfl

/-- The `RotTableSide` over the faithful tables (same discharge as `FloorsNonVacuousWave.readoutTrace_side`). -/
theorem txTrace_side : RotTableSide permOutZ (fun ins => (permOutZ ins).headD 0) txTrace where
  permWidth := permOutZ_width
  chipHashIsLane0 := fun _ => rfl
  chipTableFaithful := by
    rw [txTrace_tf, faithfulTf_poseidon2]; exact genuineChipTbl_sound
  range := by rw [txTrace_tf, faithfulTf_range]

/-- The decoded `CellState` read off a row `r`: each field is the row's value at the corresponding
state-before column, so `RowEncodes`'s state-before conjuncts are `rfl`. (We use ONE record for both the
before- and after-block reads by also defining the after fields from the after columns — see `cellAfter`.)
Here `pre = post` so a single zero record suffices; we read the actual columns. -/
def cellBefore (r : Dregg2.Circuit.Assignment) : CellState where
  balLo := r (sbCol state.BALANCE_LO)
  balHi := r (sbCol state.BALANCE_HI)
  nonce := r (sbCol state.NONCE)
  fields := fun i => r (sbCol (state.FIELD_BASE + i.val))
  capRoot := r (sbCol state.CAP_ROOT)
  reserved := r (sbCol state.RESERVED)
  commit := r (sbCol state.STATE_COMMIT)

def cellAfter (r : Dregg2.Circuit.Assignment) : CellState where
  balLo := r (saCol state.BALANCE_LO)
  balHi := r (saCol state.BALANCE_HI)
  nonce := r (saCol state.NONCE)
  fields := fun i => r (saCol (state.FIELD_BASE + i.val))
  capRoot := r (saCol state.CAP_ROOT)
  reserved := r (saCol state.RESERVED)
  commit := r (saCol state.STATE_COMMIT)

def paramsOf (r : Dregg2.Circuit.Assignment) : TransferParams where
  amount := r (prmCol param.AMOUNT)
  direction := r (prmCol param.DIRECTION)

/-- `RowEncodes` holds with the records/params READ OFF the row — every conjunct is `rfl` by the
definitions of `cellBefore`/`cellAfter`/`paramsOf`, and the two published commits are `0 = pre/post.commit`
(`pub = fun _ => 0`, and the before/after state-commit columns are `0` on `txRow`). -/
theorem rowEncodes_txRow (r : Dregg2.Circuit.Assignment) (pub0 : ℕ → ℤ)
    (hpubOld : pub0 pi.OLD_COMMIT = r (sbCol state.STATE_COMMIT))
    (hpubNew : pub0 pi.NEW_COMMIT = r (saCol state.STATE_COMMIT)) :
    RowEncodes { loc := r, nxt := r, pub := pub0 } (cellBefore r) (paramsOf r) (cellAfter r) := by
  refine ⟨rfl, rfl, rfl, fun i => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun i => rfl, rfl, rfl,
    rfl, ?_, ?_⟩
  · exact hpubOld
  · exact hpubNew

/-! ## §2 — the boundary. `pre = post`, accounts `{0,1}`, both Live; `tr = ⟨0,0,1,0⟩`. -/

def txPre : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun _ => default, caps := fun _ => [] }, log := [] }

/-- `tr`: actor 0, src 0, dst 1, amount 0. `src ≠ dst`, both ∈ {0,1}, amount ≥ 0. -/
def txTurn : Dregg2.Exec.Turn := { actor := 0, src := 0, dst := 1, amt := 0 }

def txPost : RecChainedState := { txPre with log := txTurn :: txPre.log }

theorem txTrace_envAt0 : envAt txTrace 0 = { loc := txRow 1, nxt := txRow 0, pub := fun _ => 0 } := rfl
theorem txTrace_envAt1 : envAt txTrace 1 = { loc := txRow 0, nxt := zeroAsg, pub := fun _ => 0 } := rfl

/-- `txRow dir` reads `0` at the state-commit columns (distinct from the three hot indices). -/
theorem txRow_sbCommit (dir : ℤ) : txRow dir (sbCol state.STATE_COMMIT) = 0 := by
  simp only [txRow, sbCol, sel.TRANSFER, sel.NOOP, prmCol, state.STATE_COMMIT, param.DIRECTION,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_SIZE, NUM_EFFECTS, NUM_PARAMS]
  norm_num
theorem txRow_saCommit (dir : ℤ) : txRow dir (saCol state.STATE_COMMIT) = 0 := by
  simp only [txRow, saCol, sel.TRANSFER, sel.NOOP, prmCol, state.STATE_COMMIT, param.DIRECTION,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, STATE_SIZE, NUM_EFFECTS, NUM_PARAMS]
  norm_num

/-- `txRow dir` IS a transfer row: `s_transfer = 1`, `s_noop = 0` (the two selector indices `1`, `0`
are distinct from `prmCol param.DIRECTION`). -/
theorem isTransferRow_txRow (dir : ℤ) : IsTransferRow { loc := txRow dir, nxt := zeroAsg, pub := fun _ => 0 } := by
  refine ⟨?_, ?_⟩
  · show txRow dir sel.TRANSFER = 1
    simp only [txRow, sel.TRANSFER]; norm_num
  · show txRow dir sel.NOOP = 0
    simp only [txRow, sel.TRANSFER, sel.NOOP, prmCol, param.DIRECTION, PARAM_BASE]; norm_num

/-- **`TransferTraceReadout` is INHABITED.** -/
def transfer_readout :
    TransferTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      txTrace txPre txPost txTurn (0 : Dregg2.Exec.AssetId) where
  permOut := permOutZ
  hside := txTrace_side
  di := 0
  ci := 1
  hdi := by rw [txTrace_len]; omega
  hci := by rw [txTrace_len]; omega
  hdiNotLast := by rw [txTrace_len]; omega
  hciNotLast := by rw [txTrace_len]; omega
  srcPre := cellBefore (txRow 1)
  srcPost := cellAfter (txRow 1)
  dstPre := cellBefore (txRow 0)
  dstPost := cellAfter (txRow 0)
  srcParams := paramsOf (txRow 1)
  dstParams := paramsOf (txRow 0)
  hdiRow := by rw [txTrace_envAt0]; exact isTransferRow_txRow 1
  hciRow := by rw [txTrace_envAt1]; exact isTransferRow_txRow 0
  hdiEnc := by
    rw [txTrace_envAt0]
    exact rowEncodes_txRow (txRow 1) (fun _ => 0) (txRow_sbCommit 1).symm (txRow_saCommit 1).symm
  hciEnc := by
    rw [txTrace_envAt1]
    exact rowEncodes_txRow (txRow 0) (fun _ => 0) (txRow_sbCommit 0).symm (txRow_saCommit 0).symm
  hdiDir := by
    show (paramsOf (txRow 1)).direction = 1
    simp only [paramsOf, txRow, prmCol, param.DIRECTION, sel.TRANSFER, sel.NOOP, PARAM_BASE,
      STATE_BEFORE_BASE, STATE_SIZE, NUM_EFFECTS]; norm_num
  hciDir := by
    show (paramsOf (txRow 0)).direction = 0
    simp only [paramsOf, txRow, prmCol, param.DIRECTION, sel.TRANSFER, sel.NOOP, PARAM_BASE,
      STATE_BEFORE_BASE, STATE_SIZE, NUM_EFFECTS]; norm_num
  hdiAmt := by
    show (paramsOf (txRow 1)).amount = txTurn.amt
    simp only [paramsOf, txRow, prmCol, param.AMOUNT, param.DIRECTION, sel.TRANSFER, sel.NOOP,
      PARAM_BASE, STATE_BEFORE_BASE, STATE_SIZE, NUM_EFFECTS, txTurn]
    norm_num
  hciAmt := by
    show (paramsOf (txRow 0)).amount = txTurn.amt
    simp only [paramsOf, txRow, prmCol, param.AMOUNT, param.DIRECTION, sel.TRANSFER, sel.NOOP,
      PARAM_BASE, STATE_BEFORE_BASE, STATE_SIZE, NUM_EFFECTS, txTurn]
    norm_num
  guardNonNeg := by show (0 : ℤ) ≤ txTurn.amt; decide
  guardDistinct := by show txTurn.src ≠ txTurn.dst; decide
  guardLiveSrc := by show txTurn.src ∈ txPre.kernel.accounts; decide
  guardLiveDst := by show txTurn.dst ∈ txPre.kernel.accounts; decide
  guardSrcLifecycleLive := by decide
  guardAccepts := by decide
  frAccounts := rfl
  frCell := rfl
  frCaps := rfl
  frNullifiers := rfl
  frRevoked := rfl
  frCommitments := rfl
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
  logAdv := rfl

theorem transfer_readout_inhabited :
    Nonempty (TransferTraceReadout (fun ins => (permOutZ ins).headD 0) (fun _ => 0) (fun _ => (0, 0)) []
      txTrace txPre txPost txTurn (0 : Dregg2.Exec.AssetId)) :=
  ⟨transfer_readout⟩

#assert_axioms transfer_readout

end Dregg2.Circuit.FloorsNonVacuousWaveTransfer
