/-
# Dregg2.Apps.StorageGatewayMandate — storage gateway mandate as a verified cell-program (ungated).

A **storage-gateway mandate** on the REAL `RecordKernelState`: the mandate cell carries `object_key`,
`last_op`, `volume_spent` (monotonic Stingray debit tracker), and an immutable `commitment_anchor`.
Predicate admission (`sgmAdmitM`) couples op-allowlist, prefix authorization (PUT), compartment
clearance (GET), and volume-budget debits (`Proof/Stingray.Slice`).

Load-bearing guarantees (ungated crown):

  * **REJECTION TEETH** — disallowed ops, prefix violations, clearance failures, and over-debits
    fail-closed at the predicate layer.
  * **VOLUME LEGALITY** — along any adversarial schedule of admitted ops, spent stays within ceiling
    (`sgm_volume_legal_forever`).
  * **CONSERVATION** — mandate metadata writes are balance-neutral (`sgm_pay_supply_forever` via
    `livingCellA_carries` / `cellObsA_next`).

Templates: `Apps/CompartmentWorkflowMandate.lean`.
-/
import Dregg2.Exec.CellCarry
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.FullForest
import Dregg2.Authority.ClearanceGraph
import Dregg2.Apps.StorageGatewayMandate.Core
import Dregg2.Proof.Noninterference
import Dregg2.Proof.Stingray
import Dregg2.Tactics

namespace Dregg2.Apps.StorageGatewayMandate

open Dregg2.Exec
open Dregg2.Exec (cellObsA)
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.FullForest
open Dregg2.Exec.EffectsState (caveatsAdmit fieldOf writeField stateStepGuarded stateStepGuarded_admits
  stateStepGuarded_caveat_violation_fails stateStepGuarded_eq stateStep_factors guarded_state_field_written
  setField_fieldOf setField)
open Dregg2.Proof.Noninterference (writeField_cell_other writeField_field_ne field_setField_ne
  field_setField_eq execFullA_setFieldA_writeField)
open Dregg2.Authority.ClearanceGraph
open Dregg2.Proof.Stingray

/-! ## §1 — Gateway domain on RecordKernel (object key + op + volume spent). -/

abbrev mandateActor : CellId := 0
abbrev payAsset : AssetId := 0
abbrev sgmEmitTopic : Int := 9

/-- **The mandate's published per-slot program — NOW with the op admission table baked in.** Keeps
the immutable `commitment_anchor` + monotonic/bounded `volume_spent` legs, and ADDS an `.admitTable
lastOpSlot (sgmOpAdmitTable demoMandate)`: the executor now enforces the op-allowlist ∧ GET-clearance
leg of `sgmAdmitM` inline on every `last_op` write. A disallowed op or a no-clearance GET is absent
from the table, so the executor rejects it (where no prior caveat could express op-allowlist or
clearance). Prefix-on-PUT stays a predicate obligation (key is a string, not a scalar). -/
def mandateCaveats : List SlotCaveat :=
  [ .immutable commitmentAnchorSlot
  , .monotonic volumeSpentSlot
  , .boundedBy volumeSpentSlot 0 (demoMandate.volumeBudget.ceiling : Int)
  , .admitTable lastOpSlot (sgmOpAdmitTable demoMandate) ]

/-- Write the object key field on the mandate cell. -/
def sgmExecSetKey (actor : CellId) (key : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell objectKeySlot key, [] ⟩

/-- Write the last-op field on the mandate cell. -/
def sgmExecSetOp (actor : CellId) (op : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell lastOpSlot op, [] ⟩

/-- Bump the monotonic volume-spent tracker. -/
def sgmExecDebitVolume (actor : CellId) (newSpent : Int) : FullForestA :=
  ⟨ .setFieldA actor mandateCell volumeSpentSlot newSpent, [] ⟩

/-- Audit emit for a committed storage op (blob hash as payload). -/
def sgmExecEmit (actor : CellId) (blobHash : Int) : FullForestA :=
  ⟨ .emitEventA actor mandateCell sgmEmitTopic blobHash, [] ⟩

/-- One storage op as a chained sequence: set key, set op, emit blob hash. -/
def sgmStorageChain (s : RecChainedState) (actor : CellId) (key op blobHash : Int) :
    Option RecChainedState :=
  (execFullForestA s (sgmExecSetKey actor key)).bind fun s' =>
    (execFullForestA s' (sgmExecSetOp actor op)).bind fun s'' =>
      execFullForestA s'' (sgmExecEmit actor blobHash)

/-! ## §A — Predicate-level forever stream (volume legality). -/

inductive SgmOp where
  | tick (req : StorageRequest)
  deriving Repr, DecidableEq

def SgmSched : Type := Nat → SgmOp

def sgmStep (m : StorageMandate) (s : SgmRuntime) : SgmOp → SgmRuntime
  | .tick req => (sgmAdmitM m s req).getD s

def sgmTraj (m : StorageMandate) (s : SgmRuntime) (sched : SgmSched) : Nat → SgmRuntime
  | 0     => s
  | n + 1 => sgmStep m (sgmTraj m s sched n) (sched n)

theorem sgmStep_preserves_WF (m : StorageMandate) (s : SgmRuntime) (op : SgmOp) (hwf : s.WF) :
    (sgmStep m s op).WF := by
  rcases op with ⟨req⟩
  show (sgmAdmitM m s req).getD s |>.WF
  cases hp : sgmAdmitM m s req with
  | some s' => simp only [Option.getD_some]; exact sgmAdmitM_preserves_WF m s s' req hwf hp
  | none    => simp only [Option.getD_none]; exact hwf

/-- **`sgm_volume_legal_forever`** — volume spent stays within ceiling along every admitted
op stream, under every adversarial schedule. -/
theorem sgm_volume_legal_forever (m : StorageMandate) (s : SgmRuntime) (hinit : s.WF) (sched : SgmSched) :
    ∀ n, (sgmTraj m s sched n).WF := by
  intro n
  induction n with
  | zero => exact hinit
  | succ k ih =>
      show (sgmStep m (sgmTraj m s sched k) (sched k)).WF
      exact sgmStep_preserves_WF m (sgmTraj m s sched k) (sched k) ih

/-! ## §B — REAL executor teeth + conservation crown. -/

theorem sgm_over_debit_rejected_exec (s : RecChainedState) (actor : CellId) (newSpent : Int)
    (hbound : caveatsAdmit s.kernel volumeSpentSlot actor mandateCell newSpent = false) :
    execFullForestA s (sgmExecDebitVolume actor newSpent) = none := by
  have hnone := stateStepGuarded_caveat_violation_fails s volumeSpentSlot actor mandateCell newSpent hbound
  rw [execFullForestA_eq_execFullTurnA]
  simp only [sgmExecDebitVolume, lowerForestA, lowerChildrenA, execFullTurnA, execFullA, hnone]

/-! ### §B.admit — the EXECUTOR's `caveatsAdmit` over the op slot IS `sgmAdmitM`'s op-leg.

With `mandateCaveats` now carrying `.admitTable lastOpSlot (sgmOpAdmitTable demoMandate)`, the
executor's `caveatsAdmit` on a `last_op` write reduces EXACTLY to `sgmOpAdmitTable`-membership, which
is EXACTLY `sgmAdmitM`'s op-allowlist ∧ GET-clearance leg. The inline internalization of the op
admission. -/

/-- **`sgm_caveatsAdmit_op_eq_table`.** On a cell carrying `mandateCaveats`, the executor's
`caveatsAdmit` on a `last_op` write is exactly `sgmOpAdmitTable`-membership of `(old, newOp)`. -/
theorem sgm_caveatsAdmit_op_eq_table (k : RecordKernelState)
    (hprog : k.slotCaveats mandateCell = mandateCaveats) (actor : CellId) (newOp : Int) :
    caveatsAdmit k lastOpSlot actor mandateCell newOp
      = (sgmOpAdmitTable demoMandate).contains (fieldOf lastOpSlot (k.cell mandateCell), newOp) := by
  unfold caveatsAdmit
  rw [hprog]
  have hf : (mandateCaveats.filter (fun cav => cav.field == lastOpSlot))
      = [.admitTable lastOpSlot (sgmOpAdmitTable demoMandate)] := by decide
  rw [hf]
  simp only [List.all_cons, List.all_nil, Bool.and_true, SlotCaveat.eval]

/-- **`sgm_commit_iff_op_admit` (the COMMIT-IFF-ADMIT op-leg, predicate↔executor).** On a
mandate cell whose committed `last_op` is a valid prior op code `old ∈ {-1,0,1,2}`, the executor's
caveat gate on writing op `op` ADMITS iff `sgmAdmitM`'s op-leg admits `op` (op allowed ∧ GET ⇒
clearance). The off-line op admission and the running executor decide the SAME ops. -/
theorem sgm_commit_iff_op_admit (k : RecordKernelState)
    (hprog : k.slotCaveats mandateCell = mandateCaveats) (actor : CellId) (op : StorageOp)
    (hold : fieldOf lastOpSlot (k.cell mandateCell) ∈ [(-1 : Int), 0, 1, 2]) :
    caveatsAdmit k lastOpSlot actor mandateCell op.toInt = true
      ↔ sgmOpAdmitted demoMandate op = true := by
  rw [sgm_caveatsAdmit_op_eq_table k hprog, List.contains_iff_mem,
      sgmOpAdmitTable_mem_iff demoMandate _ op hold]

theorem sgmExecSetKey_delta_zero (actor : CellId) (key : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecSetKey actor key)) b = 0 := by
  simp [sgmExecSetKey, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecSetOp_delta_zero (actor : CellId) (op : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecSetOp actor op)) b = 0 := by
  simp [sgmExecSetOp, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecDebitVolume_delta_zero (actor : CellId) (newSpent : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecDebitVolume actor newSpent)) b = 0 := by
  simp [sgmExecDebitVolume, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgmExecEmit_delta_zero (actor : CellId) (blobHash : Int) (b : AssetId) :
    turnLedgerDeltaAsset (lowerForestA (sgmExecEmit actor blobHash)) b = 0 := by
  simp [sgmExecEmit, lowerForestA, lowerChildrenA, turnLedgerDeltaAsset, ledgerDeltaAsset]

theorem sgm_chain_conserves {s s' : RecChainedState} (actor : CellId) (key op blobHash : Int) (b : AssetId)
    (h : sgmStorageChain s actor key op blobHash = some s') :
    recTotalAsset s'.kernel b = recTotalAsset s.kernel b := by
  cases hkey : execFullForestA s (sgmExecSetKey actor key) with
  | none => simp [sgmStorageChain, hkey] at h
  | some s1 =>
      cases hop : execFullForestA s1 (sgmExecSetOp actor op) with
      | none => simp [sgmStorageChain, hkey, hop] at h
      | some s2 =>
          have hem : execFullForestA s2 (sgmExecEmit actor blobHash) = some s' := by
            simpa [sgmStorageChain, hkey, hop] using h
          have h1 := execFullForestA_conserves_per_asset s s1 (sgmExecSetKey actor key) b hkey
            (sgmExecSetKey_delta_zero actor key b)
          have h2 := execFullForestA_conserves_per_asset s1 s2 (sgmExecSetOp actor op) b hop
            (sgmExecSetOp_delta_zero actor op b)
          have h3 := execFullForestA_conserves_per_asset s2 s' (sgmExecEmit actor blobHash) b hem
            (sgmExecEmit_delta_zero actor blobHash b)
          calc recTotalAsset s'.kernel b
              = recTotalAsset s2.kernel b := h3
            _ = recTotalAsset s1.kernel b := h2
            _ = recTotalAsset s.kernel b := h1

/-- **`sgm_pay_supply_forever` — APP SEMANTICS (ungated crown).** Along EVERY adversarial
schedule on the real living cell, payment asset combined supply never drifts. -/
theorem sgm_pay_supply_forever (s0 : RecChainedState) (sched : SchedA) :
    ∀ n, recTotalAsset (trajA s0 sched n).kernel payAsset =
          recTotalAsset s0.kernel payAsset := by
  intro n
  simpa [cellObsA] using congrFun (livingCellA_obs_invariant' s0 sched n) payAsset

/-! ## §B′·frame — GENERIC executor frame: `slotCaveats` of a LIVE cell is enforced forever.

The single load-bearing fact that makes the mandate crown NON-vacuous: along ANY adversarial forest
trajectory, the published per-slot caveat PROGRAM installed on the live mandate cell is NEVER removed
or altered, and the cell stays a live account. Two structural facts discharge every one of the 53
`FullActionA` arms: (1) `accounts` only ever GROWS (every kernel transform either keeps `accounts`
fixed or `insert`s a fresh id); (2) `slotCaveats` is ONLY ever written at a FRESHLY-minted id (the
three create arms, whose `newCell ∉ accounts` gate forces `newCell ≠ c` for any live `c`), so the
`slotCaveats c` projection of a live cell `c` is unchanged by every committed step. This is the
executor-level teeth: the `.immutable`/`.monotonicSeq`/`.boundedBy` program a factory publishes is
enforced for the cell's WHOLE LIFE. The structural sibling of `Subscription.execFullA_subWF_preserved`
and `CellNullifier.execFullA_nullifiers_grow`. Generic over the cell id and the caveat list. -/

-- (F2b: the queue-family frame helpers died with the queue verb family.)

mutual
/-- **`execFullA_progLive_preserved` — the per-effect program-live FRAME.** A committed
`FullActionA` keeps a live cell `c` live AND keeps its published caveat program installed. The three
create arms mint a FRESH `newCell ≠ c`; every other arm updates a non-`{accounts,slotCaveats}` field
(or `insert`s elsewhere), so the `(c ∈ accounts, slotCaveats c)` pair is preserved verbatim;
`exerciseA` RECURSES (mutual `execInnerA_progLive_preserved`). -/
theorem execFullA_progLive_preserved (s s' : RecChainedState) (fa : FullActionA) (c : CellId)
    (cav : List SlotCaveat) (h : execFullA s fa = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  cases fa with
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal } := by
        unfold recKExecAsset at hk; split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      rw [hn]; exact ⟨hlive, hprog⟩
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | revoke holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKBurnAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | setFieldA actor cell f v =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h); subst hs'; exact ⟨hlive, hprog⟩
  | emitEventA actor cell topic data =>
      simp only [execFullA] at h
      by_cases hl : cell ∈ s.kernel.accounts
      · rw [if_pos hl] at h; simp only [emitStep, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
      · rw [if_neg hl] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegateAtten at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h
      obtain ⟨rfl⟩ := h; exact ⟨hlive, hprog⟩
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hlive1 : c ∈ s1.kernel.accounts := by rw [hs1]; exact hlive
            have hprog1 : s1.kernel.slotCaveats c = cav := by rw [hs1]; exact hprog
            exact execInnerA_progLive_preserved s1 s' inner c cav h hlive1 hprog1
      · rw [if_neg hf] at h; exact absurd h (by simp)
  | createCellA actor newCell =>
      obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs'
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | createCellFromFactoryA actor newCell vk =>
      obtain ⟨e, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hs1⟩ := createCellChainA_factors hc
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs' hs1
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | spawnA actor child target =>
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hc'⟩ := createCellChainA_factors hc
      have hne : c ≠ child := fun heq => hfresh (heq ▸ hlive)
      subst hs' hc'
      refine ⟨?_, ?_⟩
      · dsimp [createCellIntoAsset]; exact Finset.mem_insert_of_mem hlive
      · dsimp [createCellIntoAsset, bornEmptyCellSlots]; simp only [if_neg hne]; exact hprog
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]; exact ⟨hlive, hprog⟩
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } := by
              unfold noteSpendNullifier at hk; split at hk
              · exact absurd hk (by simp)
              · injection hk with hk; exact hk.symm
            rw [hn]; exact ⟨hlive, hprog⟩
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA] at h
      option_inj at h; subst h
      show c ∈ (noteCreateCommitment s.kernel cm).accounts ∧ (noteCreateCommitment s.kernel cm).slotCaveats c = cav
      unfold noteCreateCommitment; exact ⟨hlive, hprog⟩
  | makeSovereignA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'; exact ⟨hlive, hprog⟩
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'
      show c ∈ (setLifecycle s.kernel cell lcSealed).accounts ∧ (setLifecycle s.kernel cell lcSealed).slotCaveats c = cav
      unfold setLifecycle; exact ⟨hlive, hprog⟩
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'
      show c ∈ (setLifecycle s.kernel cell lcLive).accounts ∧ (setLifecycle s.kernel cell lcLive).slotCaveats c = cav
      unfold setLifecycle; exact ⟨hlive, hprog⟩
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'
      refine ⟨?_, ?_⟩
      · show c ∈ (setLifecycle s.kernel cell lcDestroyed).accounts; unfold setLifecycle; exact hlive
      · show ({ (setLifecycle s.kernel cell lcDestroyed) with deathCert := _ }).slotCaveats c = cav
        unfold setLifecycle; exact hprog
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'
      show c ∈ ({ s.kernel with delegations := _ }).accounts ∧ ({ s.kernel with delegations := _ }).slotCaveats c = cav
      exact ⟨hlive, hprog⟩
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩


/-- **`execInnerA_progLive_preserved`** — the inner-effect fold an `exerciseA` recurses through keeps a
live cell's published caveat program installed. Mutual with `execFullA_progLive_preserved`. -/
theorem execInnerA_progLive_preserved (s s' : RecChainedState) (inner : List FullActionA) (c : CellId)
    (cav : List SlotCaveat) (h : execInnerA s inner = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          obtain ⟨hlive1, hprog1⟩ := execFullA_progLive_preserved s s1 a c cav ha hlive hprog
          exact execInnerA_progLive_preserved s1 s' rest c cav h hlive1 hprog1
end

/-- **`execFullTurnA_progLive_preserved`.** A committed per-asset full TURN keeps a live cell's
caveat program installed. Induction on the action list. -/
theorem execFullTurnA_progLive_preserved :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (c : CellId) (cav : List SlotCaveat),
      execFullTurnA s tt = some s' → c ∈ s.kernel.accounts → s.kernel.slotCaveats c = cav →
        c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav
  | s, s', [], c, cav, h, hlive, hprog => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; exact ⟨hlive, hprog⟩
  | s, s', a :: rest, c, cav, h, hlive, hprog => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          obtain ⟨hlive1, hprog1⟩ := execFullA_progLive_preserved s s1 a c cav ha hlive hprog
          exact execFullTurnA_progLive_preserved s1 s' rest c cav h hlive1 hprog1

/-- **`execFullForestA_progLive_preserved`.** A committed full FOREST keeps a live cell's caveat
program installed. Through the pre-order bridge `execFullForestA_eq_execFullTurnA`. -/
theorem execFullForestA_progLive_preserved (s s' : RecChainedState) (f : FullForestA) (c : CellId)
    (cav : List SlotCaveat) (h : execFullForestA s f = some s')
    (hlive : c ∈ s.kernel.accounts) (hprog : s.kernel.slotCaveats c = cav) :
    c ∈ s'.kernel.accounts ∧ s'.kernel.slotCaveats c = cav := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_progLive_preserved s s' (lowerForestA f) c cav h hlive hprog

/-! ## §B″ — the ANCHOR-VALUE FRAME: a committed forest preserves the immutable `commitment_anchor`.

`progLive_preserved` carries liveness + the caveat program (the *enforcement* of the immutable
anchor) but NOT the literal anchor *value*. This section closes that gap: the actual stored
`commitment_anchor` scalar on a cell whose published program contains `.immutable commitmentAnchorSlot`
is preserved across EVERY committed action — with ONE genuine exception, `makeSovereign` on that very
cell, which is NOT caveat-gated and rebinds the cell record behind a state commitment (it provably
clobbers any field; see `Proof.Noninterference.makeSovereign_leaks`). We carry an explicit
`anchorActionOK`/`anchorForestOK` guard EXCLUDING that one action, and prove the value frame under it. -/

/-- `fieldOf` of a value depends only on its `Value.field` read at that slot. -/
theorem fieldOf_of_field_eq {f : FieldName} {v w : Value} (h : v.field f = w.field f) :
    fieldOf f v = fieldOf f w := by
  unfold fieldOf Value.scalar; rw [h]

/-- A FRESH-cell create leaves every OLD cell's record verbatim (`c ≠ newCell`). -/
theorem createCellIntoAsset_cell_other (k : RecordKernelState) (newCell c : CellId)
    (hne : c ≠ newCell) : (createCellIntoAsset k newCell).cell c = k.cell c := by
  simp only [createCellIntoAsset, bornEmptyCellSlots, if_neg hne]

/-- A single action is anchor-safe FOR cell `c`: it is anything except `makeSovereign` aimed at `c`
(the sole un-caveat-gated cell-record rebind, which drops every field — see the §B″ note). Every
other `FullActionA` either leaves `c`'s record untouched or edits it only through a caveat-GATED
field write, against which the `.immutable commitmentAnchorSlot` caveat defends the anchor scalar.
`exerciseA` RECURSES into its inner fold (which `execFullA` runs after the hold-gate), so its inner
list must itself be anchor-safe — otherwise a `makeSovereign c` could hide inside a facet exercise.

Boolean shadow (`anchorActionOKB`): the structural recursion over `exerciseA`'s inner list field lives
here, with `termination_by` on the action `sizeOf` (each inner element is a strict subterm). -/
def anchorActionOKB (c : CellId) : FullActionA → Bool
  | .makeSovereignA _ cell => !(cell == c)
  | .exerciseA _ _ inner   => inner.attach.all (fun a => anchorActionOKB c a.1)
  | _                      => true
termination_by a => sizeOf a
decreasing_by
  · simp_wf
    rename_i a hmem
    have := List.sizeOf_lt_of_mem a.2
    omega

/-- A single action is anchor-safe FOR cell `c`. -/
def anchorActionOK (c : CellId) (a : FullActionA) : Prop := anchorActionOKB c a = true

instance anchorActionOKDecidable (c : CellId) (a : FullActionA) : Decidable (anchorActionOK c a) := by
  unfold anchorActionOK; infer_instance

theorem anchorActionOK_makeSovereign {c actor cell : CellId}
    (h : anchorActionOK c (.makeSovereignA actor cell)) : cell ≠ c := by
  unfold anchorActionOK at h
  simp only [anchorActionOKB] at h
  simpa using h

/-- An inner-effect list / lowered forest is anchor-safe for `c`: every action is. -/
def anchorListOK (c : CellId) (l : List FullActionA) : Prop := ∀ a ∈ l, anchorActionOK c a

/-- A forest is anchor-safe for `c` iff its pre-order lowering is. -/
def anchorForestOK (c : CellId) (f : FullForestA) : Prop := anchorListOK c (lowerForestA f)

/-- From a safe `exerciseA` guard, the inner list is anchor-safe. -/
theorem anchorListOK_of_exercise {c : CellId} {actor t : CellId} {inner : List FullActionA}
    (hok : anchorActionOK c (.exerciseA actor t inner)) : anchorListOK c inner := by
  intro a ha
  unfold anchorActionOK at hok ⊢
  simp only [anchorActionOKB] at hok
  have hall := List.all_eq_true.1 hok
  exact hall ⟨a, ha⟩ (List.mem_attach inner ⟨a, ha⟩)

mutual
/-- **`execFullA_anchorVal_preserved` — the per-effect ANCHOR-VALUE frame.** A committed
`FullActionA` that is anchor-safe for `c` (`anchorActionOK c fa`) preserves `c`'s stored
`commitment_anchor` scalar, PROVIDED `c` carries the `.immutable commitmentAnchorSlot` caveat in its
published program. Every non-cell-touching arm leaves `c`'s record verbatim; the field-write arms
(`incrementNonce`/`setPermissions`/`setVK`/`refusal`/`receiptArchive`) write a DISTINCT field, so
`field_setField_ne` keeps the anchor; the caveat-gated `setFieldA` is admitted only if the immutable
caveat passes — i.e. a `commitment_anchor` rewrite must be `new = old`, and a write to any OTHER slot
leaves the anchor untouched. `makeSovereign` aimed at `c` is the excluded arm. -/
theorem execFullA_anchorVal_preserved (s s' : RecChainedState) (fa : FullActionA) (c : CellId)
    (h : execFullA s fa = some s')
    (hlive : c ∈ s.kernel.accounts)
    (himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats c)
    (hok : anchorActionOK c fa) :
    fieldOf commitmentAnchorSlot (s'.kernel.cell c) = fieldOf commitmentAnchorSlot (s.kernel.cell c) := by
  cases fa with
  | balanceA t a =>
      obtain ⟨_, ⟨k', hk, h'⟩⟩ := recCexecAsset_factors t a (by simpa only [execFullA] using h)
      subst h'
      have hn : k' = { s.kernel with bal := k'.bal } := by
        unfold recKExecAsset at hk; split at hk
        · injection hk with hk; subst hk; rfl
        · exact absurd hk (by simp)
      rw [hn]
  | delegate del rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel del rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | revoke holder t =>
      simp only [execFullA, recCRevoke] at h; obtain ⟨rfl⟩ := h; rfl
  | mintA actor cell a amt =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | burnA actor cell a amt =>
      simp only [execFullA, recCBurnAsset] at h
      cases hk : recKBurnAsset s.kernel actor cell a amt with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKBurnAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | setFieldA actor cell f v =>
      -- the caveat-GATED write: `field_setField_ne` for f ≠ anchor; the `.immutable` caveat for f = anchor.
      have hstep : stateStepGuarded s f actor cell v = some s' := h
      have hadm : caveatsAdmit s.kernel f actor cell v = true := stateStepGuarded_admits hstep
      rw [execFullA_setFieldA_writeField h]
      by_cases hcell : c = cell
      · subst hcell
        by_cases hf : f = commitmentAnchorSlot
        · -- writing the anchor slot ITSELF: the immutable caveat forced `v = old` (`fieldOf`-level).
          subst hf
          have hmem : (.immutable commitmentAnchorSlot : SlotCaveat) ∈
              (s.kernel.slotCaveats c).filter (fun cav => cav.field == commitmentAnchorSlot) := by
            rw [List.mem_filter]
            exact ⟨himm, by rfl⟩
          have heval : (SlotCaveat.immutable commitmentAnchorSlot).eval actor
              (fieldOf commitmentAnchorSlot (s.kernel.cell c)) v = true := by
            have := List.all_eq_true.1 hadm _ hmem; simpa using this
          have hveq : v = fieldOf commitmentAnchorSlot (s.kernel.cell c) := by
            simpa [SlotCaveat.eval] using heval
          show fieldOf commitmentAnchorSlot
                ((writeField s.kernel commitmentAnchorSlot c (.int v)).cell c)
              = fieldOf commitmentAnchorSlot (s.kernel.cell c)
          have hcw : (writeField s.kernel commitmentAnchorSlot c (.int v)).cell c
              = setField commitmentAnchorSlot (s.kernel.cell c) (.int v) := by
            unfold writeField; simp only [if_pos]
          rw [hcw, setField_fieldOf]; exact hveq
        · -- writing a DIFFERENT slot: anchor read untouched.
          show fieldOf commitmentAnchorSlot ((writeField s.kernel f c (.int v)).cell c)
              = fieldOf commitmentAnchorSlot (s.kernel.cell c)
          exact fieldOf_of_field_eq
            (writeField_field_ne s.kernel f commitmentAnchorSlot c c (.int v) (fun he => hf he.symm))
      · -- the write targets a different cell entirely.
        show fieldOf commitmentAnchorSlot ((writeField s.kernel f cell (.int v)).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
        rw [writeField_cell_other s.kernel f cell c (.int v) hcell]
  | emitEventA actor cell topic data =>
      simp only [execFullA] at h
      by_cases hl : cell ∈ s.kernel.accounts
      · rw [if_pos hl] at h; simp only [emitStep, Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hl] at h; exact absurd h (by simp)
  | incrementNonceA actor cell n =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact fieldOf_of_field_eq
        (writeField_field_ne s.kernel nonceField commitmentAnchorSlot cell c (.int n) (by decide))
  | setPermissionsA actor cell p =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact fieldOf_of_field_eq
        (writeField_field_ne s.kernel permsField commitmentAnchorSlot cell c (.int p) (by decide))
  | setVKA actor cell vk =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact fieldOf_of_field_eq
        (writeField_field_ne s.kernel vkField commitmentAnchorSlot cell c (.int vk) (by decide))
  | introduceA intro rec t =>
      simp only [execFullA, recCDelegate] at h
      cases hk : recKDelegate s.kernel intro rec t with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegate at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | delegateAttenA del rec t keep =>
      simp only [execFullA, recCDelegateAtten] at h
      cases hk : recKDelegateAtten s.kernel del rec t keep with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with caps := k'.caps } := by
            unfold recKDelegateAtten at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | attenuateA actor idx keep =>
      simp only [execFullA, attenuateStepA] at h; obtain ⟨rfl⟩ := h; rfl
  | revokeDelegationA holder t =>
      simp only [execFullA, recCRevoke] at h; obtain ⟨rfl⟩ := h; rfl
  | exerciseA actor t inner =>
      simp only [execFullA] at h
      by_cases hf : innerFacetsAdmittedA s actor t inner = true
      · rw [if_pos hf] at h
        cases hg : exerciseStepA s actor t with
        | none => rw [hg] at h; exact absurd h (by simp)
        | some s1 =>
            rw [hg] at h
            obtain ⟨_, hs1⟩ := exerciseStepA_factors hg
            have hlive1 : c ∈ s1.kernel.accounts := by rw [hs1]; exact hlive
            have himm1 : .immutable commitmentAnchorSlot ∈ s1.kernel.slotCaveats c := by
              rw [hs1]; exact himm
            have hcell1 : s1.kernel.cell c = s.kernel.cell c := by rw [hs1]
            -- `exerciseStepA` only appends a log row (`s1.kernel = s.kernel`); the inner fold then
            -- runs `inner`, which the `exerciseA` guard requires to be anchor-safe for `c`.
            rw [hcell1.symm]
            exact execInnerA_anchorVal_preserved s1 s' inner c hlive1 h himm1
              (anchorListOK_of_exercise hok)
      · rw [if_neg hf] at h; exact absurd h (by simp)
  | createCellA actor newCell =>
      obtain ⟨_, hfresh, hs'⟩ := createCellChainA_factors (by simpa only [execFullA] using h)
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs'
      rw [createCellIntoAsset_cell_other s.kernel newCell c hne]
  | createCellFromFactoryA actor newCell vk =>
      obtain ⟨e, s1, _, _, hc, hs'⟩ :=
        createCellFromFactoryChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hs1⟩ := createCellChainA_factors hc
      have hne : c ≠ newCell := fun heq => hfresh (heq ▸ hlive)
      subst hs' hs1
      simp only [createCellIntoAsset, bornEmptyCellSlots, if_neg hne]
  | spawnA actor child target =>
      obtain ⟨s1, _, hc, hs'⟩ := spawnChainA_factors (by simpa only [execFullA] using h)
      obtain ⟨_, hfresh, hc'⟩ := createCellChainA_factors hc
      have hne : c ≠ child := fun heq => hfresh (heq ▸ hlive)
      subst hs' hc'
      show fieldOf commitmentAnchorSlot ((createCellIntoAsset s.kernel child).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      rw [createCellIntoAsset_cell_other s.kernel child c hne]
  | bridgeMintA actor cell a value =>
      simp only [execFullA, recCMintAsset] at h
      cases hk : recKMintAsset s.kernel actor cell a value with
      | none => rw [hk] at h; exact absurd h (by simp)
      | some k' =>
          commit_subst h hk
          have hn : k' = { s.kernel with bal := k'.bal } := by
            unfold recKMintAsset at hk; split at hk
            · injection hk with hk; subst hk; rfl
            · exact absurd hk (by simp)
          rw [hn]
  | noteSpendA nf actor spendProof =>
      simp only [execFullA, noteSpendChainA] at h
      by_cases hp : spendProof = true
      · rw [if_pos hp] at h
        cases hk : noteSpendNullifier s.kernel nf with
        | none => rw [hk] at h; exact absurd h (by simp)
        | some k' =>
            commit_subst h hk
            have hn : k' = { s.kernel with nullifiers := nf :: s.kernel.nullifiers } := by
              unfold noteSpendNullifier at hk; split at hk
              · exact absurd hk (by simp)
              · injection hk with hk; exact hk.symm
            rw [hn]
      · rw [if_neg hp] at h; exact absurd h (by simp)
  | noteCreateA cm actor =>
      simp only [execFullA, noteCreateChainA] at h
      option_inj at h; subst h
      show fieldOf commitmentAnchorSlot ((noteCreateCommitment s.kernel cm).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      unfold noteCreateCommitment; rfl
  | makeSovereignA actor cell =>
      -- THE EXCLUDED ARM: `anchorActionOK c (.makeSovereignA actor cell) = (cell ≠ c)`.
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := makeSovereignStep_factors h; subst hs'
      have hne : cell ≠ c := anchorActionOK_makeSovereign hok
      show fieldOf commitmentAnchorSlot ((makeSovereignKernel s.kernel cell).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      have hcell : (makeSovereignKernel s.kernel cell).cell c = s.kernel.cell c := by
        unfold makeSovereignKernel sovereignRebind
        simp only [if_neg (fun he : c = cell => hne he.symm)]
      rw [hcell]
  | refusalA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact fieldOf_of_field_eq
        (writeField_field_ne s.kernel refusalField commitmentAnchorSlot cell c (.int 1) (by decide))
  | receiptArchiveA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := stateStep_factors h; subst hs'
      exact fieldOf_of_field_eq
        (writeField_field_ne s.kernel lifecycleField commitmentAnchorSlot cell c (.int 1) (by decide))
  | cellSealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellSealChainA_factors h; subst hs'
      show fieldOf commitmentAnchorSlot ((setLifecycle s.kernel cell lcSealed).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      unfold setLifecycle; rfl
  | cellUnsealA actor cell =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellUnsealChainA_factors h; subst hs'
      show fieldOf commitmentAnchorSlot ((setLifecycle s.kernel cell lcLive).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      unfold setLifecycle; rfl
  | cellDestroyA actor cell ch =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := cellDestroyChainA_factors h; subst hs'
      show fieldOf commitmentAnchorSlot (({ (setLifecycle s.kernel cell lcDestroyed) with deathCert := _ }).cell c)
            = fieldOf commitmentAnchorSlot (s.kernel.cell c)
      unfold setLifecycle; rfl
  | refreshDelegationA actor child =>
      simp only [execFullA] at h
      obtain ⟨_, hs'⟩ := refreshDelegationChainA_factors h; subst hs'; rfl
  | pipelinedSendA actor =>
      simp only [execFullA, Option.some.injEq] at h; subst h; rfl

/-- **`execInnerA_anchorVal_preserved`** — the inner-effect fold preserves `c`'s anchor scalar when
every inner action is anchor-safe for `c`. Mutual with `execFullA_anchorVal_preserved`. -/
theorem execInnerA_anchorVal_preserved (s s' : RecChainedState) (inner : List FullActionA) (c : CellId)
    (hlive : c ∈ s.kernel.accounts)
    (h : execInnerA s inner = some s')
    (himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats c)
    (hok : anchorListOK c inner) :
    fieldOf commitmentAnchorSlot (s'.kernel.cell c) = fieldOf commitmentAnchorSlot (s.kernel.cell c) := by
  cases inner with
  | nil => simp only [execInnerA, Option.some.injEq] at h; subst h; rfl
  | cons a rest =>
      simp only [execInnerA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hoka : anchorActionOK c a := hok a List.mem_cons_self
          have hokrest : anchorListOK c rest := fun b hb => hok b (List.mem_cons_of_mem _ hb)
          -- liveness + the full caveat program (hence the immutable membership) persist across the step.
          obtain ⟨hlive1, hprog1⟩ :=
            execFullA_progLive_preserved s s1 a c (s.kernel.slotCaveats c) ha hlive rfl
          have himm1 : .immutable commitmentAnchorSlot ∈ s1.kernel.slotCaveats c := by
            rw [hprog1]; exact himm
          have hstep := execFullA_anchorVal_preserved s s1 a c ha hlive himm hoka
          have hrec := execInnerA_anchorVal_preserved s1 s' rest c hlive1 h himm1 hokrest
          rw [hrec, hstep]
end

/-- **`execFullTurnA_anchorVal_preserved`.** A committed per-asset full TURN whose action list
is anchor-safe for `c` preserves `c`'s `commitment_anchor` scalar (given `c` live + carrying the
immutable caveat). Induction on the action list, reusing `progLive_preserved` to carry liveness+caveat
across each step. -/
theorem execFullTurnA_anchorVal_preserved :
    ∀ (s s' : RecChainedState) (tt : List FullActionA) (c : CellId),
      execFullTurnA s tt = some s' → c ∈ s.kernel.accounts →
      .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats c → anchorListOK c tt →
        fieldOf commitmentAnchorSlot (s'.kernel.cell c) = fieldOf commitmentAnchorSlot (s.kernel.cell c)
  | s, s', [], c, h, _, _, _ => by
      simp only [execFullTurnA, Option.some.injEq] at h; subst h; rfl
  | s, s', a :: rest, c, h, hlive, himm, hok => by
      simp only [execFullTurnA] at h
      cases ha : execFullA s a with
      | none => rw [ha] at h; exact absurd h (by simp)
      | some s1 =>
          rw [ha] at h
          have hoka : anchorActionOK c a := hok a List.mem_cons_self
          have hokrest : anchorListOK c rest := fun b hb => hok b (List.mem_cons_of_mem _ hb)
          obtain ⟨hlive1, hprog1⟩ :=
            execFullA_progLive_preserved s s1 a c (s.kernel.slotCaveats c) ha hlive rfl
          have himm1 : .immutable commitmentAnchorSlot ∈ s1.kernel.slotCaveats c := by
            rw [hprog1]; exact himm
          have hstep := execFullA_anchorVal_preserved s s1 a c ha hlive himm hoka
          have hrec := execFullTurnA_anchorVal_preserved s1 s' rest c h hlive1 himm1 hokrest
          rw [hrec, hstep]

/-- **`execFullForestA_anchorVal_preserved` — THE ANCHOR-VALUE FOREST FRAME.** A committed
full FOREST that is anchor-safe for `c` (`anchorForestOK c f` — no `makeSovereign` aimed at `c`, even
nested inside an `exerciseA`) preserves `c`'s stored `commitment_anchor` scalar, provided `c` is live
and carries the `.immutable commitmentAnchorSlot` caveat. Through the pre-order bridge
`execFullForestA_eq_execFullTurnA`. This is the value-pinning frame the §B″ comment said was the
precise residual missing from `progLive_preserved`. -/
theorem execFullForestA_anchorVal_preserved (s s' : RecChainedState) (f : FullForestA) (c : CellId)
    (h : execFullForestA s f = some s') (hlive : c ∈ s.kernel.accounts)
    (himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats c)
    (hok : anchorForestOK c f) :
    fieldOf commitmentAnchorSlot (s'.kernel.cell c) = fieldOf commitmentAnchorSlot (s.kernel.cell c) := by
  rw [execFullForestA_eq_execFullTurnA] at h
  exact execFullTurnA_anchorVal_preserved s s' (lowerForestA f) c h hlive himm hok

/-- Anchor-value frame phrased at the `sgmAnchor`/`cwmAnchor` accessor level (same statement; the
mutual theorem already lands at the `fieldOf` level). -/
theorem execFullForestA_anchorOf_preserved (s s' : RecChainedState) (f : FullForestA) (c : CellId)
    (h : execFullForestA s f = some s') (hlive : c ∈ s.kernel.accounts)
    (himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats c)
    (hok : anchorForestOK c f) :
    fieldOf commitmentAnchorSlot (s'.kernel.cell c) = fieldOf commitmentAnchorSlot (s.kernel.cell c) :=
  execFullForestA_anchorVal_preserved s s' f c h hlive himm hok

/-! ## §B′ — `sgmWF` kernel predicates (volume bound + anchor tag). -/

def sgmVolumeSpent (k : RecordKernelState) : Int :=
  fieldOf volumeSpentSlot (k.cell mandateCell)

def sgmAnchor (k : RecordKernelState) : Int :=
  fieldOf commitmentAnchorSlot (k.cell mandateCell)

def sgmVolumeBound (k : RecordKernelState) : Bool :=
  let spent := sgmVolumeSpent k
  decide (0 ≤ spent ∧ spent ≤ (demoMandate.volumeBudget.ceiling : Int))

def sgmAnchorIs (k : RecordKernelState) (anchor : Int) : Bool :=
  decide (sgmAnchor k = anchor)

/-- Mandate cell carries the published caveat program (immutable anchor + monotonic/bounded volume). -/
def sgmMandateProgramOK (k : RecordKernelState) : Prop :=
  k.slotCaveats mandateCell = mandateCaveats

/-- **Strong step-legal invariant (Phase B)** — volume spent ≤ ceiling AND caveat program installed. -/
def sgmWFStrong (k : RecordKernelState) : Prop :=
  sgmVolumeBound k = true ∧ sgmMandateProgramOK k

/-- **Strong bucket invariant (Phase B)** — commitment anchor matches expected tag AND caveat program. -/
def sgmInBucketStrong (k : RecordKernelState) (bucket : Int) : Prop :=
  sgmAnchorIs k bucket = true ∧ sgmMandateProgramOK k

/-- **`sgmWF` — NON-VACUOUS Hatchery contract invariant.** The mandate cell stays a LIVE account AND its
published per-slot caveat program (immutable anchor + monotonic/bounded volume) remains installed — so
the executor's per-slot teeth (`sgm_over_debit_rejected_*`, immutable-anchor rewrite rejection) are
enforced on the cell for its WHOLE life, along EVERY adversarial `trajG`. Carried by the generic
`execFullForestA_progLive_preserved` frame (no `True` filler). -/
def sgmWF (k : RecordKernelState) : Prop :=
  mandateCell ∈ k.accounts ∧ sgmMandateProgramOK k

/-- **`sgmInBucket` — NON-VACUOUS bucket-binding invariant (program-live, UNCONDITIONAL).** Carries the
program-live core (mandate cell live + its published per-slot caveat program installed) along EVERY
forest. The `bucket` tag is the binding's domain: the binding to `bucket` is ENFORCED for life by the
persisted `.immutable commitmentAnchorSlot` caveat inside `mandateCaveats`. Carried by
`execFullForestA_progLive_preserved`. The LITERAL anchor-VALUE conjunct (`sgmAnchor = bucket`) is the
STRONGER predicate `sgmInBucketStrong`, now carried along anchor-safe schedules by
`sgmBucketStrong_traj_carries` / `sgm_bucket_strong_forever` (the second cell-record frame
`execFullForestA_anchorOf_preserved`, excluding the one un-caveat-gated `makeSovereign` rebind). -/
def sgmInBucket (_k : RecordKernelState) (_bucket : Int) : Prop :=
  mandateCell ∈ _k.accounts ∧ sgmMandateProgramOK _k

instance sgmWFStrongDecidable (k : RecordKernelState) : Decidable (sgmWFStrong k) := by
  unfold sgmWFStrong sgmMandateProgramOK; infer_instance

instance sgmInBucketStrongDecidable (k : RecordKernelState) (bucket : Int) :
    Decidable (sgmInBucketStrong k bucket) := by
  unfold sgmInBucketStrong sgmMandateProgramOK; infer_instance

theorem sgmWFStrong_of_mandate_cell_eq {k k' : RecordKernelState}
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hwf : sgmWFStrong k) : sgmWFStrong k' := by
  rcases hwf with ⟨hvol, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmVolumeBound sgmVolumeSpent at hvol ⊢
    simp [sgmVolumeSpent, hc] at hvol ⊢
    exact hvol
  · unfold sgmMandateProgramOK at hprog ⊢
    simpa [hcav] using hprog

theorem sgmInBucketStrong_of_mandate_cell_eq {k k' : RecordKernelState} (bucket : Int)
    (hc : k'.cell mandateCell = k.cell mandateCell) (hcav : k'.slotCaveats mandateCell = k.slotCaveats mandateCell)
    (hb : sgmInBucketStrong k bucket) : sgmInBucketStrong k' bucket := by
  rcases hb with ⟨hanchor, hprog⟩
  refine ⟨?_, ?_⟩
  · unfold sgmAnchorIs sgmAnchor at hanchor ⊢
    simp [sgmAnchor, hc] at hanchor ⊢
    exact hanchor
  · unfold sgmMandateProgramOK at hprog ⊢
    simpa [hcav] using hprog

/-- **`sgmWF_traj_carries` — NON-VACUOUS carry.** A committed forest keeps the mandate cell
live AND its published caveat program installed. The generic frame `execFullForestA_progLive_preserved`
instantiated at `mandateCell`/`mandateCaveats`. -/
theorem sgmWF_traj_carries (s s' : RecChainedState) (cf : FullForestA)
    (h : execFullForestA s cf = some s') (hwf : sgmWF s.kernel) : sgmWF s'.kernel := by
  obtain ⟨hlive, hprog⟩ := hwf
  exact execFullForestA_progLive_preserved s s' cf mandateCell mandateCaveats h hlive hprog

/-- **`sgmBucket_traj_carries` — NON-VACUOUS carry.** Same generic frame: the bucket binding's
enforcement (live cell + installed immutable-anchor caveat program) persists along every forest. -/
theorem sgmBucket_traj_carries (s s' : RecChainedState) (cf : FullForestA) (bucket : Int)
    (h : execFullForestA s cf = some s') (hb : sgmInBucket s.kernel bucket) :
    sgmInBucket s'.kernel bucket := by
  obtain ⟨hlive, hprog⟩ := hb
  exact execFullForestA_progLive_preserved s s' cf mandateCell mandateCaveats h hlive hprog

/-- The mandate program installs the `.immutable commitmentAnchorSlot` caveat — so a cell carrying
`mandateCaveats` carries the immutable-anchor caveat (the precondition of the anchor-value frame). -/
theorem mandateCaveats_has_immutable_anchor :
    (.immutable commitmentAnchorSlot : SlotCaveat) ∈ mandateCaveats := by
  simp [mandateCaveats]

/-- **`sgmBucketStrong_traj_carries` — the VALUE-PINNING carry.** A committed forest that is
anchor-safe for the mandate cell (no `makeSovereign` aimed at it — the sole un-caveat-gated rebind that
drops fields) preserves the LITERAL bucket binding `sgmAnchor = bucket`, not merely program-liveness.
This is the residual the §B″ note said was missing from the program-live carry — now PROVED via the
`execFullForestA_anchorOf_preserved` frame. The `mandateCaveats` program supplies the immutable-anchor
caveat the frame needs (`mandateCaveats_has_immutable_anchor`). -/
theorem sgmBucketStrong_traj_carries (s s' : RecChainedState) (cf : FullForestA) (bucket : Int)
    (h : execFullForestA s cf = some s') (hb : sgmInBucketStrong s.kernel bucket)
    (hok : anchorForestOK mandateCell cf) (hlive : mandateCell ∈ s.kernel.accounts) :
    sgmInBucketStrong s'.kernel bucket := by
  obtain ⟨hanchor, hprog⟩ := hb
  have himm : .immutable commitmentAnchorSlot ∈ s.kernel.slotCaveats mandateCell := by
    rw [show s.kernel.slotCaveats mandateCell = mandateCaveats from hprog]
    exact mandateCaveats_has_immutable_anchor
  have hanchorEq : fieldOf commitmentAnchorSlot (s'.kernel.cell mandateCell)
      = fieldOf commitmentAnchorSlot (s.kernel.cell mandateCell) :=
    execFullForestA_anchorOf_preserved s s' cf mandateCell h hlive himm hok
  obtain ⟨_, hprog'⟩ :=
    execFullForestA_progLive_preserved s s' cf mandateCell mandateCaveats h hlive hprog
  refine ⟨?_, hprog'⟩
  unfold sgmAnchorIs sgmAnchor at hanchor ⊢
  rw [hanchorEq]; exact hanchor

/-! ## §C — Stingray volume-budget demo (PUT debits exhaust slice). -/

def demoVolume : Slice := demoMandate.volumeBudget

theorem sgm_put_debit_fits_slice :
    (demoVolume.tryDebit demoMandate.putCost).isSome = true := by
  rw [tryDebit_isSome_iff]
  simp [demoVolume, demoMandate, Slice.remaining]

theorem sgm_double_put_exhausts_slice :
    ((demoVolume.tryDebit demoMandate.putCost).bind
      (fun s' => s'.tryDebit demoMandate.putCost)).isSome = true := by
  have h1 : demoVolume.tryDebit demoMandate.putCost = some { ceiling := 10, spent := 5 } := by
    unfold Slice.tryDebit; simp [demoVolume, demoMandate, Slice.remaining]
  have h2 : ({ ceiling := 10, spent := 5 } : Slice).tryDebit demoMandate.putCost =
      some { ceiling := 10, spent := 10 } := by
    unfold Slice.tryDebit; simp [demoMandate, Slice.remaining]
  simpa [h1, h2]

/-! ## §D — NON-VACUITY: authorize PUT on prefix, reject GET above clearance, slice exhaust. -/

def sgm0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun c =>
          if c = mandateCell then
            .record [("balance", .int 0), (objectKeySlot, .int 0), (lastOpSlot, .int (-1)),
                     (volumeSpentSlot, .int 0), (commitmentAnchorSlot, .int demoMandate.anchor)]
          else .record [("balance", .int 0)]
        caps := fun _ => []
        bal := fun c a => if c = 0 then (if a = 0 then 100 else if a = 1 then 7 else 0) else 0
        slotCaveats := fun c => if c = mandateCell then mandateCaveats else [] }
    log := [] }

abbrev demoKeyCode : Int := 101
abbrev demoBlobHash : Int := 3735928559

def sgmPutCommitted : Option RecChainedState :=
  sgmStorageChain sgm0 mandateActor demoKeyCode (StorageOp.PUT.toInt) demoBlobHash

def sgmPutDebited : Option RecChainedState :=
  sgmPutCommitted.bind (fun s => execFullForestA s (sgmExecDebitVolume mandateActor 5))

#guard ({ volume := demoVolume, anchor := demoMandate.anchor } : SgmRuntime).WF
#guard (sgmAdmitM demoMandate { volume := demoVolume, anchor := demoMandate.anchor } demoPutReq).isSome
#guard (sgmAdmitM demoMandate { volume := demoVolume, anchor := demoMandate.anchor } demoBadPutReq).isSome == false
#guard (sgmAdmitM guestMandate { volume := demoVolume, anchor := demoMandate.anchor } demoGetReq).isSome == false
#guard putPrefixOK demoMandate "uploads/doc.txt"
#guard getClearanceOK demoMandate
#guard getClearanceOK guestMandate == false

#guard (sgmPutCommitted.isSome)
#guard (sgmPutCommitted.map (fun s => fieldOf objectKeySlot (s.kernel.cell mandateCell))) == some demoKeyCode
#guard (sgmPutCommitted.map (fun s => fieldOf lastOpSlot (s.kernel.cell mandateCell))) == some 1
#guard (caveatsAdmit sgm0.kernel volumeSpentSlot mandateActor mandateCell 11) == false
#guard ((execFullForestA sgm0 (sgmExecDebitVolume mandateActor 11)).isSome) == false

#guard (demoVolume.tryDebit demoMandate.putCost).isSome
#guard ((demoVolume.tryDebit demoMandate.putCost).bind
        (fun s' => s'.tryDebit demoMandate.putCost)).isSome
#guard (((demoVolume.tryDebit demoMandate.putCost).bind
          (fun s' => s'.tryDebit demoMandate.putCost)).bind
         (fun s'' => s''.tryDebit demoMandate.putCost)).isSome == false

#guard ((sgmPutDebited.map (fun s => recTotalAsset s.kernel payAsset)).getD 0) == 100
#guard (sgmVolumeBound sgm0.kernel)
#guard (sgmAnchorIs sgm0.kernel (demoMandate.anchor : Int))
#guard (sgmWFStrong sgm0.kernel)
#guard (sgmInBucketStrong sgm0.kernel (demoMandate.anchor : Int))
-- NON-VACUITY of the carried invariant: the program-live invariant HOLDS at the genesis state
-- (mandate cell live + caveat program installed), so the safety crown is non-trivially applicable.
#guard (decide (mandateCell ∈ sgm0.kernel.accounts) && (sgm0.kernel.slotCaveats mandateCell == mandateCaveats))

#assert_axioms execFullA_progLive_preserved
#assert_axioms execFullForestA_progLive_preserved
#assert_axioms sgm_volume_legal_forever
#assert_axioms sgm_over_debit_rejected_exec
#assert_axioms sgm_caveatsAdmit_op_eq_table
#assert_axioms sgm_commit_iff_op_admit
#assert_axioms sgm_chain_conserves
#assert_axioms sgm_pay_supply_forever
#assert_axioms sgm_put_debit_fits_slice
#assert_axioms sgm_double_put_exhausts_slice
#assert_axioms sgmWFStrong_of_mandate_cell_eq
#assert_axioms sgmInBucketStrong_of_mandate_cell_eq
#assert_axioms sgmWF_traj_carries
#assert_axioms sgmBucket_traj_carries

end Dregg2.Apps.StorageGatewayMandate