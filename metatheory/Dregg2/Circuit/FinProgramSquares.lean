/-
# Dregg2.Circuit.FinProgramSquares — DEBT-B step 3B: the deployed programs' commuting squares.

`Dregg2/Circuit/FinInterp.lean` proved the per-CONSTRUCTOR squares:
  * `denote_finInterp` for the 10-constructor side-condition-free `Pure` fragment
    (skip/guard/insFresh/checkLe/checkSubset/setNullifiers/setRevoked/setCommitments/setFactories/seq);
  * `denote_finSetCaps`/`denote_finSetBal`/`denote_finSetLifecycle`/`denote_finSetDeathCert`/
    `denote_finSetSlotCaveats`/`denote_finSetDelegations`/`denote_finSetCell` for the whole-function writers,
    each gated on an EXPLICIT `FiniteDiff`/non-default side condition, and `denote_seq_compose` for `seq`.

This file DISCHARGES those side conditions for the REAL deployed `*Stmt` programs and ASSEMBLES each
program's end-to-end square. The measured empirical fact — every whole-function writer in the deployed
programs is used with a POINT diff off the current field — is here PROVED as a theorem per writer
(`grant_finiteDiff` reused from `FinInterp`; `removeEdgeCaps_finiteDiff`, `recDelegateCaps_finiteDiff`,
`introduceCaps_finiteDiff`, `attenuateSlotF_finiteDiff`, `recTransferBal_finiteDiff`,
`setLifecycleField_fd`, `refreshDelegationsMap_finiteDiff`, `cellDestroyLifecycle_fd`,
`cellDestroyDeathCert_fd` — never assumed). The `setCell` non-default obligation is discharged by
`setBalance_ne_nil`/`setField_ne_nil` (both field-writers land a non-empty record).

Each `<prog>Stmt_square` states the deployed program's operational commuting square — R1's `hpres` gate,
`FinKernelState.denote_surjective_on_reachable`, for that effect term. `createCellStmt` /
`createCellFromFactoryStmt` are EXCLUDED (they use `allocCell`, whose `bal`-column predicate-erase is
unblocked by step 3A's `filterErase` primitive — flagged pending-3A here, not implemented). `setDelegate`
has NO deployed program (only `CompileFold`'s stub), so its constructor square is vacuously unused.

Builds ON the committed `FinInterp` + Argus effect terms verbatim; edits NOTHING committed. Sorry-free.
-/
import Dregg2.Circuit.FinInterp
import Dregg2.Circuit.Argus.Effects.EmitEvent
import Dregg2.Circuit.Argus.Effects.ExerciseViaCapability
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Circuit.Argus.Effects.NoteSpendCompose
import Dregg2.Circuit.Argus.Effects.NoteCreate
import Dregg2.Circuit.Argus.Effects.PipelinedSend
import Dregg2.Circuit.Argus.Effects.Noop
import Dregg2.Circuit.Argus.Effects.Introduce
import Dregg2.Circuit.Argus.Effects.Delegate
import Dregg2.Circuit.Argus.Effects.DelegateAtten
import Dregg2.Circuit.Argus.Effects.Attenuate
import Dregg2.Circuit.Argus.Effects.RevokeDelegation
import Dregg2.Circuit.Argus.Effects.RefreshDelegation
import Dregg2.Circuit.Argus.Effects.BalanceA
import Dregg2.Circuit.Argus.Effects.BridgeMint
import Dregg2.Circuit.Argus.Effects.CellSeal
import Dregg2.Circuit.Argus.Effects.CellUnseal
import Dregg2.Circuit.Argus.Effects.CellDestroy
import Dregg2.Circuit.Argus.Effects.MakeSovereign
import Dregg2.Circuit.Argus.Effects.IncrementNonce
import Dregg2.Circuit.Argus.Effects.SetPermissions
import Dregg2.Circuit.Argus.Effects.SetField
import Dregg2.Circuit.Argus.Effects.SetVerificationKey
import Dregg2.Circuit.Argus.Effects.ReceiptArchive
import Dregg2.Circuit.Argus.Effects.Refusal

namespace Dregg2.Circuit.FinProgramSquares

open Dregg2.Exec
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Exec.TurnExecutorFull
  (setLifecycle attenuateSlotF lcLive lcSealed lcDestroyed permsField vkField refusalField
   lifecycleField commitmentField stateCommitment sovereignNonce)
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinInterp
open Dregg2.Circuit.FinInterp.CanonMap
open Dregg2.Circuit.Argus
open Dregg2.Circuit.Spec.AuthorityRevocation (removeEdgeCaps)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (recDelegateCaps)
open Dregg2.Circuit.Spec.RefreshDelegation (refreshDelegationsMap)
open Dregg2.Circuit.Spec.CellStateMonotone (incNonceCellMap)
open Dregg2.Circuit.Argus.Effects.EmitEvent (emitEventStmt emitEventGuardB)
open Dregg2.Circuit.Argus.Effects.ExerciseViaCapability (exerciseStmt exerciseGuardB)
open Dregg2.Circuit.Argus.Effects.NoteCreate (noteCreateStmt)
open Dregg2.Circuit.Argus (noteSpendStmt)
open Dregg2.Circuit.Argus.Effects.NoteSpendCompose (noteSpendComposeStmt)
open Dregg2.Circuit.Argus.Effects.PipelinedSend (pipelinedSendStmt)
open Dregg2.Circuit.Argus.Effects.Noop (noopStmt)
open Dregg2.Circuit.Argus.Effects.Introduce (introduceStmt introduceGate introduceCaps)
open Dregg2.Circuit.Argus.Effects.Delegate (delegateStmt delegateGuardB)
open Dregg2.Circuit.Argus.Effects.DelegateAtten
  (delegateAttenStmt delAttenGuardB grantedDelRightsSet heldDelRightsSet)
open Dregg2.Circuit.Argus.Effects.Attenuate (attenuateStmt grantedRightsSet heldRightsSet)
open Dregg2.Circuit.Argus.Effects.RevokeDelegation (revokeDelegationStmt)
open Dregg2.Circuit.Argus.Effects.RefreshDelegation (refreshDelegationStmt refreshDelegationGuard)
open Dregg2.Circuit.Argus.Effects.BalanceA (balanceAStmt balanceAGuard)
open Dregg2.Circuit.Argus.Effects.BridgeMint (bridgeMintStmt bridgeMintGuard)
open Dregg2.Circuit.Argus.Effects.CellSeal (cellSealStmt cellSealGuard)
open Dregg2.Circuit.Argus.Effects.CellUnseal (cellUnsealStmt cellUnsealGuard)
open Dregg2.Circuit.Argus.Effects.CellDestroy (cellDestroyStmt cellDestroyGuard)
open Dregg2.Circuit.Argus.Effects.MakeSovereign (makeSovereignStmt makeSovereignGuard)
open Dregg2.Circuit.Argus.Effects.IncrementNonce (incrementNonceStmt incrementNonceGuardB)
open Dregg2.Circuit.Argus.Effects.SetPermissions (setPermissionsStmt setPermsGuardB)
open Dregg2.Circuit.Argus.Effects.SetField (setFieldStmt setFieldGuard)
open Dregg2.Circuit.Argus.Effects.SetVerificationKey (setVerificationKeyStmt setVerificationKeyGuard)
open Dregg2.Circuit.Argus.Effects.ReceiptArchive (receiptArchiveStmt receiptArchiveGuard)
open Dregg2.Circuit.Argus.Effects.Refusal (refusalStmt refusalGuard)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — GENERIC ASSEMBLY GLUE (built on the committed `denote_seq_compose` + leaf squares).

Every deployed program is a `seq` of a `Pure` prefix (`guard`/`checkSubset`) and one or two writers.
`pureThenSquare` composes a `Pure` prefix with ANY proven suffix square; `writerLeaf` folds a leaf
writer square (with its FiniteDiff/non-default side condition already discharged) into the shape
`denote_seq_compose` consumes; `pureThenWriter_square` is the common single-writer-after-pure-prefix case. -/

/-- Fold a writer leaf square (`some (denote (finW g)) = interp wStmt (denote g)`) into the
`Option.map`-shaped hypothesis `denote_seq_compose` consumes. -/
theorem writerLeaf {wStmt : RecStmt} {finW : FinKernelState → FinKernelState}
    (hw : ∀ g, some (denote (finW g)) = interp wStmt (denote g)) (g : FinKernelState) :
    (some (finW g)).map denote = interp wStmt (denote g) := by
  rw [Option.map_some]; exact hw g

/-- Compose a `Pure` prefix `p` (interpreted by `finInterp`) with ANY proven suffix square. `hp` is an
autoParam so it is discharged AFTER `p` is pinned by the expected type (guard/checkSubset ⇒ `Pure` = True). -/
theorem pureThenSquare {p suffix : RecStmt}
    {finS : FinKernelState → Option FinKernelState}
    (hs : ∀ g, (finS g).map denote = interp suffix (denote g)) (f : FinKernelState)
    (hp : Pure p := by first | exact trivial | exact ⟨trivial, trivial⟩) :
    ((finInterp p f).bind finS).map denote = interp (.seq p suffix) (denote f) :=
  denote_seq_compose (fun g => denote_finInterp p hp g) hs f

/-- The common shape: a `Pure` prefix `p` then a single writer leaf. -/
theorem pureThenWriter_square {p wStmt : RecStmt}
    {finW : FinKernelState → FinKernelState}
    (hw : ∀ g, some (denote (finW g)) = interp wStmt (denote g)) (f : FinKernelState)
    (hp : Pure p := by first | exact trivial | exact ⟨trivial, trivial⟩) :
    ((finInterp p f).bind (fun f' => some (finW f'))).map denote
      = interp (.seq p wStmt) (denote f) :=
  denote_seq_compose (fun g => denote_finInterp p hp g) (writerLeaf hw) f

/-! ## §1 — the `setCell` NON-DEFAULT obligation: the two field-writers land a non-empty record.

`finSetCell` needs each written leaf to be `≠ .record []` (the sparse `insertNZ` sparsity condition). The
two field-write primitives the deployed programs use — `setBalance` (RecordKernel) and `setField`
(EffectsState) — ALWAYS produce a `.record (nonempty)`, so the obligation holds for every leaf. -/

/-- `setBalance`'s field-list is never empty. -/
theorem setBalanceList_ne_nil : ∀ (fs : List (FieldName × Value)) (v : Int),
    setBalance.setBalanceList fs v ≠ [] := by
  intro fs v
  cases fs with
  | nil => simp [setBalance.setBalanceList]
  | cons hd tl =>
      obtain ⟨k, x⟩ := hd
      simp only [setBalance.setBalanceList]
      split <;> simp

/-- `setBalance cell v` is a non-empty record (the transfer/mint/burn cell leaf is non-default). -/
theorem setBalance_ne_nil (cell : Value) (v : Int) : setBalance cell v ≠ Value.record [] := by
  cases cell with
  | record fs => simp only [setBalance, ne_eq, Value.record.injEq]; exact setBalanceList_ne_nil fs v
  | int n => simp [setBalance]
  | dig n => simp [setBalance]
  | sym n => simp [setBalance]

/-- `setField`'s field-list is never empty. -/
theorem setFieldList_ne_nil : ∀ (fld : FieldName) (fs : List (FieldName × Value)) (v : Value),
    setField.setFieldList fld fs v ≠ [] := by
  intro fld fs v
  cases fs with
  | nil => simp [setField.setFieldList]
  | cons hd tl =>
      obtain ⟨k, x⟩ := hd
      simp only [setField.setFieldList]
      split <;> simp

/-- `setField fld cell v` is a non-empty record (the metadata-write cell leaf is non-default). -/
theorem setField_ne_nil (fld : FieldName) (cell : Value) (v : Value) :
    setField fld cell v ≠ Value.record [] := by
  cases cell with
  | record fs => simp only [setField, ne_eq, Value.record.injEq]; exact setFieldList_ne_nil fld fs v
  | int n => simp [setField]
  | dig n => simp [setField]
  | sym n => simp [setField]

/-- The transfer leaf `recTransfer` is non-default on the touched pair `{src, dst}` (both branches are
`setBalance`). -/
theorem transfer_leaf_nd (turn : Turn) (g : FinKernelState) :
    ∀ c ∈ ({turn.src, turn.dst} : Finset CellId).toList,
      recTransfer (denote g).cell turn.src turn.dst turn.amt c ≠ Value.record [] := by
  intro c hc
  rw [Finset.mem_toList, Finset.mem_insert, Finset.mem_singleton] at hc
  simp only [recTransfer]
  rcases hc with h | h
  · rw [if_pos h]; exact setBalance_ne_nil _ _
  · by_cases hs : c = turn.src
    · rw [if_pos hs]; exact setBalance_ne_nil _ _
    · rw [if_neg hs, if_pos h]; exact setBalance_ne_nil _ _

/-- The incrementNonce leaf is non-default on the touched cell (a `setField` write on the `if`-true arm). -/
theorem incNonce_leaf_nd (cell : CellId) (n : Int) (g : FinKernelState) :
    ∀ c ∈ ({cell} : Finset CellId).toList, incNonceCellMap (denote g) cell n c ≠ Value.record [] := by
  intro c hc
  rw [Finset.mem_toList, Finset.mem_singleton] at hc
  subst hc
  simp only [incNonceCellMap]
  split
  · exact setField_ne_nil _ _ _
  · rename_i hne; exact (hne trivial).elim

/-! ## §2 — the FiniteDiff obligations, PROVED per deployed writer (never assumed).

Each theorem below shows the deployed whole-function write agrees with the current field OFF an explicit
touched `Finset` — i.e. it IS a bounded point diff, discharging the §3 `FinInterp` side condition. -/

/-- `removeEdgeCaps` (revoke) is a single-slot diff off `{holder}`. -/
theorem removeEdgeCaps_finiteDiff (holder t : CellId) (f : FinKernelState) :
    ∀ l, l ∉ ({holder} : Finset Label) →
      removeEdgeCaps (denote f).caps holder t l = (denote f).caps l := by
  intro l hl
  simp only [Finset.mem_singleton] at hl
  simp only [removeEdgeCaps, if_neg hl]

/-- `recDelegateCaps` (delegate) is the `grant` point diff off `{recp}` (via the committed
`grant_finiteDiff`). -/
theorem recDelegateCaps_finiteDiff (del recp t : CellId) (f : FinKernelState) :
    ∀ l, l ∉ ({recp} : Finset Label) →
      recDelegateCaps (denote f).caps del recp t l = (denote f).caps l := by
  intro l hl
  simp only [recDelegateCaps]
  exact grant_finiteDiff recp (heldCapTo (denote f).caps del t) f l hl

/-- `introduceCaps` (introduce) is the `grant` point diff off `{recp}`. -/
theorem introduceCaps_finiteDiff (introd recp t : CellId) (f : FinKernelState) :
    ∀ l, l ∉ ({recp} : Finset Label) →
      introduceCaps introd recp t (denote f) l = (denote f).caps l := by
  intro l hl
  simp only [introduceCaps]
  exact grant_finiteDiff recp (heldCapTo (denote f).caps introd t) f l hl

/-- `attenuateSlotF` (attenuate) is a single-slot diff off `{actor}`. -/
theorem attenuateSlotF_finiteDiff (actor : CellId) (idx : Nat) (keep : List Auth) (f : FinKernelState) :
    ∀ l, l ∉ ({actor} : Finset Label) →
      attenuateSlotF (denote f).caps actor idx keep l = (denote f).caps l := by
  intro l hl
  simp only [Finset.mem_singleton] at hl
  simp only [attenuateSlotF, if_neg hl]

/-- `recTransferBal` (balanceA / bridgeMint) is a two-key diff off `{toLex (src,a), toLex (dst,a)}` in
the `bal` ledger: it touches ONLY the moved asset's two rows. -/
theorem recTransferBal_finiteDiff (src dst : CellId) (a : AssetId) (amt : ℤ) (f : FinKernelState) :
    ∀ key, key ∉ ({toLex (src, a), toLex (dst, a)} : Finset BalKey) →
      recTransferBal (denote f).bal src dst a amt (ofLex key).1 (ofLex key).2
        = (denote f).bal (ofLex key).1 (ofLex key).2 := by
  intro key hkey
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkey
  obtain ⟨h1, h2⟩ := hkey
  by_cases hb : (ofLex key).2 = a
  · have hcs : (ofLex key).1 ≠ src := by
      intro hc
      apply h1
      have hpair : ofLex key = (src, a) := by
        apply Prod.ext
        · exact hc
        · exact hb
      rw [← toLex_ofLex key, hpair]
    have hcd : (ofLex key).1 ≠ dst := by
      intro hc
      apply h2
      have hpair : ofLex key = (dst, a) := by
        apply Prod.ext
        · exact hc
        · exact hb
      rw [← toLex_ofLex key, hpair]
    simp only [recTransferBal, if_pos hb, if_neg hcs, if_neg hcd]
  · simp only [recTransferBal, if_neg hb]

/-- The cellSeal/cellUnseal lifecycle write `(setLifecycle k cell lc).lifecycle` is a single-cell diff
off `{cell}`. -/
theorem setLifecycleField_fd (cell : CellId) (lc : Nat) (g : FinKernelState) :
    ∀ c, c ∉ ({cell} : Finset CellId) →
      (setLifecycle (denote g) cell lc).lifecycle c = (denote g).lifecycle c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  show (if c = cell then lc else (denote g).lifecycle c) = (denote g).lifecycle c
  rw [if_neg hc]

/-- The cellDestroy lifecycle write is a single-cell diff off `{cell}`. -/
theorem cellDestroyLifecycle_fd (cell : CellId) (g : FinKernelState) :
    ∀ c, c ∉ ({cell} : Finset CellId) →
      (fun (k : RecordKernelState) c => if c = cell then lcDestroyed else k.lifecycle c) (denote g) c
        = (denote g).lifecycle c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [if_neg hc]

/-- The cellDestroy death-certificate write is a single-cell diff off `{cell}`. -/
theorem cellDestroyDeathCert_fd (cell : CellId) (certHash : Nat) (g : FinKernelState) :
    ∀ c, c ∉ ({cell} : Finset CellId) →
      (fun (k : RecordKernelState) c => if c = cell then certHash else k.deathCert c) (denote g) c
        = (denote g).deathCert c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [if_neg hc]

/-- `refreshDelegationsMap` (refreshDelegation) is a single-child diff off `{child}`. -/
theorem refreshDelegationsMap_finiteDiff (child : CellId) (f : FinKernelState) :
    ∀ c, c ∉ ({child} : Finset CellId) →
      refreshDelegationsMap (denote f) child c = (denote f).delegations c := by
  intro c hc
  simp only [Finset.mem_singleton] at hc
  simp only [refreshDelegationsMap, if_neg hc]

/-! ## §3 — the DEPLOYED PROGRAM SQUARES. Each `<prog>Stmt_square` is R1's `hpres` for that effect term:
the finite operational step (built from the §0 glue + the discharged side conditions) denotes to
`interp <prog>`. -/

/-! ### §3a — the `Pure`-fragment programs (no writer; `denote_finInterp` directly). -/

theorem emitEventStmt_square (cell : CellId) (f : FinKernelState) :
    (finInterp (emitEventStmt cell) f).map denote = interp (emitEventStmt cell) (denote f) := by
  unfold emitEventStmt; refine denote_finInterp _ ?_ f; trivial

theorem exerciseStmt_square (actor target : CellId) (f : FinKernelState) :
    (finInterp (exerciseStmt actor target) f).map denote
      = interp (exerciseStmt actor target) (denote f) := by
  unfold exerciseStmt; refine denote_finInterp _ ?_ f; trivial

theorem noteSpendStmt_square (nf : Nat) (f : FinKernelState) :
    (finInterp (noteSpendStmt nf) f).map denote = interp (noteSpendStmt nf) (denote f) := by
  unfold noteSpendStmt; refine denote_finInterp _ ?_ f; trivial

theorem pipelinedSendStmt_square (actor : CellId) (f : FinKernelState) :
    (finInterp (pipelinedSendStmt actor) f).map denote
      = interp (pipelinedSendStmt actor) (denote f) := by
  unfold pipelinedSendStmt; refine denote_finInterp _ ?_ f; trivial

theorem noopStmt_square (f : FinKernelState) :
    (finInterp noopStmt f).map denote = interp noopStmt (denote f) := by
  unfold noopStmt; refine denote_finInterp _ ?_ f; trivial

theorem noteCreateStmt_square (cm : Nat) (f : FinKernelState) :
    (finInterp (noteCreateStmt cm) f).map denote = interp (noteCreateStmt cm) (denote f) := by
  unfold noteCreateStmt; refine denote_finInterp _ ?_ f; trivial

theorem noteSpendComposeStmt_square (nf : Nat) (spendProof : Bool) (f : FinKernelState) :
    (finInterp (noteSpendComposeStmt nf spendProof) f).map denote
      = interp (noteSpendComposeStmt nf spendProof) (denote f) := by
  unfold noteSpendComposeStmt noteSpendStmt
  refine denote_finInterp _ ?_ f
  exact ⟨trivial, trivial⟩

/-! ### §3b — the cap-graph (`setCaps`) programs. -/

theorem introduceStmt_square (introd recp t : CellId) (f : FinKernelState) :
    ((finInterp (.guard (introduceGate introd t)) f).bind
      (fun f' => some (finSetCaps (introduceCaps introd recp t) {recp} f'))).map denote
      = interp (introduceStmt introd recp t) (denote f) := by
  unfold introduceStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCaps (introduceCaps introd recp t) {recp} g
      (introduceCaps_finiteDiff introd recp t g)) f

theorem delegateStmt_square (del recp t : Label) (f : FinKernelState) :
    ((finInterp (.guard (delegateGuardB del t)) f).bind
      (fun f' => some (finSetCaps (fun k => recDelegateCaps k.caps del recp t) {recp} f'))).map denote
      = interp (delegateStmt del recp t) (denote f) := by
  unfold delegateStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCaps (fun k => recDelegateCaps k.caps del recp t) {recp} g
      (recDelegateCaps_finiteDiff del recp t g)) f

theorem attenuateStmt_square (actor : CellId) (idx : Nat) (keep : List Auth) (f : FinKernelState) :
    ((finInterp (.checkSubset (grantedRightsSet actor idx keep) (heldRightsSet actor idx)) f).bind
      (fun f' => some (finSetCaps (fun k => attenuateSlotF k.caps actor idx keep) {actor} f'))).map denote
      = interp (attenuateStmt actor idx keep) (denote f) := by
  unfold attenuateStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCaps (fun k => attenuateSlotF k.caps actor idx keep) {actor} g
      (attenuateSlotF_finiteDiff actor idx keep g)) f

theorem revokeDelegationStmt_square (holder t : CellId) (f : FinKernelState) :
    (some (finSetCaps (fun k => removeEdgeCaps k.caps holder t) {holder} f)).map denote
      = interp (revokeDelegationStmt holder t) (denote f) := by
  unfold revokeDelegationStmt
  rw [Option.map_some]
  exact denote_finSetCaps (fun k => removeEdgeCaps k.caps holder t) {holder} f
    (removeEdgeCaps_finiteDiff holder t f)

theorem delegateAttenStmt_square (del recp t : Label) (keep : List Auth) (f : FinKernelState) :
    ((finInterp (.guard (delAttenGuardB del t)) f).bind
      (fun f' =>
        (finInterp (.checkSubset (grantedDelRightsSet del t keep) (heldDelRightsSet del t)) f').bind
          (fun f'' => some (finSetCaps
            (fun k => grant k.caps recp (attenuate keep (heldCapTo k.caps del t))) {recp} f'')))).map denote
      = interp (delegateAttenStmt del recp t keep) (denote f) := by
  unfold delegateAttenStmt
  exact denote_seq_compose
    (fun g => denote_finInterp (.guard (delAttenGuardB del t)) trivial g)
    (fun f' => pureThenWriter_square
      (p := .checkSubset (grantedDelRightsSet del t keep) (heldDelRightsSet del t))
      (fun g => denote_finSetCaps
        (fun k => grant k.caps recp (attenuate keep (heldCapTo k.caps del t))) {recp} g
        (grant_finiteDiff recp (attenuate keep (heldCapTo (denote g).caps del t)) g)) f')
    f

/-! ### §3c — the per-asset ledger (`setBal`) programs. -/

theorem balanceAStmt_square (turn : Turn) (a : AssetId) (f : FinKernelState) :
    ((finInterp (.guard (balanceAGuard turn a)) f).bind
      (fun f' => some (finSetBal (fun k => recTransferBal k.bal turn.src turn.dst a turn.amt)
        {toLex (turn.src, a), toLex (turn.dst, a)} f'))).map denote
      = interp (balanceAStmt turn a) (denote f) := by
  unfold balanceAStmt
  exact pureThenWriter_square
    (fun g => denote_finSetBal (fun k => recTransferBal k.bal turn.src turn.dst a turn.amt)
      {toLex (turn.src, a), toLex (turn.dst, a)} g
      (recTransferBal_finiteDiff turn.src turn.dst a turn.amt g)) f

theorem bridgeMintStmt_square (actor cell : CellId) (a : AssetId) (value : ℤ) (f : FinKernelState) :
    ((finInterp (.guard (bridgeMintGuard actor cell a value)) f).bind
      (fun f' => some (finSetBal (fun k => recTransferBal k.bal a cell a value)
        {toLex (a, a), toLex (cell, a)} f'))).map denote
      = interp (bridgeMintStmt actor cell a value) (denote f) := by
  unfold bridgeMintStmt
  exact pureThenWriter_square
    (fun g => denote_finSetBal (fun k => recTransferBal k.bal a cell a value)
      {toLex (a, a), toLex (cell, a)} g (recTransferBal_finiteDiff a cell a value g)) f

/-! ### §3d — the per-cell lifecycle (`setLifecycle`) programs. -/

theorem cellSealStmt_square (actor cell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (cellSealGuard actor cell)) f).bind
      (fun f' => some (finSetLifecycle (fun k => (setLifecycle k cell lcSealed).lifecycle)
        {cell} f'))).map denote
      = interp (cellSealStmt actor cell) (denote f) := by
  unfold cellSealStmt
  exact pureThenWriter_square
    (fun g => denote_finSetLifecycle (fun k => (setLifecycle k cell lcSealed).lifecycle) {cell} g
      (setLifecycleField_fd cell lcSealed g)) f

theorem cellUnsealStmt_square (actor cell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (cellUnsealGuard actor cell)) f).bind
      (fun f' => some (finSetLifecycle (fun k => (setLifecycle k cell lcLive).lifecycle)
        {cell} f'))).map denote
      = interp (cellUnsealStmt actor cell) (denote f) := by
  unfold cellUnsealStmt
  exact pureThenWriter_square
    (fun g => denote_finSetLifecycle (fun k => (setLifecycle k cell lcLive).lifecycle) {cell} g
      (setLifecycleField_fd cell lcLive g)) f

/-! ### §3e — the per-cell delegation-snapshot (`setDelegations`) program. -/

theorem refreshDelegationStmt_square (actor child : CellId) (f : FinKernelState) :
    ((finInterp (.guard (refreshDelegationGuard actor child)) f).bind
      (fun f' => some (finSetDelegations (fun k => refreshDelegationsMap k child) {child} f'))).map denote
      = interp (refreshDelegationStmt actor child) (denote f) := by
  unfold refreshDelegationStmt
  exact pureThenWriter_square
    (fun g => denote_finSetDelegations (fun k => refreshDelegationsMap k child) {child} g
      (refreshDelegationsMap_finiteDiff child g)) f

/-! ### §3f — the `setCell` programs (non-default side condition discharged by §1). -/

theorem transferStmt_square (turn : Turn) (f : FinKernelState) :
    ((finInterp (.guard (transferGuard turn)) f).bind
      (fun f' => some (finSetCell {turn.src, turn.dst}
        (fun k c => recTransfer k.cell turn.src turn.dst turn.amt c) f' (transfer_leaf_nd turn f')))).map denote
      = interp (transferStmt turn) (denote f) := by
  unfold transferStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {turn.src, turn.dst}
      (fun k c => recTransfer k.cell turn.src turn.dst turn.amt c) g (transfer_leaf_nd turn g)) f

theorem mintStmt_square (actor cell : CellId) (amt : Int) (f : FinKernelState) :
    ((finInterp (.guard (mintGuard actor cell amt)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setBalance (k.cell c) (balOf (k.cell c) + amt)) f'
        (fun c _ => setBalance_ne_nil _ _)))).map denote
      = interp (mintStmt actor cell amt) (denote f) := by
  unfold mintStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setBalance (k.cell c) (balOf (k.cell c) + amt)) g (fun c _ => setBalance_ne_nil _ _)) f

theorem burnStmt_square (actor cell : CellId) (amt : Int) (f : FinKernelState) :
    ((finInterp (.guard (burnGuard actor cell amt)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setBalance (k.cell c) (balOf (k.cell c) + (-amt))) f'
        (fun c _ => setBalance_ne_nil _ _)))).map denote
      = interp (burnStmt actor cell amt) (denote f) := by
  unfold burnStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setBalance (k.cell c) (balOf (k.cell c) + (-amt))) g
      (fun c _ => setBalance_ne_nil _ _)) f

theorem setPermissionsStmt_square (actor cell : CellId) (p : Int) (f : FinKernelState) :
    ((finInterp (.guard (setPermsGuardB actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setField permsField (k.cell c) (.int p)) f'
        (fun c _ => setField_ne_nil _ _ _)))).map denote
      = interp (setPermissionsStmt actor cell p) (denote f) := by
  unfold setPermissionsStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setField permsField (k.cell c) (.int p)) g (fun c _ => setField_ne_nil _ _ _)) f

theorem setFieldStmt_square (actor cell : CellId) (fld : FieldName) (v : Int) (f : FinKernelState) :
    ((finInterp (.guard (setFieldGuard actor cell fld v)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k _ => setField fld (k.cell cell) (.int v)) f'
        (fun c _ => setField_ne_nil _ _ _)))).map denote
      = interp (setFieldStmt actor cell fld v) (denote f) := by
  unfold setFieldStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k _ => setField fld (k.cell cell) (.int v)) g (fun c _ => setField_ne_nil _ _ _)) f

theorem receiptArchiveStmt_square (actor cell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (receiptArchiveGuard actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setField lifecycleField (k.cell c) (.int 1)) f'
        (fun c _ => setField_ne_nil _ _ _)))).map denote
      = interp (receiptArchiveStmt actor cell) (denote f) := by
  unfold receiptArchiveStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setField lifecycleField (k.cell c) (.int 1)) g (fun c _ => setField_ne_nil _ _ _)) f

theorem refusalStmt_square (actor cell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (refusalGuard actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setField refusalField (k.cell c) (.int 1)) f'
        (fun c _ => setField_ne_nil _ _ _)))).map denote
      = interp (refusalStmt actor cell) (denote f) := by
  unfold refusalStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setField refusalField (k.cell c) (.int 1)) g (fun c _ => setField_ne_nil _ _ _)) f

theorem setVerificationKeyStmt_square (actor cell : CellId) (vk : Int) (f : FinKernelState) :
    ((finInterp (.guard (setVerificationKeyGuard actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => setField vkField (k.cell c) (.int vk)) f'
        (fun c _ => setField_ne_nil _ _ _)))).map denote
      = interp (setVerificationKeyStmt actor cell vk) (denote f) := by
  unfold setVerificationKeyStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => setField vkField (k.cell c) (.int vk)) g (fun c _ => setField_ne_nil _ _ _)) f

theorem incrementNonceStmt_square (actor cell : CellId) (n : Int) (f : FinKernelState) :
    ((finInterp (.guard (incrementNonceGuardB actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k c => incNonceCellMap k cell n c) f' (incNonce_leaf_nd cell n f')))).map denote
      = interp (incrementNonceStmt actor cell n) (denote f) := by
  unfold incrementNonceStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k c => incNonceCellMap k cell n c) g (incNonce_leaf_nd cell n g)) f

theorem makeSovereignStmt_square (actor cell : CellId) (f : FinKernelState) :
    ((finInterp (.guard (makeSovereignGuard actor cell)) f).bind
      (fun f' => some (finSetCell {cell}
        (fun k _c => Value.record [(commitmentField, Value.dig (stateCommitment (k.cell cell))),
                       (TurnExecutorFull.nonceField, Value.int (TurnExecutorFull.sovereignNonce (k.cell cell)))])
        f' (fun c _ => by simp only [ne_eq, Value.record.injEq]; exact List.cons_ne_nil _ _)))).map denote
      = interp (makeSovereignStmt actor cell) (denote f) := by
  unfold makeSovereignStmt
  exact pureThenWriter_square
    (fun g => denote_finSetCell {cell}
      (fun k _c => Value.record [(commitmentField, Value.dig (stateCommitment (k.cell cell))),
                     (TurnExecutorFull.nonceField, Value.int (TurnExecutorFull.sovereignNonce (k.cell cell)))])
      g (fun c _ => by simp only [ne_eq, Value.record.injEq]; exact List.cons_ne_nil _ _)) f

/-! ### §3g — cellDestroy: a guard then TWO writers (`setLifecycle` ⨾ `setDeathCert`). -/

theorem cellDestroyStmt_square (actor cell : CellId) (certHash : Nat) (f : FinKernelState) :
    ((finInterp (.guard (cellDestroyGuard actor cell)) f).bind
      (fun f' =>
        (some (finSetLifecycle (fun k c => if c = cell then lcDestroyed else k.lifecycle c) {cell} f')).bind
          (fun f'' => some (finSetDeathCert
            (fun k c => if c = cell then certHash else k.deathCert c) {cell} f'')))).map denote
      = interp (cellDestroyStmt actor cell certHash) (denote f) := by
  unfold cellDestroyStmt
  exact denote_seq_compose
    (fun g => denote_finInterp (.guard (cellDestroyGuard actor cell)) trivial g)
    (fun f' => denote_seq_compose
      (writerLeaf (fun g => denote_finSetLifecycle
        (fun k c => if c = cell then lcDestroyed else k.lifecycle c) {cell} g (cellDestroyLifecycle_fd cell g)))
      (writerLeaf (fun g => denote_finSetDeathCert
        (fun k c => if c = cell then certHash else k.deathCert c) {cell} g
        (cellDestroyDeathCert_fd cell certHash g)))
      f')
    f

/-! ## §4 — TEETH (`#guard` + theorems, both polarities). -/

section Teeth

-- A `Pure` program commits, and the finite writer of a list side-table lands the exact list:
#guard (finInterp (pipelinedSendStmt 0) finInit).isSome
#guard ((finInterp (noteCreateStmt 7) finInit).map (fun f => f.commitments)) == some [7]

/-- **POSITIVE tooth — the deployed cellSeal lifecycle write fires concretely.** The finite step's
denotation (obtained via the §3d square, not by evaluating the noncomputable `setOver`) sets cell `0`'s
lifecycle to `lcSealed` (Live→Sealed), matching `interp`. -/
theorem cellSealStmt_fires :
    (denote (finSetLifecycle (fun k => (setLifecycle k 0 lcSealed).lifecycle) {0} finInit)).lifecycle 0
      = lcSealed := by
  have hsq := denote_finSetLifecycle (fun k => (setLifecycle k 0 lcSealed).lifecycle) {0} finInit
    (setLifecycleField_fd 0 lcSealed finInit)
  have hd := Option.some.inj (by simpa only [interp] using hsq)
  rw [hd]
  show (setLifecycle (denote finInit) 0 lcSealed).lifecycle 0 = lcSealed
  simp [setLifecycle]

/-- **NEGATIVE tooth — the `FiniteDiff` side condition BITES.** The genuine cellSeal lifecycle write is
NOT finite-diff over the EMPTY touched set: the agreement-off-`∅` obligation is FALSE (it changes slot
`0` from Live `0` to Sealed `1`), so an under-approximated touched set cannot discharge the square. -/
theorem cellSeal_notFiniteDiff_over_empty :
    ¬ (∀ c, c ∉ (∅ : Finset CellId) →
        (setLifecycle (denote finInit) 0 lcSealed).lifecycle c = (denote finInit).lifecycle c) := by
  intro hall
  have h0 := hall 0 (by simp)
  rw [show (setLifecycle (denote finInit) 0 lcSealed).lifecycle 0 = lcSealed from by
        simp [setLifecycle]] at h0
  simp only [denote, finInit, CanonMap.get_empty] at h0
  exact absurd h0 (by decide)

end Teeth

end Dregg2.Circuit.FinProgramSquares
