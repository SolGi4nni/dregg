/-
# Dregg2.Exec.AdmissionWire — write-set extraction + turn-header builders for the FFI seam.

Mirrors dregg1 `turn/src/conflict.rs::extract_access_sets`: the agent cell is always in the
write-set (fee + nonce prologue), and every forest node contributes the cells its `FullActionA`
may mutate. Conservative over-approximation — safe for the freeze gate (`admissible` leg 6).

Used by `Exec/FFI.lean` to build `TurnHdr` and drive `TurnAdmission.runGatedForestTurn`.
-/
import Dregg2.Exec.TurnAdmission
import Dregg2.Exec.FullForest
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Exec.Receipt

namespace Dregg2.Exec.AdmissionWire

open Dregg2.Exec
open Dregg2.Exec.Admission
open Dregg2.Exec.FullForest (FullForestA FullChildA)
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Exec.Receipts (genesisSentinel)

/-! ## §1 — list helpers. -/

/-- Insert `c` if absent (preserves order; duplicates dropped). -/
def addUnique (c : CellId) (xs : List CellId) : List CellId :=
  if xs.contains c then xs else c :: xs

/-- Fold `addUnique` over a cell list into accumulator `xs`. -/
def addAll (cs : List CellId) (xs : List CellId) : List CellId :=
  cs.foldl (fun acc c => addUnique c acc) xs

/-! ## §2 — per-action write-set (conservative, Rust-faithful). -/

/-- Cells a single `FullActionA` may write. Mirrors `conflict.rs::extract_tree_access` effect
arms; unknown / read-only arms contribute nothing beyond what the caller adds. -/
def actionWriteSet : FullActionA → List CellId
  | .balanceA t _       => [t.src, t.dst]
  | .delegate _ rec _   => [rec]
  | .revoke holder _     => [holder]
  | .mintA _ cell _ _    => [cell]
  | .burnA _ cell _ _    => [cell]
  | .setFieldA _ cell _ _ => [cell]
  | .emitEventA _ _ _ _  => []
  | .incrementNonceA _ cell _ => [cell]
  | .setPermissionsA _ cell _ => [cell]
  | .setVKA _ cell _     => [cell]
  | .introduceA _ rec _  => [rec]
  | .delegateAttenA _ rec _ _ => [rec]
  | .attenuateA actor _ _ => [actor]
  | .dropRefA holder _    => [holder]
  | .revokeDelegationA holder _ => [holder]
  | .validateHandoffA _ rec _ => [rec]
  | .exerciseA _ target inner =>
      addAll (inner.flatMap actionWriteSet) [target]
  | .createCellA _ newCell => [newCell]
  | .createCellFromFactoryA _ newCell _ => [newCell]
  | .spawnA _ child _     => [child]
  | .bridgeMintA _ cell _ _ => [cell]
  | .createEscrowA _ _ creator _ _ _ => [creator]
  | .releaseEscrowA _ actor => [actor]
  | .refundEscrowA _ actor => [actor]
  | .createObligationA _ _ obligor _ _ _ => [obligor]
  | .fulfillObligationA _ actor => [actor]
  | .slashObligationA _ actor => [actor]
  | .noteSpendA _ actor   => [actor]
  | .noteCreateA _ actor  => [actor]
  | .createCommittedEscrowA _ _ creator _ _ _ _ => [creator]
  | .releaseCommittedEscrowA _ actor => [actor]
  | .refundCommittedEscrowA _ actor => [actor]
  | .bridgeLockA _ _ originator _ _ _ => [originator]
  | .bridgeFinalizeA _ actor _ _ => [actor]
  | .bridgeCancelA _ actor => [actor]
  | .sealA _ actor _       => [actor]
  | .unsealA _ actor _     => [actor]
  | .createSealPairA _ actor sealer unsealer => [actor, sealer, unsealer]
  | .makeSovereignA _ cell => [cell]
  | .refusalA _ cell      => [cell]
  | .receiptArchiveA _ cell => [cell]
  | .queueAllocateA _ _ cell _ => [cell]
  | .queueEnqueueA _ _ _ cell _ _ _ => [cell]
  | .queueDequeueA _ _ cell _ _ => [cell]
  | .queueResizeA _ _ _ cell => [cell]
  | .exportSturdyRefA _ _ exporter _ _ => [exporter]
  | .enlivenRefA _ _ exporter _ => [exporter]
  | .swissHandoffA _ _ _ exporter => [exporter]
  | .swissDropA _ _ exporter => [exporter]
  | .cellSealA _ cell      => [cell]
  | .cellUnsealA _ cell    => [cell]
  | .queueAtomicTxA actor ops =>
      addAll (ops.flatMap fun op =>
        match op with
        | .enqueue _ _ _ c _ _ _ => [c]
        | .dequeue _ _ c _ _ => [c]) [actor]
  | .queuePipelineStepA _ owner sinkCells _ =>
      addUnique owner (sinkCells.foldl (fun acc c => addUnique c acc) [])
  | .pipelinedSendA actor => [actor]
  | .cellDestroyA _ cell _ => [cell]
  | .refreshDelegationA actor child => [actor, child]

mutual
/-- Write-set of a structural `FullForestA` tree (pre-order union). -/
def forestWriteSet : FullForestA → List CellId
  | ⟨a, kids⟩ => addAll (actionWriteSet a) (forestWriteSetChildren kids)

/-- Union write-sets of child edges. -/
def forestWriteSetChildren : List FullChildA → List CellId
  | [] => []
  | ⟨_, _, _, sub⟩ :: rest => addAll (forestWriteSet sub) (forestWriteSetChildren rest)
end

/-- The full turn write-set: agent (always written by the prologue) ∪ forest cells. -/
def turnWriteSet (agent : CellId) (root : FullForestA) : List CellId :=
  addUnique agent (forestWriteSet root)

/-! ## §3 — header / context builders for the FFI wire. -/

/-- Map a wire `prevHash` digest to the `TurnHdr.prevReceipt` option (`0` = genesis = `none`). -/
def prevReceiptOf (prevHash : Nat) : Option Nat :=
  if prevHash = genesisSentinel then none else some prevHash

/-- Build a `TurnHdr` from the turn envelope + structural forest (write-set extracted). -/
def turnHdrOf (agent : CellId) (root : FullForestA) (nonce : Nat) (fee : Int)
    (validUntil : Nat) (prevHash : Nat) : TurnHdr :=
  { agent := agent
  , nonce := Int.ofNat nonce
  , fee := fee
  , validUntil := some validUntil
  , prevReceipt := prevReceiptOf prevHash
  , writeSet := turnWriteSet agent root
  , forestNonEmpty := true }

/-- Build an `AdmCtx` from host-fed wire fields. -/
def admCtxOf (now : Nat) (frozen : List CellId) (storedHead : Option Nat) (budget : Nat) : AdmCtx :=
  { now := now, frozen := frozen, storedHead := storedHead, budget := budget }

end Dregg2.Exec.AdmissionWire