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
open Dregg2.Exec.FullForest (FullForestA FullChildA capTarget targetOf lowerForestA lowerChildrenA)
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
  -- W1: mint/burn are issuer-moves — the issuer WELL (`a`, the asset's own cell id) is written
  -- alongside the recipient/holder.
  | .mintA _ cell a _    => [a, cell]
  | .burnA _ cell a _    => [cell, a]
  | .setFieldA _ cell _ _ => [cell]
  | .emitEventA _ _ _ _  => []
  | .incrementNonceA _ cell _ => [cell]
  | .setPermissionsA _ cell _ => [cell]
  | .setVKA _ cell _     => [cell]
  | .setProgramA _ cell _ => [cell]
  | .introduceA _ rec _  => [rec]
  | .delegateAttenA _ rec _ _ => [rec]
  | .attenuateA actor _ _ => [actor]
  | .revokeDelegationA holder _ => [holder]
  | .exerciseA _ target inner =>
      addAll (inner.flatMap actionWriteSet) [target]
  | .createCellA _ newCell => [newCell]
  | .createCellFromFactoryA _ newCell _ => [newCell]
  | .spawnA _ child _     => [child]
  | .bridgeMintA _ cell a _ => [a, cell]   -- W1: the bridge well is written too
  | .noteSpendA _ actor _ => [actor]
  | .noteCreateA _ actor  => [actor]
  | .makeSovereignA _ cell => [cell]
  | .refusalA _ cell      => [cell]
  | .receiptArchiveA _ cell => [cell]
  | .cellSealA _ cell      => [cell]
  | .cellUnsealA _ cell    => [cell]
  | .pipelinedSendA actor => [actor]
  | .cellDestroyA _ cell _ => [cell]
  | .refreshDelegationA actor child => [actor, child]
  -- §MA-heap: the heap write mutates the `target` cell (its heap leaves + `heap_root` register).
  | .heapWriteA _ target _ _ _ => [target]

/-! The write-set the executor ACTUALLY touches is the union of `actionWriteSet` over the EXECUTED
action list — which is `lowerForestA root`, NOT the node-action tree. `lowerForestA` interleaves, BEFORE
each child subtree, the EXECUTED `delegateAttenA delegator holder t keep` the forest executor inserts
(`execFullChildrenA`'s `recCDelegateAtten` handoff). That handoff MUTATES the `holder`'s cap slot
(`actionWriteSet (.delegateAttenA _ rec _ _) = [rec]`). A write-set built from the node-action tree
alone would OMIT these implicit per-child delegation writes, so a FROZEN `holder` could be cap-mutated
by the implicit edge WITHOUT appearing in the freeze/conflict write-set — the very hole the freeze gate
(`admissible` leg 6) exists to close. We therefore extract the write-set from `lowerForestA`, which
contains exactly the actions (nodes AND inserted handoffs) the executor runs. -/

/-- Write-set of the EXECUTED action list of a `FullForestA` tree: the `actionWriteSet`-union over the
pre-order lowering `lowerForestA` — so the per-child implicit `delegateAttenA` (the `holder` cap-slot
write the forest executor inserts) IS included, closing the frozen-holder freeze-bypass. -/
def forestWriteSet (root : FullForestA) : List CellId :=
  (lowerForestA root).foldl (fun acc a => addAll (actionWriteSet a) acc) []

/-- The full turn write-set: agent (always written by the prologue) ∪ the EXECUTED-action cells
(forest nodes AND the inserted per-child delegation handoffs). -/
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

/-! ## §4 — the IMPLICIT-DELEGATION-WRITE teeth (frozen-holder freeze-bypass closed).

The forest executor inserts, per child edge, an EXECUTED `delegateAttenA delegator holder t keep` that
MUTATES `holder`'s cap slot (`recCDelegateAtten` ⇒ `actionWriteSet … = [holder]`). The write-set must
include these implicit writes, or a FROZEN `holder` could be cap-mutated WITHOUT the freeze gate
(`admissible` leg 6) catching it. `forestWriteSet` is now built from `lowerForestA`, which contains the
inserted handoffs — so the holder IS in the write-set. The witness below has a `holder` that is NOT any
node-action target, so the OLD node-only write-set would have OMITTED it. -/

/-- A tree whose single child edge delegates to `holder := 4` — a cell that NO node action touches (the
root `mintA 9 0 1 5` writes `[0]` and well `1`; the child `burnA 9 0 1 5` writes `[0]` and well `1`).
So `4` appears in the write-set ONLY via the inserted `delegateAttenA … 4 …` handoff. -/
def implicitDelegWitness : FullForestA :=
  ⟨ .mintA 9 0 1 5
  , [ { holder := 4, keep := [], parentCap := .node 0
      , sub := ⟨ .burnA 9 0 1 5, [] ⟩ } ] ⟩

-- The implicit-delegation holder `4` IS now in the forest write-set (it was OMITTED by the old
-- node-only `forestWriteSetChildren` — the freeze-bypass):
#guard ((forestWriteSet implicitDelegWitness).contains 4)  --  true (the inserted delegateAtten write)
-- ...and therefore in the full turn write-set the admission header carries:
#guard ((turnWriteSet 7 implicitDelegWitness).contains 4)  --  true

/-- A frozen-holder context: the delegation HOLDER `4` is frozen, but agent `7` and every node-target
cell is NOT. Pre-fix this admitted (holder `4` was invisible to the freeze gate); post-fix it REJECTS. -/
def frozenHolderCtx : AdmCtx := { now := 0, frozen := [4], storedHead := none, budget := 1000000000 }

-- MUTATION-CONFIRM: a frozen HOLDER now makes the turn INADMISSIBLE (the implicit cap-mutation is
-- caught). The write-set's `4` trips `admissible` leg 6 (`writeSet.all (!isFrozen)` = false):
#guard ((frozenHolderCtx.frozen.contains 4))  --  true (holder 4 is frozen)
#guard ((turnHdrOf 7 implicitDelegWitness 0 0 0 0).writeSet.all
        (fun c => !isFrozen frozenHolderCtx c)) == false  --  false (frozen holder ⇒ leg-6 REJECT)

end Dregg2.Exec.AdmissionWire