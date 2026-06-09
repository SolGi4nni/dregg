/-
# Dregg2.Circuit.Argus.Effects.QueueDequeue — the FIFO pop-front + deposit-REFUND effect `queueDequeue`
welded into the Argus IR, on the FULL-STATE `Surface2`-triple surface.

`Argus/Stmt.lean` laid the cornerstone (the executor IS the meaning of a `RecStmt` term) and validated
it on transfer/mint/burn (single-cell) + createEscrow (two-component side-table). `Argus/Effects/
BalanceA.lean` did the genuinely DIFFERENT thing: it welded against the v2 `Surface2` / `EffectCommit2`
descriptor whose soundness pins the **whole 17-field post-state** (`balanceA_full_sound ⇒
BalanceMovementSpec`), routing the executor side through the independent `execFullA_…_iff_spec`. This
module replicates THAT stronger surface for `queueDequeue`, in a disjoint file (it imports the Argus IR
+ the audited `queueDequeueA` triple instance read-only and owns only its own declarations; it edits no
other Argus file).

## What `queueDequeue` IS, and why it is the THREE-component side-table shape.

The unified action executor dispatches `.queueDequeueA id actor cell depId` to `queueDequeueChainA`
(`TurnExecutorFull:3878 / :2248`):

    queueDequeueChainA s id actor cell depId
      = if stateAuthB caps actor cell ∧ acceptsEffects cell ∧ dequeueBindB actor depId
           ∧ queueDequeueHeadB id actor depId then
          match queueDequeueRefundK s.kernel id actor depId with
          | some (k', _) => some { kernel := k',
              log := {actor, src:=cell, dst:=actor, amt:=dequeueRefundAmount s.kernel depId} :: s.log }
          | none         => none
        else none

and `queueDequeueRefundK` (`RecordKernel:2355`) composes the FIFO POP-FRONT (`queueDequeueK`,
owner-gated, fail-closed on absent/not-owner/EMPTY) with the deposit REFUND
(`settleEscrowRawAsset` — credit the dequeuer's `bal` by the parked `r.amount` at `r.asset` AND mark
the deposit record resolved in `escrows`). So a committed dequeue touches THREE `RecordKernelState`
components: `queues` (pop-front), `bal` (refund credit), `escrows` (deposit resolved); it advances the
chained `log`; the other 14 kernel fields are the FRAME. This is the shape the §A component-write
primitives `setQueues`/`setBal`/`setEscrows` (`Stmt.lean`) were built for — no new IR primitive needed.

## The TWO surfaces, and why this module takes the FULL-STATE one.

  * The EffectVM descriptor `EffectVmEmitQueueDequeue.queueDequeueVmDescriptor` is a SINGLE-ROW AIR; its
    soundness pins ONE cell's refund-credit projection + the in-row queue-root advance. That is the
    per-cell surface (transfer's beachhead).
  * `queueDequeue`'s GENUINE full-state crown jewel lives in the v2 `EffectCommit3`-triple universe
    (`Inst/queueDequeueA.lean`): `queueDequeueE` (the `EffectSpec2Triple` whose three active components
    are the WHOLE `queues` list digest, the WHOLE `bal` function digest, and the WHOLE `escrows` list
    digest) and `queueDequeueA_full_sound : satisfiedE2Triple … (queueDequeueE …) … ⟹ QueueDequeueSpec`
    — a FULL 17-field declarative post-state soundness, keyed on the CHAINED executor `execFullA` via
    the independent `execFullA_queueDequeueA_iff_spec` (`Spec/queuefifocore.lean`).

This module welds against THAT full-state descriptor (strictly stronger than the per-cell EffectVM row),
exactly as `BalanceA.lean` welds against `balanceA_full_sound` instead of the EffectVM transfer row.

So this module is HONEST in both directions:

  (1) **Cornerstone (the standalone executor-refinement):** `interp_queueDequeueStmt_eq_kernelStep` —
      the kernel projection of `queueDequeueChainA` (gate, then the THREE component writes reproducing
      `queueDequeueRefundK`'s post-kernel) IS the Argus term, using `setQueues`/`setBal`/`setEscrows`.

  (2) **Compile weld against the full-state triple descriptor:** lift the kernel cornerstone to the
      chained `execFullA`, then weld to `queueDequeueA_full_sound` / `execFullA_queueDequeueA_iff_spec`.
      The conclusion is the FULL `QueueDequeueSpec` agreement (all 17 kernel fields + the receipt log) —
      a satisfying witness of `queueDequeue`'s own full-state circuit agrees with the WHOLE post-state
      the IR term's executor produces.

## HONEST DIVERGENCE carried explicitly (NOT papered).

There is ONE genuine kernel-vs-runtime divergence, carried as an explicit conjunct of the weld's
statement (the `divergence` field of the structured result):

  * **NONCE-TICK (runtime row vs full-state spec).** The EffectVM RUNTIME row TICKS the per-cell nonce
    (the global non-NoOp invariant, `EffectVmEmitQueueDequeue` §RECONCILIATION); the full-state spec
    `QueueDequeueSpec` (and the executor `queueDequeueRefundK`) FREEZE the per-cell `cell` record (the
    pop edits only `queues`/`bal`/`escrows`). The full-state weld this module proves is over the
    `Surface2`-triple descriptor (`queueDequeueE`), whose `cell` component is part of the FROZEN
    `restFrame` — so on THIS surface there is no per-cell nonce mutation at all (the spec freezes
    `cell`). The runtime row's tick is reconciled at the turn level exactly as for transfer/burn
    (`Argus/Nonce`); it is NOT part of the full-state triple's statement. We record this so the reader
    knows the per-row runtime descriptor and the full-state triple descriptor differ on the cell nonce,
    and that this module welds the latter (where `cell` is frozen).

A SECOND honest boundary (a collapsed surface, not a divergence): the full-state spec pins the post
`queues`/`bal`/`escrows` as the EXACT `queueDequeueRefundK` outputs (via the canonical post-functions),
and the triple's three component digests bind those whole structures under the injective list/function
digest portals. The EffectVM row, by contrast, carries the queue side-table as a single advanced ROOT
(`fields[4]`), not the list. This module welds the triple (the whole-structure digest), so the
list-vs-digest boundary the EffectVM row has does NOT arise here — the triple binds the real post lists.

## Honesty

`#assert_axioms` on every headline theorem ⊆ {propext, Classical.choice, Quot.sound}; the
whole-list/whole-function digest CR assumptions enter ONLY inside the reused `queueDequeueA_full_sound`
(its `Function.Injective D` / `listLeafInjective` / `compressNInjective` / `logHashInjective`
hypotheses), not in the welded conclusion's statement. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Inst.queueDequeueA

namespace Dregg2.Circuit.Argus.Effects.QueueDequeue

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Exec.EffectsState (stateAuthB)
-- The full-state triple descriptor + its soundness, and the independent executor⟺spec corner.
open Dregg2.Circuit.StateCommit (logHashInjective compressNInjective)
open Dregg2.Circuit.EffectCommit2 (Surface2)
open Dregg2.Circuit.ListCommit (listLeafInjective)
open Dregg2.Circuit.EffectCommit3 (satisfiedE2Triple encodeE2Triple)
open Dregg2.Circuit.Spec.QueueFifoCore
  (QueueDequeueSpec dequeueReceipt execFullA_queueDequeueA_iff_spec)
open Dregg2.Circuit.Inst.QueueDequeueA
  (DequeueArgs RestIffNoQueuesBalEscrows queueDequeueE queueDequeueA_full_sound)

/-! ## §1 — the kernel step of `queueDequeueChainA`, and its capture as an Argus IR term.

`queueDequeueChainA` is `if <4-conjunct chain gate> then (map the kernel of `queueDequeueRefundK`) else
none`, prepending the refund receipt onto the log. The ARGUS `interp` is a `RecordKernelState → Option
RecordKernelState` transformer (no log), so the cornerstone is over the KERNEL PROJECTION of
`queueDequeueChainA`; §3 lifts that kernel cornerstone to the chained `execFullA` (carrying the log
prepend), exactly as `BalanceA.lean §3` lifts its raw-kernel cornerstone to `execFullA`. -/

/-- The 4-conjunct chained dequeue admissibility gate as a `Bool` over the kernel — exactly the `if`
condition of `queueDequeueChainA`: authority over the queue cell, lifecycle-liveness of the cell, the
P0-1 deposit binding (`dequeueBindB`: the named deposit is destined to the dequeuer), AND the
P0-1-full pre-pop head binding (`queueDequeueHeadB`: the named deposit binds to the peeked FIFO head
`(queueId, msgHash, recipient)` BEFORE any pop runs, so a failed binding cannot consume the buffer). -/
def dequeueChainGateB (k : RecordKernelState) (id : Nat) (actor cell : CellId) (depId : Nat) : Bool :=
  stateAuthB k.caps actor cell
    && acceptsEffects k cell
    && dequeueBindB k actor depId
    && queueDequeueHeadB k id actor depId

/-! ### The THREE component-write leaves, as DIRECT projections of the PRE-state fields.

A subtlety the single-cell / two-component effects never hit: `queueDequeueRefundK` is NOT idempotent —
its first act is to POP the FIFO front (`queueDequeueK`), and its escrow lookup reads the (unresolved)
`escrows`. So a leaf that RE-RAN `queueDequeueRefundK` on a PARTIALLY-mutated intermediate state (the
result of a prior `setQueues`/`setEscrows` write) would pop AGAIN or miss the now-resolved record — it
would NOT reproduce the kernel step. The faithful capture therefore reads each post-field DIRECTLY off
the PRE-state fields (no re-pop), and the body ORDERS the three writes (`setBal` → `setEscrows` →
`setQueues`) so that each leaf reads only PRE-fields no prior write has clobbered:

  * `setBal` reads `bal` + `escrows` (for the refunded record) — runs FIRST (both untouched);
  * `setEscrows` reads `escrows` (`markResolved`) — runs SECOND (`setBal` wrote only `bal`);
  * `setQueues` reads `queues` (the pop) — runs LAST (`queues` is never written by the other two).

`§2`'s `queueDequeueRefundK_fields` proves these three direct leaves equal the kernel step's `k'.bal`/
`k'.escrows`/`k'.queues`, so the ordered body reproduces `k'` on the nose. -/

/-- The post-`queues` of a committed dequeue, read DIRECTLY off `k.queues`: find queue `id`, pop its
FIFO front, and `replaceQueue` it (buffer := the tail). Total: the `none`/empty fallbacks are the
unchanged table (the gate then rejects, so a committed dequeue always hits the pop branch). The
`setQueues` leaf — reads ONLY `k.queues`. -/
def dequeuePoppedQueues (k : RecordKernelState) (id : Nat) : List QueueRecord :=
  match findQueue k.queues id with
  | none   => k.queues
  | some q =>
      match qbufDequeue q.buffer with
      | none           => k.queues
      | some (_, rest) => replaceQueue k.queues id { q with buffer := rest }

/-- The post-`bal` of a committed dequeue, read DIRECTLY off `k.bal` + `k.escrows`: look up the
unresolved deposit record `depId` and CREDIT the dequeuer `actor` at the record's `asset` by its
`amount` (the refund). Total: the `none` fallback is the unchanged ledger. The `setBal` leaf — reads
ONLY `k.bal` and `k.escrows`. -/
def dequeueRefundBal (k : RecordKernelState) (actor : CellId) (depId : Nat) :
    CellId → AssetId → Int :=
  match findUnresolvedDeposit k depId with
  | some r => recBalCreditCell k.bal actor r.asset r.amount
  | none   => k.bal

/-- **`queueDequeueK_shape`** — a committed FIFO pop produces EXACTLY `{ k with queues :=
dequeuePoppedQueues k id }` (only `queues` changes, to the popped table) and returns the popped HEAD as
`mh`. The single structural fact about the pop the whole cornerstone rests on (`queueDequeueK` is the
only sub-op that touches `queues`). -/
theorem queueDequeueK_shape {k k₁ : RecordKernelState} {id : Nat} {actor : CellId} {mh : Nat}
    (h : queueDequeueK k id actor = some (k₁, mh)) :
    k₁ = { k with queues := dequeuePoppedQueues k id } := by
  unfold queueDequeueK at h
  unfold dequeuePoppedQueues
  cases hf : findQueue k.queues id with
  | none => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h ⊢
      by_cases ho : actor = q.owner
      · simp only [if_pos ho] at h ⊢
        cases hd : qbufDequeue q.buffer with
        | none => simp only [hd] at h; exact absurd h (by simp)
        | some hr =>
            obtain ⟨m, rest⟩ := hr
            simp only [hd] at h ⊢; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk₁, _⟩ := h; rw [← hk₁]
      · simp only [if_neg ho] at h; exact absurd h (by simp)

/-- **`queueDequeueRefundK_fields`** — a committed dequeue's post-kernel `k'` has its THREE touched
components EQUAL to the DIRECT pre-state projections above (`dequeueRefundBal` for `bal`, `markResolved`
for `escrows`, `dequeuePoppedQueues` for `queues`). This is the load-bearing fact that the direct leaves
(read off pre-fields, never re-popping) reproduce the kernel step's outputs. Proved by unfolding
`queueDequeueRefundK` ONCE on a commit and using `queueDequeueK_shape` (the pop touches only `queues`, so
its `k₁.bal`/`k₁.escrows` are `k.bal`/`k.escrows` and `findUnresolvedDeposit k₁ = … k`), then observing
`settleEscrowRawAsset` writes exactly `recBalCreditCell k.bal actor r.asset r.amount` /
`markResolved k.escrows depId`. -/
theorem queueDequeueRefundK_fields {k k' : RecordKernelState} {id : Nat} {actor : CellId}
    {depId m : Nat} (h : queueDequeueRefundK k id actor depId = some (k', m)) :
    k'.bal = dequeueRefundBal k actor depId
    ∧ k'.escrows = markResolved k.escrows depId
    ∧ k'.queues = dequeuePoppedQueues k id := by
  unfold queueDequeueRefundK at h
  cases hqd : queueDequeueK k id actor with
  | none => simp only [hqd] at h; exact absurd h (by simp)
  | some kr =>
      obtain ⟨k₁, mh⟩ := kr
      simp only [hqd] at h
      -- the pop's shape: `k₁ = { k with queues := dequeuePoppedQueues k id }`, so `k₁.bal = k.bal`,
      -- `k₁.escrows = k.escrows`, `k₁.queues = dequeuePoppedQueues k id` (all by projection).
      have hshape := queueDequeueK_shape hqd
      have hbalEq : k₁.bal = k.bal := by rw [hshape]
      have hescEq : k₁.escrows = k.escrows := by rw [hshape]
      have hqEq : k₁.queues = dequeuePoppedQueues k id := by rw [hshape]
      -- the message-binding gate; `none`/`false` ⇒ reject.
      by_cases hbind : dequeueMsgBindB k₁ actor depId id mh = true
      · simp only [if_pos hbind] at h
        cases hfind : findUnresolvedDeposit k₁ depId with
        | none => simp only [hfind] at h; exact absurd h (by simp)
        | some r =>
            simp only [hfind] at h
            by_cases hacc : actor ∈ k₁.accounts
            · simp only [if_pos hacc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨hk', _⟩ := h; subst hk'
              have hfindEq : findUnresolvedDeposit k depId = some r := by
                unfold findUnresolvedDeposit at hfind ⊢; rw [← hescEq]; exact hfind
              refine ⟨?_, ?_, ?_⟩
              · -- bal: settle credits `actor` at `r.asset` by `r.amount` over `k₁.bal = k.bal`; the direct
                -- leaf reads the SAME record via `findUnresolvedDeposit k = some r`.
                show (settleEscrowRawAsset k₁ depId actor r.asset r.amount).bal
                  = dequeueRefundBal k actor depId
                unfold settleEscrowRawAsset dequeueRefundBal
                rw [hbalEq, hfindEq]
              · -- escrows: settle marks `depId` resolved over `k₁.escrows = k.escrows`.
                show (settleEscrowRawAsset k₁ depId actor r.asset r.amount).escrows
                  = markResolved k.escrows depId
                unfold settleEscrowRawAsset; rw [hescEq]
              · -- queues: settle touches only bal/escrows, so post-queues = `k₁.queues` = pop of `k`.
                show (settleEscrowRawAsset k₁ depId actor r.asset r.amount).queues
                  = dequeuePoppedQueues k id
                unfold settleEscrowRawAsset; exact hqEq
            · simp only [if_neg hacc] at h; exact absurd h (by simp)
      · simp only [Bool.not_eq_true] at hbind; simp only [hbind] at h; exact absurd h (by simp)

/-- **`queueDequeueRefundK_rebuild`** — a committed dequeue's post-kernel `k'` is REBUILT from the
original `k` by writing exactly the three touched components (`bal`/`escrows`/`queues`) to their DIRECT
pre-state projections; every OTHER field of `k'` equals `k`'s (the dequeue FRAMES the remaining 14
fields, via the audited `queueDequeueRefundK_preserves_frame`). This is what lets the ordered THREE
component writes of the IR body reproduce the kernel step's `k'` on the nose. -/
theorem queueDequeueRefundK_rebuild {k k' : RecordKernelState} {id : Nat} {actor : CellId}
    {depId m : Nat} (h : queueDequeueRefundK k id actor depId = some (k', m)) :
    { k with bal := dequeueRefundBal k actor depId,
             escrows := markResolved k.escrows depId,
             queues := dequeuePoppedQueues k id } = k' := by
  obtain ⟨hbal, hesc, hq⟩ := queueDequeueRefundK_fields h
  obtain ⟨hAcc, hCell, hCaps, hNul, hRev, hCom, hSw, hSC, hFac, hLif, hDC, hDel, hDgs, hSB⟩ :=
    Dregg2.Circuit.Inst.QueueDequeueA.queueDequeueRefundK_preserves_frame h
  -- all 17 fields agree: bal/escrows/queues are the direct projections (= `k'`'s by `queueDequeueRefundK
  -- _fields`), the other 14 are `k`'s = `k'`'s by the frame fact (used symmetrically).
  apply Dregg2.Circuit.Inst.QueueDequeueA.recordKernel_eq_of_fields
  · exact hAcc.symm
  · exact hCell.symm
  · exact hCaps.symm
  · exact hesc.symm          -- escrows := markResolved k.escrows depId = k'.escrows
  · exact hNul.symm
  · exact hRev.symm
  · exact hCom.symm
  · exact hbal.symm          -- bal := dequeueRefundBal … = k'.bal
  · exact hq.symm            -- queues := dequeuePoppedQueues k id = k'.queues
  · exact hSw.symm
  · exact hSC.symm
  · exact hFac.symm
  · exact hLif.symm
  · exact hDC.symm
  · exact hDel.symm
  · exact hDgs.symm
  · exact hSB.symm

/-- **The kernel step of `queueDequeueChainA`** — gate on the 4-conjunct chain gate, then the kernel of
`queueDequeueRefundK` (FIFO pop + refund). `none` when the gate rejects OR `queueDequeueRefundK`
rejects (e.g. the message-binding `dequeueMsgBindB` fails inside the refund). This is exactly the
`{kernel := ·}` field of `queueDequeueChainA` (§3 proves that). -/
def dequeueKernelStep (k : RecordKernelState) (id : Nat) (actor cell : CellId) (depId : Nat) :
    Option RecordKernelState :=
  if dequeueChainGateB k id actor cell depId then
    match queueDequeueRefundK k id actor depId with
    | some (k', _) => some k'
    | none         => none
  else none

/-- **The queueDequeue effect as an IR term: gate, then the THREE ORDERED component writes.** Unlike
transfer/mint/burn (one move), the body is `seq (setBal <refund>) (seq (setEscrows <resolve>) (setQueues
<pop>))`: CREDIT the dequeuer's per-asset ledger by the parked refund, mark the deposit record resolved,
then POP the FIFO front. The order is LOAD-BEARING (see §1): each direct leaf reads ONLY pre-fields no
prior write has clobbered (`setBal` reads `bal`+`escrows`; `setEscrows` reads `escrows`; `setQueues`
reads `queues`). The gate is the FULL `dequeueChainGateB ∧ refundK-commits`, captured as a `Bool` (so
when the gate admits, `queueDequeueRefundK` is `some` and the three leaves rebuild its `k'`). The three
component-write primitives `setBal`/`setEscrows`/`setQueues` (§A) are exactly the shapes a multi-component
side-table effect assembles — no new constructor needed. -/
def queueDequeueStmt (id : Nat) (actor cell : CellId) (depId : Nat) : RecStmt :=
  RecStmt.seq
    (RecStmt.guard (fun k => dequeueChainGateB k id actor cell depId
      && (queueDequeueRefundK k id actor depId).isSome))
    (RecStmt.seq
      (RecStmt.setBal (fun k => dequeueRefundBal k actor depId))
      (RecStmt.seq
        (RecStmt.setEscrows (fun k => markResolved k.escrows depId))
        (RecStmt.setQueues (fun k => dequeuePoppedQueues k id))))

/-! ## §2 — the cornerstone: `interp` of the queueDequeue term IS the kernel step `dequeueKernelStep`.

Two ingredients, as in `createEscrow`/`refundEscrow`: (a) the `Bool` gate decodes to the kernel step's
admission, and (b) the three-component body reproduces `queueDequeueRefundK`'s post-kernel. The
load-bearing side-table fact (the chained interleaving the single-cell effects never had): the
`setBal` and `setEscrows` leaves are read on the INTERMEDIATE states after the prior writes, but each
reads `queueDequeueRefundK k id actor depId` on the ORIGINAL `k` — and the prior `setQueues`/`setBal`
writes touch only `queues`/`bal`, so the look-ups still see the original `k`'s `queues`/`bal`/`escrows`
inside `queueDequeueRefundK`. We make that explicit by reducing the body against `k` directly. -/

/-- The ORDERED three-write body reduces to the explicit three-field record-update read off the ORIGINAL
`k`. The order makes this hold by definitional record-projection: `setEscrows`'s `markResolved`-leaf is
read on `{k with bal := …}` whose `.escrows` IS `k.escrows`; `setQueues`'s pop-leaf is read on
`{k with bal := …, escrows := …}` whose `.queues` IS `k.queues`. So the later leaves see the ORIGINAL
fields they depend on, and the body's post-state is the three direct projections of `k`. -/
theorem queueDequeueBody_eq (id : Nat) (actor : CellId) (depId : Nat) (k : RecordKernelState) :
    interp (RecStmt.seq
        (RecStmt.setBal (fun k => dequeueRefundBal k actor depId))
        (RecStmt.seq
          (RecStmt.setEscrows (fun k => markResolved k.escrows depId))
          (RecStmt.setQueues (fun k => dequeuePoppedQueues k id)))) k
      = some { k with bal := dequeueRefundBal k actor depId
                      escrows := markResolved k.escrows depId
                      queues := dequeuePoppedQueues k id } := by
  -- Each `set<C>` clause is `some { · with <C> := g · }`; chaining through `bind`, the `setEscrows`
  -- leaf reads `{k with bal:=…}.escrows = k.escrows` and the `setQueues` leaf reads
  -- `{k with bal:=…, escrows:=…}.queues = k.queues` — both definitional record projections, so the
  -- body's `interp` reduces to the three-field update on `k`.
  simp only [interp, Option.bind]
  rfl

/-- The gate `Bool` decodes to the kernel step's admission: `dequeueChainGateB` holds AND
`queueDequeueRefundK` commits. (Used to align the term's `guard` with `dequeueKernelStep`'s `if`/
`match`.) -/
theorem queueDequeueGate_iff (id : Nat) (actor cell : CellId) (depId : Nat) (k : RecordKernelState) :
    (dequeueChainGateB k id actor cell depId
        && (queueDequeueRefundK k id actor depId).isSome) = true ↔
      (dequeueChainGateB k id actor cell depId = true
        ∧ (queueDequeueRefundK k id actor depId).isSome = true) := by
  simp only [Bool.and_eq_true]

/-- **The cornerstone (three-component side-table).** `interp` of the queueDequeue term IS the kernel
step `dequeueKernelStep` — the same partial function, by construction, exactly as the transfer/mint/burn/
createEscrow cornerstones, now over a THREE-component side-table effect (`queues` pop + `bal` refund +
`escrows` resolve). The kernel projection of the chained `queueDequeueChainA`. -/
theorem interp_queueDequeueStmt_eq_kernelStep (id : Nat) (actor cell : CellId) (depId : Nat)
    (k : RecordKernelState) :
    interp (queueDequeueStmt id actor cell depId) k = dequeueKernelStep k id actor cell depId := by
  -- the term is `seq (guard g) body`; reduce ONLY the leading guard (NOT the body's `interp`, so the
  -- `queueDequeueBody_eq` rewrite below still applies). `interp (seq (guard g) body) k =
  -- (if g k then some k else none).bind (interp body)`.
  show (if (dequeueChainGateB k id actor cell depId
            && (queueDequeueRefundK k id actor depId).isSome) = true then some k else none).bind
        (interp (RecStmt.seq
          (RecStmt.setBal (fun k => dequeueRefundBal k actor depId))
          (RecStmt.seq
            (RecStmt.setEscrows (fun k => markResolved k.escrows depId))
            (RecStmt.setQueues (fun k => dequeuePoppedQueues k id)))))
      = dequeueKernelStep k id actor cell depId
  unfold dequeueKernelStep
  by_cases hg : (dequeueChainGateB k id actor cell depId
      && (queueDequeueRefundK k id actor depId).isSome) = true
  · -- ADMIT: the guard fires (`some k`); the body produces the three-write post-state. The RHS opens its
    -- `if` on `dequeueChainGateB`, then its `match` on `queueDequeueRefundK` (which is `some` by the gate).
    rw [if_pos hg]
    simp only [Option.bind]                 -- `(some k).bind (interp body) = interp body k`
    obtain ⟨hgate, hsome⟩ := (queueDequeueGate_iff id actor cell depId k).mp hg
    rw [if_pos hgate]
    -- `queueDequeueRefundK` is `some (k', m)` (from `hsome`); name it WITHOUT reverting the goal.
    obtain ⟨⟨k', m⟩, hk⟩ := Option.isSome_iff_exists.mp hsome
    -- RHS `match some (k', m) => some k'` (rewrite by `hk`); LHS body = the three ORDERED writes on `k`.
    rw [hk, queueDequeueBody_eq]
    -- `{ k with bal := dequeueRefundBal …, escrows := markResolved …, queues := dequeuePoppedQueues … }
    -- = k'` because the three direct projections ARE `k'.bal/.escrows/.queues` and every other field of
    -- `k'` equals `k`'s (the dequeue frames them — `queueDequeueRefundK_rebuild`).
    exact congrArg some (queueDequeueRefundK_rebuild hk)
  · -- REJECT: the guard fails ⇒ `none.bind _ = none`. The RHS closes: gate false, or refundK none.
    rw [if_neg hg]
    simp only [Option.bind]                 -- `none.bind _ = none`
    -- decode the failed gate Bool to show the RHS `if`/`match` is also `none`.
    rw [Bool.and_eq_true, not_and_or] at hg
    rcases hg with hgate | hsome
    · -- the 4-conjunct gate is false ⇒ RHS `if` is `none`.
      rw [if_neg (by simpa using hgate)]
    · -- the gate holds but `queueDequeueRefundK` is none ⇒ RHS `match` is `none`.
      by_cases hgate : dequeueChainGateB k id actor cell depId = true
      · rw [if_pos hgate]
        cases hk : queueDequeueRefundK k id actor depId with
        | none => rfl
        | some kr => rw [hk] at hsome; exact absurd (by simp) hsome
      · rw [if_neg hgate]

#assert_axioms interp_queueDequeueStmt_eq_kernelStep

/-! ## §3 — lifting the kernel cornerstone to the CHAINED executor `execFullA`.

The full-state triple descriptor (§4) is keyed on the CHAINED executor `execFullA` over `RecChainedState`
(kernel + receipt log) via the arm `execFullA s (.queueDequeueA id actor cell depId) = queueDequeueChainA
s id actor cell depId`. The §2 cornerstone is over the kernel projection `dequeueKernelStep`. The chained
layer is exactly that kernel step PLUS the receipt-log prepend `dequeueReceipt actor cell
(dequeueRefundAmount s.kernel depId) :: s.log`. We bridge faithfully. -/

/-- **`interp_queueDequeueStmt_chained` — the IR term's executor, lifted to the chained `execFullA`.**
When the §2 cornerstone commits on the kernel (`interp (queueDequeueStmt …) st.kernel = some k'`), the
unified action executor `execFullA st (.queueDequeueA id actor cell depId)` commits to the chained state
`⟨k', dequeueReceipt actor cell (dequeueRefundAmount st.kernel depId) :: st.log⟩`. So the Argus term's
kernel meaning lifts to the chained executor the full-state descriptor speaks about. -/
theorem interp_queueDequeueStmt_chained
    (st : RecChainedState) (id : Nat) (actor cell : CellId) (depId : Nat) (k' : RecordKernelState)
    (hexec : interp (queueDequeueStmt id actor cell depId) st.kernel = some k') :
    execFullA st (.queueDequeueA id actor cell depId)
      = some { kernel := k',
               log := dequeueReceipt actor cell (dequeueRefundAmount st.kernel depId) :: st.log } := by
  -- the §2 cornerstone turns the IR term into the kernel step `dequeueKernelStep`.
  rw [interp_queueDequeueStmt_eq_kernelStep] at hexec
  -- `execFullA … (.queueDequeueA …)` reduces to `queueDequeueChainA st …`.
  show queueDequeueChainA st id actor cell depId
      = some { kernel := k', log := _ :: st.log }
  unfold queueDequeueChainA
  -- `dequeueKernelStep` = the kernel of `queueDequeueChainA`: open its gate + `match`.
  unfold dequeueKernelStep at hexec
  by_cases hgate : dequeueChainGateB st.kernel id actor cell depId = true
  · -- the gate holds; `dequeueChainGateB` IS the 4-conjunct `if` condition of `queueDequeueChainA`.
    rw [if_pos hgate] at hexec
    have hgate' : stateAuthB st.kernel.caps actor cell = true
        ∧ acceptsEffects st.kernel cell = true
        ∧ dequeueBindB st.kernel actor depId = true
        ∧ queueDequeueHeadB st.kernel id actor depId = true := by
      simpa only [dequeueChainGateB, Bool.and_eq_true, and_assoc] using hgate
    rw [if_pos hgate']
    cases hk : queueDequeueRefundK st.kernel id actor depId with
    | none => rw [hk] at hexec; exact absurd hexec (by simp)
    | some kr =>
        obtain ⟨k'', m⟩ := kr
        rw [hk] at hexec; simp only [Option.some.injEq] at hexec; subst hexec
        -- the chained `match some (k'', _)` reduces to the receipt-prepended state; `dequeueReceipt`
        -- unfolds to the exact `{actor, src:=cell, dst:=actor, amt:=dequeueRefundAmount …}` row.
        simp only [dequeueReceipt]
  · -- the gate fails ⇒ the kernel step is `none`, contradicting `hexec : … = some k'`.
    rw [if_neg hgate] at hexec; exact absurd hexec (by simp)

#assert_axioms interp_queueDequeueStmt_chained

/-! ## §4 — THE COMPILE WELD: a satisfying witness of `queueDequeue`'s OWN full-state triple circuit
agrees with the FULL post-state the IR term's executor interpretation produces.

This welds against `queueDequeue`'s GENUINE full-state triple descriptor `queueDequeueE` (the v2
`EffectCommit3`-triple circuit whose soundness is `queueDequeueA_full_sound`), NOT the per-cell EffectVM
row — see the descriptor investigation in this file's header. The executor side is routed through §3
(`interp` ⟹ `execFullA`) and the independent `execFullA_queueDequeueA_iff_spec` (executor ⟺
`QueueDequeueSpec`); the circuit side is the audited `queueDequeueA_full_sound` (circuit ⟹
`QueueDequeueSpec`). Both name the SAME `QueueDequeueSpec`, so they PROVABLY agree on the WHOLE 17-field
state + the receipt log — strictly stronger than a per-cell weld. -/

/-- The Argus circuit interpretation of a `queueDequeue` term: `queueDequeue`'s OWN audited standalone v2
`EffectCommit3`-triple circuit step — the full-state arithmetization `satisfiedE2Triple S (queueDequeueE
…) (encodeE2Triple …)` satisfied on the encoded `(st, args, st')` triple. Its soundness
`queueDequeueA_full_sound` pins the complete `QueueDequeueSpec`. The `queueDequeue`-keyed analog of
`BalanceA.balanceACircuit`, in the universe where queueDequeue carries its OWN genuine full-state circuit
(the three whole-structure digests for `queues`/`bal`/`escrows`). -/
def queueDequeueCircuit (S : Surface2)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (st : RecChainedState) (args : DequeueArgs) (st' : RecChainedState) : Prop :=
  satisfiedE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE)
    (encodeE2Triple S (queueDequeueE D hD LQ cNQ hNQ hLQ LE cNE hNE hLE) st args st')

/-- **`queueDequeueSpec_unique` — the spec pins a UNIQUE post-state.** Two chained states that BOTH
satisfy `QueueDequeueSpec st id actor cell depId ·` are equal. Rather than re-derive this field-by-field,
we route through the PROVEN executor⟺spec corner `execFullA_queueDequeueA_iff_spec`: each
`QueueDequeueSpec` reconstructs the SAME committed value `execFullA st (.queueDequeueA …) = some ·`, and
`some` is injective. This is exactly the sense in which `QueueDequeueSpec` is functional — it determines
the post-state — so the circuit-side and executor-side spec facts collapse to one welded post-state. -/
theorem queueDequeueSpec_unique {st st₁ st₂ : RecChainedState} {id : Nat} {actor cell : CellId}
    {depId : Nat}
    (h₁ : QueueDequeueSpec st id actor cell depId st₁)
    (h₂ : QueueDequeueSpec st id actor cell depId st₂) : st₁ = st₂ := by
  have e₁ : execFullA st (.queueDequeueA id actor cell depId) = some st₁ :=
    (execFullA_queueDequeueA_iff_spec st id actor cell depId st₁).mpr h₁
  have e₂ : execFullA st (.queueDequeueA id actor cell depId) = some st₂ :=
    (execFullA_queueDequeueA_iff_spec st id actor cell depId st₂).mpr h₂
  exact Option.some.injEq _ _ ▸ (e₁.symm.trans e₂)

/-- **`queueDequeue_compile_sound` — the welded soundness (queueDequeue slice), against queueDequeue's
OWN full-state triple descriptor.**

Suppose, for the Argus queueDequeue term `queueDequeueStmt id actor cell depId` (with
`args = ⟨id, actor, cell, depId⟩`):
  * the standalone queueDequeue circuit `queueDequeueCircuit S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE st args
    st'` (= `queueDequeueE`'s full-state triple arithmetization satisfied on the encoded triple) holds,
    under the realizable whole-structure digest portals (`hRest : RestIffNoQueuesBalEscrows S.RH`,
    `hLog : logHashInjective S.LH`, and the three component digest injectivities `hD`/`hLQ`/`hNQ`/
    `hLE`/`hNE`);
  * the IR term's EXECUTOR interpretation COMMITS on the kernel: `interp (queueDequeueStmt …) st.kernel =
    some k'` (`hexec`).

Then the chained post-state the circuit pins is EXACTLY the chained post-state the IR term's executor
produces: `st' = { kernel := k', log := dequeueReceipt actor cell (dequeueRefundAmount st.kernel depId)
:: st.log }`. I.e. queueDequeue's OWN full-state circuit and the IR term AGREE on the WHOLE 17-field
RecordKernelState (`queues` popped, `bal` refund-credited, `escrows` resolved, every other field frozen)
AND the receipt log — the full `QueueDequeueSpec`, not a per-cell projection. So the circuit the prover
runs for queueDequeue pins the complete state the IR term's executor produces.

DIVERGENCE (carried, not papered): the per-row EffectVM runtime descriptor TICKS the cell nonce; the
full-state triple welded HERE FREEZES `cell` entirely (it is part of `QueueDequeueSpec`'s frame). The
runtime tick is reconciled at the turn level (`Argus/Nonce`), NOT part of this full-state statement. -/
theorem queueDequeue_compile_sound
    (S : Surface2)
    (D : (CellId → AssetId → ℤ) → ℤ) (hD : Function.Injective D)
    (LQ : QueueRecord → ℤ) (cNQ : List ℤ → ℤ) (hNQ : compressNInjective cNQ)
    (hLQ : listLeafInjective LQ) (LE : EscrowRecord → ℤ) (cNE : List ℤ → ℤ)
    (hNE : compressNInjective cNE) (hLE : listLeafInjective LE)
    (hRest : RestIffNoQueuesBalEscrows S.RH) (hLog : logHashInjective S.LH)
    (st st' : RecChainedState) (id : Nat) (actor cell : CellId) (depId : Nat) (k' : RecordKernelState)
    (hcirc : queueDequeueCircuit S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE st
      ⟨id, actor, cell, depId⟩ st')
    (hexec : interp (queueDequeueStmt id actor cell depId) st.kernel = some k') :
    st' = { kernel := k',
            log := dequeueReceipt actor cell (dequeueRefundAmount st.kernel depId) :: st.log } := by
  -- circuit side: queueDequeue's OWN audited soundness forces the FULL `QueueDequeueSpec` on `(st, args, st')`.
  have hspec : QueueDequeueSpec st id actor cell depId st' :=
    queueDequeueA_full_sound S D hD LQ cNQ hNQ hLQ LE cNE hNE hLE hRest hLog st
      ⟨id, actor, cell, depId⟩ st' hcirc
  -- executor side: the §3 chained lift gives `execFullA … = some ⟨k', dequeueReceipt … :: st.log⟩`, and the
  -- independent executor⟺spec corner turns THAT into `QueueDequeueSpec st id actor cell depId ⟨k', …⟩`.
  have hspec' : QueueDequeueSpec st id actor cell depId
      { kernel := k', log := dequeueReceipt actor cell (dequeueRefundAmount st.kernel depId) :: st.log } :=
    (execFullA_queueDequeueA_iff_spec st id actor cell depId _).mp
      (interp_queueDequeueStmt_chained st id actor cell depId k' hexec)
  -- both states satisfy the SAME spec ⇒ they are the same state (the spec pins every kernel field + log).
  exact queueDequeueSpec_unique hspec hspec'

#assert_axioms queueDequeue_compile_sound

/-! ## §5 — NON-VACUITY: the IR term genuinely POPS the FIFO + REFUNDS (observable), the welded circuit
is the genuine full-state descriptor (not a placeholder), and the gate REJECTS forged inputs (fail-closed).

The cornerstone/weld would be hollow if `queueDequeue` never committed, if the move were a no-op, or if
the gate admitted everything. A concrete kernel `kQ0` (one live owner cell `0`; a queue id `5` owned by
`0` holding the head message hash `99`; a parked unresolved deposit record `depId 3` bound to that queue
+ head, refunding `0` of asset `0` to `0`) exercises a real pop+refund; the rejection lemmas show guard
legs fail closed. The `0`-amount keeps the refund-credit trivial so the witness isolates the FIFO pop +
the `escrows` resolve + the gates. -/

/-- A concrete kernel for the witnesses. Cell `0` is a live account (lifecycle defaults Live). Queue id
`5` is owned by `0`, capacity `1`, holding ONE message hash `99` at the head. A parked UNRESOLVED deposit
record `depId 3` is bound to `(queueDep := some 5, queueMsg := some 99)`, recipient `0` (the dequeuer),
creator `0`, refunding `0` of asset `0`. This satisfies the full P0-1-full binding chain so a dequeue of
queue `5` by owner `0` naming deposit `3` commits. -/
def kQ0 : RecordKernelState :=
  { accounts := {0}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => [Authority.Cap.node 0]
    queues := [{ id := 5, owner := 0, capacity := 1, buffer := [99] }]
    escrows := [{ id := 3, creator := 0, recipient := 0, amount := 0, resolved := false,
                  asset := 0, queueDep := some 5, queueMsg := some 99 }] }

/-- **NON-VACUITY (the FIFO POP is OBSERVABLE).** The committed dequeue DROPS queue `5`'s buffer from
`[99]` to `[]` — the head message genuinely LEAVES the FIFO (the `setQueues`/`queueDequeueK` pop-front is
real, not a no-op). -/
theorem queueDequeueStmt_pops :
    (interp (queueDequeueStmt 5 0 0 3) kQ0).map
        (fun k => (k.queues.find? (fun q => q.id == 5)).map (·.buffer))
      = some (some []) := by
  rw [interp_queueDequeueStmt_eq_kernelStep]
  decide

/-- **NON-VACUITY (the deposit RESOLVE is OBSERVABLE).** The committed dequeue flips the parked deposit
record (`depId 3`)'s `resolved` flag `false → true` (via `settleEscrowRawAsset`/`markResolved` inside
`queueDequeueRefundK`): the `escrows` side-table write is a real, observable state edit. -/
theorem queueDequeueStmt_resolves :
    (interp (queueDequeueStmt 5 0 0 3) kQ0).map
        (fun k => (k.escrows.find? (fun r => r.id == 3)).map (·.resolved))
      = some (some true) := by
  rw [interp_queueDequeueStmt_eq_kernelStep]
  decide

/-- **NON-VACUITY (fail-closed: not the owner).** A dequeue by a NON-owner (actor `1`, who is not queue
`5`'s owner `0`) does NOT commit — the owner gate inside `queueDequeueK` fails (and the authority/binding
gates besides). The term returns `none`; no message can be popped by a non-owner. -/
theorem queueDequeueStmt_rejects_non_owner :
    interp (queueDequeueStmt 5 1 1 3) kQ0 = none := by
  rw [interp_queueDequeueStmt_eq_kernelStep]
  decide

/-- **NON-VACUITY (fail-closed: wrong deposit binding).** A dequeue naming a deposit id with NO parked
record (`depId 8`) does NOT commit — the P0-1 binding gate `dequeueBindB`/`queueDequeueHeadB` fails
closed. The term returns `none`; a dequeue cannot run without a bound deposit. -/
theorem queueDequeueStmt_rejects_unbound_deposit :
    interp (queueDequeueStmt 5 0 0 8) kQ0 = none := by
  rw [interp_queueDequeueStmt_eq_kernelStep]
  decide

/-- **NON-VACUITY (fail-closed: empty / absent queue).** A dequeue of a NON-existent queue id (`7`) does
NOT commit — `queueDequeueK`'s `findQueue` fails closed (so does the head-binding gate). The term returns
`none`; no value is conjured from an absent queue. -/
theorem queueDequeueStmt_rejects_absent_queue :
    interp (queueDequeueStmt 7 0 0 3) kQ0 = none := by
  rw [interp_queueDequeueStmt_eq_kernelStep]
  decide

#assert_axioms queueDequeueStmt_pops
#assert_axioms queueDequeueStmt_resolves
#assert_axioms queueDequeueStmt_rejects_non_owner
#assert_axioms queueDequeueStmt_rejects_unbound_deposit
#assert_axioms queueDequeueStmt_rejects_absent_queue

end Dregg2.Circuit.Argus.Effects.QueueDequeue
