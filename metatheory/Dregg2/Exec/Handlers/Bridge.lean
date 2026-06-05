/-
# Dregg2.Exec.Handlers.Bridge — the cross-chain BRIDGE handler batch (the `delta < 0` milestone).

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler` (read that module first:
the `EffectHandler` record bundling `step`/`delta`/`auth`/`admission`/`trace` WITH the forced obligation
proofs `auth_gated`/`admission_gated`/`conserves`, the registry coproduct, and the generic
`turn_conserves` that SUMS the per-effect per-asset deltas). We register one handler per phase of dregg1's
two-phase note bridge, each reusing that phase's ALREADY-PROVED kernel step + combined-measure lemma +
authority gate from `Dregg2.Exec.RecordKernel`. We do NOT touch `TurnExecutorFull`'s
`execFullA`/`FullActionA` (that cutover is a later step); we only IMPORT and REUSE.

The bridge is the bridge-shaped TWIN of escrow over the SHARED off-ledger holding-store, BUT its FINALIZE
phase is the one place the holding-store pair does NOT conserve — and honestly so:

  * **bridgeLock** (Phase 1, `initiate_bridge`): DEBIT the originator + PARK the value in a `Locked`,
    `bridge := true`-tagged record. The bare `bal` DROPS by `amount`; the holding-store RISES by `amount`;
    the COMBINED per-asset measure is CONSERVED — IDENTICAL to escrow-create. `delta = 0`. `conserves`
    cites the proved `bridge_lock_conserves_combined_per_asset`; `auth_gated` from
    `bridgeLockKAsset_authorized` (the `authorizedB` gate over the debited originator).

  * **bridgeFinalize** (Phase 3, `finalize_bridge`) — **THE `delta < 0` MILESTONE, CLOSING R12.** The §8
    confirmation receipt arrived; the lock resolves and the value LEAVES for the other chain. On the
    COMBINED measure this is a no-credit resolve: the bare `bal` is untouched (the value already left the
    ledger at lock) but the held value DROPS — so `recTotalAssetWithEscrow` DROPS by the bridged amount, a
    DISCLOSED OUTFLOW (like burn). The catalog historically MISLABELLED `bridgeFinalize` `Conservative`
    (`CatalogInstances.effectLinearity`); it is NOT — it is `Annihilative` (a disclosed non-conservation).
    So `bridgeFinalizeH.delta` is NEGATIVE: `if b = asset then -amount else 0`, and `conserves` proves the
    combined measure DROPS by exactly the disclosed amount, composing the proved
    `bridgeFinalizeKAsset_moves_combined_per_asset`. This is the first handler that exercises the SUMMING
    of a `delta < 0` per-effect contribution in the global `turn_conserves` — the disclosed outflow is now
    correctly ACCOUNTED, not hidden as a conserved move. The bare `bridgeFinalizeKAsset` carries NO actor
    authority, so we WRAP the `bridgeAuthOK` creator-only gate (the missing one the re-audit flagged:
    "anyone who knows the id could finalize a victim's lock"); `auth_gated` makes that a TYPING obligation.

  * **bridgeCancel** (Phase 4, `cancel_bridge`): the timeout was reached without a receipt; the value is
    REFUNDED to the originator (credit + resolve). COMBINED per-asset CONSERVED — IDENTICAL to
    escrow-refund. `delta = 0`. `conserves` cites `bridge_cancel_conserves_combined_per_asset`; `auth_gated`
    from the wrapped `bridgeAuthOK` creator-only gate.

  * **pipelinedSend** (dregg1 `apply_pipelined_send`, the apply-time NEUTRAL marker): the `EventualRef`
    resolution already ran in the pipeline; the apply-time effect is a pure CLOCK RECEIPT row — it leaves
    the kernel state LITERALLY unchanged. TOTAL (always commits), `delta = 0`, `conserves` is `rfl`-grade.

EVAL-VERIFIED (`§TEETH`): bridgeFinalize on a Live bridge record DROPS the combined measure by exactly
`amount` (the new total < the old); the `bridgeAuthOK` creator-only gate REJECTS a non-creator finalize
/cancel; lock/cancel are combined-conserving; a mismatched-`(asset, amount)` finalize is fail-closed.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/eval-only. Every keystone `#assert_axioms`-pinned
(a `sorryAx` fails the pin and the build). Pure, computable, `#eval`-able. Verified standalone:
`lake build Dregg2.Exec.Handlers.Bridge`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Bridge

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle bridgeAuthOK)

/-! ## §1 — `bridgeLockA`: Phase-1 lock, combined-conserving (`delta = 0`).

`bridgeLockKAsset` debits the originator by `amount` and parks the same `amount` in the `bridge := true`
holding-store record, so the COMBINED per-asset measure is unchanged — `delta = 0`. `conserves` cites the
proved `bridge_lock_conserves_combined_per_asset` directly; `auth_gated` from `bridgeLockKAsset_authorized`
(the `authorizedB` gate over the debited originator — the SAME capability gate as transfer). The kernel
lock already gates the originator liveness (`originator ∈ accounts`); we mirror that into `admission` via
the creator-Live wrapper so `admission_gated` is genuinely provable. -/

/-- Bridge-lock arguments (the executable `bridgeLockKAsset` signature). -/
structure BridgeLockArgs where
  /-- The bridge record id (dregg1's `[u8;32]` bridge key). -/
  id : Nat
  /-- The actor performing the lock (authority subject). -/
  actor : CellId
  /-- The originator whose `asset` column is debited (the refund target on cancel). -/
  originator : CellId
  /-- The destination cell the bridge value is heading to. -/
  destination : CellId
  /-- The locked asset. -/
  asset : AssetId
  /-- The locked amount. -/
  amount : Int

/-- The synthesized authority turn `bridgeLockKAsset` checks (`actor` moves `amount` originator⇒destination). -/
def bridgeLockTurn (a : BridgeLockArgs) : Turn :=
  { actor := a.actor, src := a.originator, dst := a.destination, amt := a.amount }

/-- The lifecycle-gated bridge lock: the ORIGINATOR must be Live, then run the proved lock. -/
def bridgeLockStep (k : RecordKernelState) (a : BridgeLockArgs) : Option RecordKernelState :=
  if acceptsEffects k a.originator then
    bridgeLockKAsset k a.id a.actor a.originator a.destination a.asset a.amount
  else none

/-- Authority extracted from `bridgeLockKAsset`'s fail-closed gate. -/
theorem bridgeLockStep_authorized (k k' : RecordKernelState) (a : BridgeLockArgs)
    (h : bridgeLockStep k a = some k') : authorizedB k.caps (bridgeLockTurn a) = true := by
  unfold bridgeLockStep at h
  by_cases hadm : acceptsEffects k a.originator
  · rw [if_pos hadm] at h
    exact bridgeLockKAsset_authorized h
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`bridgeLockA` — the registered Phase-1 bridge-lock handler.** `conserves` cites the proved
combined-conservation keystone `bridge_lock_conserves_combined_per_asset` (`delta = 0`); `auth_gated` via
`bridgeLockStep_authorized`; `admission_gated` from the originator-Live wrapper. -/
def bridgeLockA : EffectHandler BridgeLockArgs where
  step := bridgeLockStep
  delta := fun _ _ => 0           -- debit ledger / park in bridge store ⇒ combined measure fixed
  auth := fun k a => authorizedB k.caps (bridgeLockTurn a)
  admission := fun k a => acceptsEffects k a.originator
  trace := bridgeLockTurn
  auth_gated := by intro s a s' h; exact bridgeLockStep_authorized s s' a h
  admission_gated := by
    intro s a s' h
    unfold bridgeLockStep at h
    by_cases hadm : acceptsEffects s a.originator
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold bridgeLockStep at h
    by_cases hadm : acceptsEffects s a.originator
    · rw [if_pos hadm] at h
      have := bridge_lock_conserves_combined_per_asset (k := s) (k' := s') (id := a.id)
        (actor := a.actor) (originator := a.originator) (destination := a.destination)
        (asset := a.asset) (amount := a.amount) b h
      rw [this]; ring
    · rw [if_neg hadm] at h; exact absurd h (by simp)

/-! ## §2 — `bridgeFinalizeA`: Phase-3 finalize — **THE `delta < 0` MILESTONE (CLOSES R12).**

`bridgeFinalizeKAsset` is a no-credit resolve: the bare `bal` is untouched (the value left at lock) but
the held value DROPS as the record leaves the unresolved set — so the COMBINED measure DROPS by the
disclosed `amount` at the disclosed `asset`. This is a DISCLOSED OUTFLOW (the value genuinely left for the
other chain — a burn), NOT a conserved move: `bridgeFinalizeH.delta = if b = asset then -amount else 0` is
NEGATIVE at the bridged asset. The proved `bridgeFinalizeKAsset_moves_combined_per_asset` states exactly
this drop, so `conserves` reads off it after a `← neg_eq, sub` normalization (the lemma's `- (if … then
amount else 0)` is definitionally `+ (if … then -amount else 0)` per asset). This is the first registered
handler whose `delta` is NEGATIVE — it exercises the path the global `turn_conserves` SUMS a `delta < 0`
contribution along, so the disclosed outflow is now correctly ACCOUNTED in the turn measure (the catalog
mislabel of `bridgeFinalize` as `Conservative` was the symptom; the honest color is `Annihilative`).

The bare `bridgeFinalizeKAsset` carries NO actor authority (anyone who names the id could finalize a
victim's lock). We WRAP `bridgeAuthOK` — the creator-only gate (only the bridge record's RECORDED creator,
read off the committed side-table, may finalize) — so `auth_gated` is a TYPING obligation. -/

/-- Bridge-finalize/cancel arguments: the actor performing the resolve + the bridge id + the DISCLOSED
`(asset, amount)` the receipt asserts (the finalize verifies these against the parked record). -/
structure BridgeFinalizeArgs where
  /-- The bridge record id to finalize. -/
  id : Nat
  /-- The actor performing the finalize (must be the recorded creator — `bridgeAuthOK`). -/
  actor : CellId
  /-- The DISCLOSED asset class leaving for the other chain (matched against the parked record). -/
  asset : AssetId
  /-- The DISCLOSED amount leaving for the other chain (the disclosed outflow magnitude). -/
  amount : Int

/-- **The R12-closing wrapped finalize step.** Commit the kernel finalize ONLY when the actor is the
recorded creator (`bridgeAuthOK`); the bare op (anyone-finalizes) is otherwise unchanged. -/
def bridgeFinalizeStep (k : RecordKernelState) (a : BridgeFinalizeArgs) : Option RecordKernelState :=
  if bridgeAuthOK k a.id a.actor then bridgeFinalizeKAsset k a.id a.asset a.amount else none

/-- **`bridgeFinalizeA` — the registered Phase-3 finalize handler (`delta < 0`, the disclosed outflow).**
`delta a b = if b = a.asset then -a.amount else 0` — NEGATIVE at the bridged asset (the value left for the
other chain). `conserves` reads off the proved `bridgeFinalizeKAsset_moves_combined_per_asset` (the combined
measure DROPS by exactly the disclosed amount). `auth_gated` BITES via the wrapped `bridgeAuthOK`
creator-only gate; `admission` reports the same creator gate (the finalize-liveness is the record's own
existence, surfaced by `bridgeAuthOK` finding the unresolved bridge record). -/
def bridgeFinalizeA : EffectHandler BridgeFinalizeArgs where
  step := bridgeFinalizeStep
  delta := fun a b => if b = a.asset then (-a.amount) else 0   -- DISCLOSED OUTFLOW: negative at the asset
  auth := fun k a => bridgeAuthOK k a.id a.actor
  admission := fun k a => bridgeAuthOK k a.id a.actor
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := -a.amount }
  auth_gated := by
    intro s a s' h
    unfold bridgeFinalizeStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold bridgeFinalizeStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold bridgeFinalizeStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · rw [if_pos hg] at h
      -- the proved finalize lemma: combined DROPS by the disclosed amount at the disclosed asset.
      have hmove := bridgeFinalizeKAsset_moves_combined_per_asset (k := s) (k' := s')
        (id := a.id) (asset := a.asset) (amount := a.amount) b h
      rw [hmove]
      -- `- (if b = asset then amount else 0) = + (if b = asset then -amount else 0)`, per asset.
      by_cases hba : b = a.asset
      · rw [if_pos hba, if_pos hba]; ring
      · rw [if_neg hba, if_neg hba]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — `bridgeCancelA`: Phase-4 cancel/refund, combined-conserving (`delta = 0`).

`bridgeCancelKAsset` refunds the originator (`+amount` credit) and resolves the record (holding-store drop),
so the COMBINED per-asset measure is CONSERVED at every asset — IDENTICAL to escrow-refund. `delta = 0`.
`conserves` cites the proved `bridge_cancel_conserves_combined_per_asset` directly. The bare op carries no
actor authority, so we WRAP the SAME `bridgeAuthOK` creator-only gate (only the recorded creator may cancel
their own lock); `auth_gated` makes that a TYPING obligation. -/

/-- Bridge-cancel arguments: the actor performing the cancel + the bridge id. -/
structure BridgeCancelArgs where
  /-- The actor performing the cancel (must be the recorded creator — `bridgeAuthOK`). -/
  actor : CellId
  /-- The bridge record id to cancel. -/
  id : Nat

/-- **The R12-companion wrapped cancel step.** Commit the kernel cancel ONLY when the actor is the recorded
creator (`bridgeAuthOK`). -/
def bridgeCancelStep (k : RecordKernelState) (a : BridgeCancelArgs) : Option RecordKernelState :=
  if bridgeAuthOK k a.id a.actor then bridgeCancelKAsset k a.id else none

/-- **`bridgeCancelA` — the registered Phase-4 cancel/refund handler.** `conserves` cites the proved
combined-conservation keystone `bridge_cancel_conserves_combined_per_asset` (`delta = 0`); `auth_gated` via
the wrapped `bridgeAuthOK` creator-only gate; `admission` reports the same creator gate (the cancel
finds-and-resolves the recorded bridge record). -/
def bridgeCancelA : EffectHandler BridgeCancelArgs where
  step := bridgeCancelStep
  delta := fun _ _ => 0           -- refund-credit offsets the holding-store drop ⇒ combined fixed
  auth := fun k a => bridgeAuthOK k a.id a.actor
  admission := fun k a => bridgeAuthOK k a.id a.actor
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold bridgeCancelStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold bridgeCancelStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold bridgeCancelStep at h
    by_cases hg : bridgeAuthOK s a.id a.actor
    · rw [if_pos hg] at h
      have := bridge_cancel_conserves_combined_per_asset (k := s) (k' := s') (id := a.id) b h
      rw [this]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §4 — `pipelinedSendA`: the apply-time NEUTRAL clock receipt (TOTAL, `delta = 0`).

dregg1's `apply_pipelined_send` (`apply.rs:2657`) is a HARD ERROR if the `EventualRef` is still unresolved
— the producer fills it in the PIPELINE step, and the resolved action ALREADY ran. So the apply-time effect
is a pure CLOCK RECEIPT row: it leaves the kernel ledger state LITERALLY unchanged (in the full executor it
appends `escrowReceiptA actor` to the LOG; the LEDGER is untouched). At the kernel-state level the step is
the IDENTITY: `some k`. TOTAL (always commits — a clock row never fails), `delta = 0`, `conserves` is
`rfl`-grade (`recTotalAssetWithEscrow` reads `bal`+`escrows`, both unchanged). The catalog's `Neutral`
coloring is honest here (`effectLinearity .pipelinedSend = Neutral`). -/

/-- Pipelined-send arguments: the actor whose clock receipt is emitted. -/
structure PipelinedSendArgs where
  /-- The actor the apply-time clock receipt names (the resolved action already ran). -/
  actor : CellId

/-- The pipelined-send step: the apply-time NEUTRAL marker — the kernel ledger state is unchanged. -/
def pipelinedSendStep (k : RecordKernelState) (_ : PipelinedSendArgs) : Option RecordKernelState :=
  some k

/-- **`pipelinedSendA` — the registered apply-time NEUTRAL pipelined-send handler.** TOTAL (always commits
— a clock receipt never fails); `delta = 0` (the kernel ledger state is identity); `conserves` is the
`rfl`-grade identity frame. `auth`/`admission` are default-true (the EventualRef resolution + producer
authority happened in the PIPELINE step; the apply-time row is pure book-keeping). -/
def pipelinedSendA : EffectHandler PipelinedSendArgs where
  step := pipelinedSendStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold pipelinedSendStep at h
    simp only [Option.some.injEq] at h; subst h
    ring

/-! ## §5 — The bridge batch registry: the lock/finalize/cancel/pipelined-send cluster as coproduct entries.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler` (it is generic over
the registry, and `turn_conserves` already SUMS arbitrary deltas — including the NEGATIVE bridgeFinalize
delta). -/

/-- The bridge batch registry (the coproduct menu for the cross-chain bridge cluster). -/
def bridgeBatchRegistry : Registry :=
  [ ⟨BridgeLockArgs, bridgeLockA⟩,
    ⟨BridgeFinalizeArgs, bridgeFinalizeA⟩,
    ⟨BridgeCancelArgs, bridgeCancelA⟩,
    ⟨PipelinedSendArgs, pipelinedSendA⟩ ]

/-- Build a closed bridge-lock effect (tag `0`). -/
def bridgeLockEffect (id : Nat) (actor originator destination : CellId) (asset : AssetId) (amount : Int) :
    ClosedEffect :=
  { tag := 0, Args := BridgeLockArgs,
    args := { id := id, actor := actor, originator := originator, destination := destination,
              asset := asset, amount := amount }, handler := bridgeLockA }

/-- Build a closed bridge-finalize effect (tag `1`; the disclosed outflow, `delta = -amount`). -/
def bridgeFinalizeEffect (id : Nat) (actor : CellId) (asset : AssetId) (amount : Int) : ClosedEffect :=
  { tag := 1, Args := BridgeFinalizeArgs,
    args := { id := id, actor := actor, asset := asset, amount := amount }, handler := bridgeFinalizeA }

/-- Build a closed bridge-cancel effect (tag `2`). -/
def bridgeCancelEffect (actor : CellId) (id : Nat) : ClosedEffect :=
  { tag := 2, Args := BridgeCancelArgs, args := { actor := actor, id := id }, handler := bridgeCancelA }

/-- Build a closed pipelined-send effect (tag `3`; apply-time neutral). -/
def pipelinedSendEffect (actor : CellId) : ClosedEffect :=
  { tag := 3, Args := PipelinedSendArgs, args := { actor := actor }, handler := pipelinedSendA }

/-! ## §6 — TEETH: the R12 `delta < 0` milestone + the `bridgeAuthOK` creator gate, evaluated.

A 2-cell, 2-asset bridge fixture (mirroring `RecordKernel.brg0`): cell 0 holds 100 of asset 1; cell 0 owns
itself (`node 1` self-cap authorizes the lock over originator 0). Cell 0 locks 30 of asset 1 (bridge id 9),
destination cell 1. Then: a FINALIZE by the creator (cell 0) DROPS the combined measure by exactly 30 (the
disclosed outflow — the `delta < 0` milestone); a finalize/cancel by a NON-creator (cell 5) is REJECTED
(the `bridgeAuthOK` gate bites); the lock and a creator-cancel are combined-conserving. -/

/-- The base fixture: cells 0,1 accounts; cell 0 holds 100 of asset 1; cell 0 holds a `node 1` self-cap;
both Live. -/
def br0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun l => if l = 0 then [Cap.node 1] else []
    bal := fun c a => if c = 0 ∧ a = 1 then 100 else 0 }

/-- The fixture after cell 0 locks 30 of asset 1 (bridge id 9, originator 0, destination 1). -/
def brLocked : Option RecordKernelState :=
  bridgeLockStep br0 { id := 9, actor := 0, originator := 0, destination := 1, asset := 1, amount := 30 }

-- §TEETH-1 (LOCK conserves): the lock fixes the COMBINED measure at asset 1 (100, held 0 → bare 70, held 30).
#eval brLocked.map (fun k => (recTotalAssetWithEscrow k 1, recTotalAsset k 1, escrowHeldAsset k 1))
        -- some (100, 70, 30) — combined CONSERVED, bare DOWN, held UP
-- §TEETH-2 (THE `delta < 0` MILESTONE, R12 CLOSED): the CREATOR (cell 0) finalizes bridge 9 ⇒ the combined
-- measure DROPS from 100 to 70 at asset 1 (a disclosed outflow of 30), asset 0 FIXED at 0. The NEW total
-- is STRICTLY LESS than the OLD total — the `delta < 0` is genuinely accounted.
#eval (brLocked.bind (fun k => execEffect (bridgeFinalizeEffect 9 0 1 30) k)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0))   -- some (70, 0) — DROPPED by 30 at asset 1
-- §TEETH-3 (the drop is STRICTLY NEGATIVE — the milestone, made explicit): new < old at the bridged asset.
#eval (brLocked.bind (fun k => execEffect (bridgeFinalizeEffect 9 0 1 30) k)).map
        (fun k' => decide (recTotalAssetWithEscrow k' 1 < recTotalAssetWithEscrow br0 1))   -- some true
-- §TEETH-4 (CREATOR-ONLY finalize, R-audit gate): a NON-creator (cell 5) finalizing bridge 9 ⇒ REJECTED.
#eval (brLocked.bind (fun k => execEffect (bridgeFinalizeEffect 9 5 1 30) k)).isSome    -- false
-- §TEETH-5 (CREATOR-ONLY cancel): a NON-creator (cell 5) cancelling bridge 9 ⇒ REJECTED.
#eval (brLocked.bind (fun k => execEffect (bridgeCancelEffect 5 9) k)).isSome           -- false
-- §TEETH-6 (HONEST CANCEL conserves): the creator (cell 0) cancels bridge 9 ⇒ the value REFUNDS to the
-- originator; combined CONSERVED at (100, 0), held back to 0, bare back to 100.
#eval (brLocked.bind (fun k => execEffect (bridgeCancelEffect 0 9) k)).map
        (fun k => (recTotalAssetWithEscrow k 1, recTotalAssetWithEscrow k 0,
                   escrowHeldAsset k 1, recTotalAsset k 1))                    -- some (100, 0, 0, 100) — REFUND round-trip CONSERVED
-- §TEETH-7 (MISMATCHED finalize fail-closed): disclosed amount 99 ≠ parked 30 (receipt-vs-pending) ⇒ REJECTED.
#eval (brLocked.bind (fun k => execEffect (bridgeFinalizeEffect 9 0 1 99) k)).isSome    -- false
-- §TEETH-8 (MISMATCHED-ASSET finalize fail-closed): disclosed asset 0 ≠ parked 1 ⇒ REJECTED.
#eval (brLocked.bind (fun k => execEffect (bridgeFinalizeEffect 9 0 0 30) k)).isSome    -- false
-- §TEETH-9 (UNAUTHORIZED lock fail-closed): actor 5 owns nothing ⇒ the lock is REJECTED.
#eval (execEffect (bridgeLockEffect 9 5 0 1 1 30) br0).isSome                           -- false
-- §TEETH-10 (PIPELINED-SEND total + neutral): always commits, leaves the combined measure unchanged.
#eval (execEffect (pipelinedSendEffect 0) br0).map (fun k => recTotalAssetWithEscrow k 1)  -- some 100
-- §TEETH-11 (turn SUMS the `delta < 0`): a turn [lock; finalize-by-creator] runs through the registry
-- foldlM; the combined measure lands at 100 - 30 = 70 — the SUM of (lock 0) + (finalize -30), the headline
-- `turn_conserves` law summing a NEGATIVE per-effect delta.
#eval (execTurn [bridgeLockEffect 9 0 0 1 1 30, bridgeFinalizeEffect 9 0 1 30] br0).map
        (fun k => recTotalAssetWithEscrow k 1)                                          -- some 70
-- §TEETH-12 (turnDelta cross-check): the §TEETH-11 turn's combined per-asset delta at asset 1 is
-- `0 + (-30) = -30` (the SUM the algebra's `turn_conserves` holds the measure to — the NEGATIVE milestone).
#eval turnDelta [bridgeLockEffect 9 0 0 1 1 30, bridgeFinalizeEffect 9 0 1 30] 1          -- -30

/-! ## §7 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs), and the
lock-authority helper is pinned directly. A `sorryAx` anywhere in the composed lemmas fails the pin AND the
build — so these pins certify that bridge lock/finalize/cancel/pipelined-send soundness (including the
`delta < 0` finalize accounting) rests only on the kernel triple. -/

#assert_axioms bridgeLockStep_authorized
#assert_axioms bridgeLockA
#assert_axioms bridgeFinalizeA
#assert_axioms bridgeCancelA
#assert_axioms pipelinedSendA

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **The §8 confirmation-receipt portal.** `bridgeFinalize` here gates on the parked record being
    present-unresolved-bridge-tagged AND the disclosed `(asset, amount)` matching it. The destination-
    federation SIGNATURE over the nullifier (`verify_bridge_receipt`) is the §8 `CryptoPortal` face — it
    enters as a portal obligation (a `Prop`-carrier hypothesis exactly as `bridgeMint`'s foreign finality),
    NOT a `Bool` gate. The LEDGER move (the disclosed outflow + creator authority) is the sound CORE here.

  * **The bridge TIMEOUT gate.** `bridgeCancel` is valid only AFTER the timeout (a relayer cannot cancel a
    still-pending lock). That predicate needs a clock/round oracle the `RecordKernelState` does not carry,
    so we register the EXECUTABLE cancel math (creator authority + per-asset conservation) and leave the
    timeout as the effect-layer gate — one more conjunct in the gate, the conservation proof unchanged.

  * **The relayer-finalize path.** `bridgeAuthOK` is creator-only (the sound CORE: the creator can always
    finalize/cancel their own lock). A relayer finalizing with a foreign receipt is the §8 receipt portal,
    deferred — adding it is a disjunct in the gate (creator OR valid-receipt-holder), the conservation and
    disclosed-outflow accounting unchanged.

  * **The catalog `Annihilative` relabel — LANDED.** This handler's NEGATIVE `delta` is the LOAD-BEARING
    fix of the R12 mislabel (the combined measure is now correctly DROPPED, not falsely conserved). The
    companion relabel of `CatalogInstances.effectLinearity .bridgeFinalize` from `Conservative` to
    `Annihilative` (now witnessed by `CatalogEffects.a_bridgeFinalize`, and the `TurnExecutorFull`
    per-effect characterization's coloring conjunct) is now done, so the catalog classification AGREES
    with this handler's proved `delta = -amount` sign. `EffectsPaired.bridgeFinalize_conserves` /
    `EffectsSupply.bridgeFinalizeStep` are SEPARATE local toys (a paired field-write / a balance-framed
    no-credit step), decoupled from the catalog color. The algebra-level accounting — the thing that makes
    the disclosed outflow REAL in `turn_conserves` — is closed HERE.
-/

end Dregg2.Exec.Handlers.Bridge
