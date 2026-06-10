/-
# Dregg2.Exec.Handlers.Escrow — the NOTE handler batch (F1b: the escrow/obligation handlers are GONE).

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler`. F1b deleted the kernel
escrow holding-store (`RecordKernelState.escrows`) and its ops (`createEscrowKAsset`/
`releaseEscrowKAsset`/`refundEscrowKAsset`), so the escrow/obligation handler cluster that rode on
them (`createEscrowA`/`releaseEscrowA`/`refundEscrowA` + the obligation aliases, including the
R2-closing settle-actor gate) is GONE WITH IT — escrow/obligation semantics (deposit/release/refund,
conservation, no-double-resolve, settle-condition, the settle-actor gate) live in the proven factory
contracts (`Apps/{EscrowFactory,ObligationFactory}.lean`) over factory-born cells' OWN `bal` columns.

What remains registered here is the NOTE cluster:

  * `noteSpendA` — the double-spend gate (step `noteSpendNullifier`; a replayed nullifier is rejected).
  * `noteCreateA` — the grow-only fresh-commitment insert (total, `delta = 0`, self-limiting freshness).

`#eval`-verified TEETH: double-spend rejected, create total + neutral. Standalone: `lake build
Dregg2.Exec.Handlers.Escrow`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Escrow

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle)

/-! ## §4 — Note handlers: the double-spend gate + the grow-only commitment insert.

`noteSpendNullifier` inserts a nullifier IF it is not already present (rejecting a double-spend,
`apply.rs:942`); it touches ONLY `nullifiers`, so the per-asset measure is UNCHANGED at every
asset (`delta = 0`). `noteCreateCommitment` inserts a FRESH commitment into the grow-only set; a fresh
commitment cannot conflict, so it ALWAYS commits (total, `delta = 0`, self-limiting freshness — the
grow-only dual of the nullifier gate). Both are balance-NEUTRAL: `recTotalAsset` reads
`bal`, never `nullifiers`/`commitments`, so `conserves` is `rfl`-grade. -/

/-- Note-spend arguments: the actor + the nullifier being spent. -/
structure NoteSpendArgs where
  /-- The actor spending the note (the receipt subject; the double-spend gate is on the nullifier set,
  not capability authority — the §8 STARK spending-proof is the crypto-portal face). -/
  actor : CellId
  /-- The nullifier derived from the spent note. -/
  nf : Nat

/-- The note-spend step: the kernel's fail-closed double-spend gate (a replayed nullifier ⇒ `none`). -/
def noteSpendStep (k : RecordKernelState) (a : NoteSpendArgs) : Option RecordKernelState :=
  noteSpendNullifier k a.nf

/-- `noteSpendNullifier` touches only `nullifiers`, so the per-asset ledger
measure is LITERALLY unchanged whenever it commits. -/
theorem noteSpendStep_measure_fixed (k k' : RecordKernelState) (a : NoteSpendArgs)
    (h : noteSpendStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b := by
  unfold noteSpendStep noteSpendNullifier at h
  by_cases hin : a.nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h
    rfl

/-- **`noteSpendA` — the registered note-spend handler.** The double-spend gate is the kernel's
nullifier-set membership check (a replay ⇒ `none`). `delta = 0` (touches only `nullifiers`).
`admission`/`auth` are the default-true gates here (the real gate is the double-spend set membership IN
the step, plus the §8 spending-proof portal); the load-bearing teeth is the double-spend `#eval` below. -/
def noteSpendA : EffectHandler NoteSpendArgs where
  step := noteSpendStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    rw [noteSpendStep_measure_fixed s s' a h b]; ring

/-- Note-create arguments: the actor + the fresh commitment. -/
structure NoteCreateArgs where
  /-- The actor creating the note (the receipt subject). -/
  actor : CellId
  /-- The fresh Pedersen commitment to insert (always fresh — no conflict). -/
  cm : Nat

/-- The note-create step: ALWAYS commits (the grow-only fresh-commitment insert). -/
def noteCreateStep (k : RecordKernelState) (a : NoteCreateArgs) : Option RecordKernelState :=
  some (noteCreateCommitment k a.cm)

/-- **`noteCreateA` — the registered note-create handler (TOTAL, self-limiting freshness).** Always
commits (a fresh commitment cannot conflict — the grow-only dual of the nullifier gate). `delta = 0`
(touches only `commitments`); `conserves` from `noteCreate_recTotalAsset`. `auth`/`admission` default
true (the §8 range-proof is the crypto-portal face). -/
def noteCreateA : EffectHandler NoteCreateArgs where
  step := noteCreateStep
  delta := fun _ _ => 0
  auth := fun _ _ => true
  admission := fun _ _ => true
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by intro s a s' _; rfl
  admission_gated := by intro s a s' _; rfl
  conserves := by
    intro s a s' h b
    unfold noteCreateStep at h
    simp only [Option.some.injEq] at h; subst h
    rw [noteCreate_recTotalAsset s a.cm b]; ring

/-! ## §5 — The batch registry: the note cluster as coproduct entries.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler` (it is generic over
the registry). -/

/-- The note batch registry (the coproduct menu for this cluster). -/
def escrowBatchRegistry : Registry :=
  [ ⟨NoteSpendArgs, noteSpendA⟩,
    ⟨NoteCreateArgs, noteCreateA⟩ ]

/-- Build a closed note-spend effect (tag `0`). -/
def noteSpendEffect (actor : CellId) (nf : Nat) : ClosedEffect :=
  { tag := 0, Args := NoteSpendArgs, args := { actor := actor, nf := nf }, handler := noteSpendA }

/-- Build a closed note-create effect (tag `1`). -/
def noteCreateEffect (actor : CellId) (cm : Nat) : ClosedEffect :=
  { tag := 1, Args := NoteCreateArgs, args := { actor := actor, cm := cm }, handler := noteCreateA }

/-! ## §6 — TEETH: the note gates, evaluated (`#eval`-verified).

A fixture with two accounts (0, 1), cell 0 holding 100 of asset 0, with self-authority. (F1b: the R2
escrow-settle attack fixtures left with the kernel escrow store — the settle-actor gate lives in the
factory contract now, with its own teeth in `Apps/EscrowFactory.lean`.) -/

/-- The base fixture: cells 0,1 accounts; cell 0 holds 100 of asset 0; self-authority; both Live. -/
def es0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

-- §TEETH-8 (NOTE double-spend): a first spend of nullifier 7 succeeds; a replay is REJECTED.
#guard ((execEffect (noteSpendEffect 0 7) es0).isSome)  --  true
#guard (((noteSpendStep es0 { actor := 0, nf := 7 }).bind
        (fun k => noteSpendStep k { actor := 0, nf := 7 })).isSome) == false  --  false
-- §TEETH-9 (NOTE create total): a note-create always commits and is balance-neutral.
#guard ((execEffect (noteCreateEffect 0 42) es0).map (fun k => (k.commitments, recTotalAsset k 0))) == some ([42], 100)  -- some ([42], 100)
-- §TEETH-10 (turn conserves): a turn [spend; create] runs the foldlM and conserves.
#guard ((execTurn [noteSpendEffect 0 7, noteCreateEffect 0 42] es0).map
        (fun k => recTotalAsset k 0)) == some 100  --  some 100

/-! ## §7 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs), and
each settle-actor / conservation helper is pinned directly. A `sorryAx` anywhere fails the pin AND the
build. -/

#assert_axioms noteSpendStep_measure_fixed
#assert_axioms noteSpendA
#assert_axioms noteCreateA

/-! ## §DEFER — scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **`noteSpend` capability authority.** The note-spend gate here is the kernel's double-spend
    nullifier-set check (the real anti-replay invariant); the SPENDING PROOF (a STARK that the spender
    owns the note + correct nullifier derivation) is the §8 `CryptoPortal` face, entering as a portal
    obligation, not a `Bool` capability gate. `auth`/`admission` are default-true here because the gate
    that matters (double-spend) lives in the step and is `#eval`-teeth-verified.
-/

end Dregg2.Exec.Handlers.Escrow
