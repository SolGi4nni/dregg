/-
# Dregg2.Exec.Handlers.Escrow — the ESCROW + OBLIGATION + NOTE handler batch.

This EXTENDS the `EffectHandler` algebra scaffolded in `Dregg2.Exec.Handler` (read that module
first: the `EffectHandler` record bundling `step`/`delta`/`auth`/`admission`/`trace` WITH the forced
obligation proofs `auth_gated`/`admission_gated`/`conserves`, the registry coproduct, and the generic
`turn_conserves`). We register MORE handlers — one per effect of the escrow/obligation/note cluster —
each reusing that effect's ALREADY-PROVED kernel step + conservation lemma + authority gate from
`Dregg2.Exec.RecordKernel`. We do NOT touch `TurnExecutorFull`'s `execFullA`/`FullActionA` (that
cutover is a later step); we only IMPORT and REUSE.

What this batch closes — **the R2 hole (settle-actor authority)**:

  `releaseEscrowKAsset`/`refundEscrowKAsset` in the kernel take ONLY the escrow `id` — they carry NO
  actor authority, so ANYONE who can name the id settles the escrow (the recipient's funds released,
  or the creator refunded, by an unrelated party). dregg1 requires the settling actor to be entitled.
  The fix is a WRAP: `releaseStep`/`refundStep` look up the unresolved record and gate on the actor's
  authority over the settlement party (the recipient for release, the creator for refund — `authorizedB`,
  the SAME capability gate as transfer). `auth_gated` makes this a TYPING obligation: a handler whose
  step ignored the actor gate would not type-check. The conservation lemma
  (`releaseEscrowKAsset_conserves_combined_per_asset`) is UNCONDITIONAL on `release k id = some k'`, so
  the wrap composes for free (the actor gate only narrows WHO may settle; the value-conservation math is
  the kernel's, cited verbatim). `delta = 0` (settle moves value ledger↔holding-store, combined fixed).

Handlers registered:

  * `createEscrowA` — mirrors the scaffold's `escrowH` (step `createEscrowKAsset`, `delta = 0`,
    conserves `escrow_create_conserves_combined_per_asset`, auth `authorizedB` over the create-turn).
  * `releaseEscrowA` / `refundEscrowA` — the **R2-closing** settle handlers (actor gate wrapped on the
    bare kernel op; conserves from the unconditional combined-conservation lemma).
  * `createObligationA` / `slashObligationA` / `fulfillObligationA` — **ALIASES** of escrow
    create/release/refund (a dregg obligation IS an escrow with obligor↔creator, beneficiary↔recipient
    naming; slash = release-to-beneficiary, fulfill = refund-to-obligor). The deadline predicate is the
    §8-DEFERRED face (documented, not enforced here — see `§DEFER`).
  * `noteSpendA` — the double-spend gate (step `noteSpendNullifier`; a replayed nullifier is rejected).
  * `noteCreateA` — the grow-only fresh-commitment insert (total, `delta = 0`, self-limiting freshness).

`#eval`-verified TEETH: the R2 attack (unauthorized settle)
returns `none`; the authorized creator/recipient returns `some`. Standalone: `lake build
Dregg2.Exec.Handlers.Escrow`.
-/
import Dregg2.Exec.Handler

namespace Dregg2.Exec.Handlers.Escrow

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec
open Dregg2.Exec.Handler
open Dregg2.Exec.TurnExecutorFull (acceptsEffects lcLive lcSealed lcDestroyed setLifecycle)

/-! ## §1 — `createEscrowA`: per-asset escrow create (mirrors the scaffold's `escrowH`).

Identical shape to `Dregg2.Exec.Handler.escrowH`: `createEscrowKAsset` debits the bare ledger by
`amount` and parks the same `amount` off-ledger, so the COMBINED per-asset measure is unchanged
(`delta = 0`). `conserves` cites `escrow_create_conserves_combined_per_asset`; `auth_gated` from the
create op's own fail-closed `authorizedB` gate; `admission_gated` from a creator-Live wrapper. We restate
it in THIS batch so the obligation cluster (create/release/refund) lives together. -/

/-- Escrow-create arguments (the executable `createEscrowKAsset` signature). -/
structure CreateEscrowArgs where
  /-- The escrow record id. -/
  id : Nat
  /-- The actor performing the create (authority subject). -/
  actor : CellId
  /-- The creator whose `asset` column is debited (the refund target). -/
  creator : CellId
  /-- The recipient the escrow settles to on release. -/
  recipient : CellId
  /-- The locked asset. -/
  asset : AssetId
  /-- The locked amount. -/
  amount : Int

/-- The synthesized authority turn `createEscrowKAsset` checks (`actor` moves `amount` creator⇒recipient). -/
def createEscrowTurn (a : CreateEscrowArgs) : Turn :=
  { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount }

/-- The lifecycle-gated escrow create: the CREATOR must be Live, then run the proved create. -/
def createEscrowStep (k : RecordKernelState) (a : CreateEscrowArgs) : Option RecordKernelState :=
  if acceptsEffects k a.creator then
    createEscrowKAsset k a.id a.actor a.creator a.recipient a.asset a.amount
  else none

/-- Authority extracted from `createEscrowKAsset`'s fail-closed gate. -/
theorem createEscrowStep_authorized (k k' : RecordKernelState) (a : CreateEscrowArgs)
    (h : createEscrowStep k a = some k') : authorizedB k.caps (createEscrowTurn a) = true := by
  unfold createEscrowStep at h
  by_cases hadm : acceptsEffects k a.creator
  · rw [if_pos hadm] at h
    unfold createEscrowKAsset createEscrowTurn at *
    by_cases hg : authorizedB k.caps { actor := a.actor, src := a.creator, dst := a.recipient, amt := a.amount } = true
        ∧ 0 ≤ a.amount ∧ a.amount ≤ k.bal a.creator a.asset ∧ a.creator ∈ k.accounts
        ∧ ¬ (∃ r ∈ k.escrows, r.id = a.id)
    · exact hg.1
    · rw [if_neg hg] at h; exact absurd h (by simp)
  · rw [if_neg hadm] at h; exact absurd h (by simp)

/-- **`createEscrowA` — the registered escrow-create handler.** `conserves` cites the proved
combined-conservation keystone (`delta = 0`); `auth_gated` via `createEscrowStep_authorized`;
`admission_gated` from the creator-Live wrapper. -/
def createEscrowA : EffectHandler CreateEscrowArgs where
  step := createEscrowStep
  delta := fun _ _ => 0           -- debit ledger / park in store ⇒ combined measure fixed
  auth := fun k a => authorizedB k.caps (createEscrowTurn a)
  admission := fun k a => acceptsEffects k a.creator
  trace := createEscrowTurn
  auth_gated := by intro s a s' h; exact createEscrowStep_authorized s s' a h
  admission_gated := by
    intro s a s' h
    unfold createEscrowStep at h
    by_cases hadm : acceptsEffects s a.creator
    · exact hadm
    · rw [if_neg hadm] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold createEscrowStep at h
    by_cases hadm : acceptsEffects s a.creator
    · rw [if_pos hadm] at h
      have := escrow_create_conserves_combined_per_asset (k := s) (k' := s') (id := a.id)
        (actor := a.actor) (creator := a.creator) (recipient := a.recipient)
        (asset := a.asset) (amount := a.amount) b h
      rw [this]; ring
    · rw [if_neg hadm] at h; exact absurd h (by simp)

/-! ## §2 — `releaseEscrowA` / `refundEscrowA`: the R2-closing settle handlers.

The kernel `releaseEscrowKAsset`/`refundEscrowKAsset` take ONLY the id — NO actor authority, so anyone
settles. We WRAP a settle-actor gate: the actor must be authorized over the SETTLEMENT PARTY (the
recipient for release, the creator for refund — `authorizedB`, the same capability gate as transfer).
Because the kernel op already fail-closed-gates the settle-liveness (target ∈ accounts) AND the
record-found, the combined-conservation lemma is UNCONDITIONAL on `op k id = some k'`; our actor wrap
only narrows WHO commits, so we cite the lemma verbatim. `delta = 0`. -/

/-- Find the unresolved escrow record named `id` (the kernel's own `find?` predicate). The settle gates
read the record's parties off THIS lookup, so the gate is a pure function of `(state, id)`. -/
def findUnresolved (k : RecordKernelState) (id : Nat) : Option EscrowRecord :=
  k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false))

/-- Settle arguments: the actor performing the settle + the escrow id. -/
structure SettleArgs where
  /-- The actor performing the settle (authority subject — the R2 fix's load-bearing field). -/
  actor : CellId
  /-- The escrow record id to settle. -/
  id : Nat

/-- **The RELEASE settle-actor gate (R2).** The actor must be authorized over the RECIPIENT (be the
recipient itself, or hold a settling cap over it). If no unresolved record is named, fail-closed. -/
def releaseSettleAuthB (k : RecordKernelState) (a : SettleArgs) : Bool :=
  match findUnresolved k a.id with
  | some r => authorizedB k.caps { actor := a.actor, src := r.recipient, dst := r.recipient, amt := 0 }
  | none => false

/-- **The REFUND settle-actor gate (R2).** The actor must be authorized over the CREATOR (be the creator
itself, or hold a settling cap over it). If no unresolved record is named, fail-closed. -/
def refundSettleAuthB (k : RecordKernelState) (a : SettleArgs) : Bool :=
  match findUnresolved k a.id with
  | some r => authorizedB k.caps { actor := a.actor, src := r.creator, dst := r.creator, amt := 0 }
  | none => false

/-- **The R2-closing RELEASE step.** Commit the kernel release ONLY when the actor is authorized over
the recipient; the bare op (anyone-settles) is otherwise unchanged. -/
def releaseStep (k : RecordKernelState) (a : SettleArgs) : Option RecordKernelState :=
  if releaseSettleAuthB k a then releaseEscrowKAsset k a.id else none

/-- **The R2-closing REFUND step.** Commit the kernel refund ONLY when the actor is authorized over the
creator. -/
def refundStep (k : RecordKernelState) (a : SettleArgs) : Option RecordKernelState :=
  if refundSettleAuthB k a then refundEscrowKAsset k a.id else none

/-- **The settle-liveness admission witness (release).** A committed kernel release required the recipient
to be a live account (`r.recipient ∈ accounts`, the kernel's own fail-closed settle gate) — recovered
here so the handler's `admission` field is genuinely provable, mirroring the conservation-lemma proof's
case split. -/
def releaseAdmitB (k : RecordKernelState) (a : SettleArgs) : Bool :=
  match findUnresolved k a.id with
  | some r => decide (r.recipient ∈ k.accounts)
  | none => false

/-- The settle-liveness admission witness (refund): the creator must be a live account. -/
def refundAdmitB (k : RecordKernelState) (a : SettleArgs) : Bool :=
  match findUnresolved k a.id with
  | some r => decide (r.creator ∈ k.accounts)
  | none => false

/-- **`releaseEscrowA` — the R2-closing release handler.** `auth_gated` BITES: a committed release proves
the actor passed `releaseSettleAuthB` (authorized over the recipient). `conserves` cites the unconditional
`releaseEscrowKAsset_conserves_combined_per_asset` (`delta = 0`). `admission_gated` recovers the kernel's
settle-liveness gate. -/
def releaseEscrowA : EffectHandler SettleArgs where
  step := releaseStep
  delta := fun _ _ => 0
  auth := releaseSettleAuthB
  admission := releaseAdmitB
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold releaseStep at h
    by_cases hg : releaseSettleAuthB s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold releaseStep at h
    by_cases hg : releaseSettleAuthB s a
    · rw [if_pos hg] at h
      -- a committed kernel release ⇒ found an unresolved record with a LIVE recipient.
      show releaseAdmitB s a = true
      unfold releaseEscrowKAsset at h
      unfold releaseAdmitB findUnresolved
      cases hfind : s.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
      | none => rw [hfind] at h; exact absurd h (by simp)
      | some r =>
          rw [hfind] at h; simp only at h
          by_cases hlive : r.recipient ∈ s.accounts ∧ cellLifecycleLive s r.recipient = true
          · exact decide_eq_true hlive.1
          · rw [if_neg hlive] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold releaseStep at h
    by_cases hg : releaseSettleAuthB s a
    · rw [if_pos hg] at h
      have := releaseEscrowKAsset_conserves_combined_per_asset (k := s) (k' := s') (id := a.id) b h
      rw [this]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`refundEscrowA` — the R2-closing refund handler.** Symmetric to `releaseEscrowA`: the actor must be
authorized over the CREATOR (refund target); value returns to the creator, combined measure fixed. -/
def refundEscrowA : EffectHandler SettleArgs where
  step := refundStep
  delta := fun _ _ => 0
  auth := refundSettleAuthB
  admission := refundAdmitB
  trace := fun a => { actor := a.actor, src := a.actor, dst := a.actor, amt := 0 }
  auth_gated := by
    intro s a s' h
    unfold refundStep at h
    by_cases hg : refundSettleAuthB s a
    · exact hg
    · rw [if_neg hg] at h; exact absurd h (by simp)
  admission_gated := by
    intro s a s' h
    unfold refundStep at h
    by_cases hg : refundSettleAuthB s a
    · rw [if_pos hg] at h
      unfold refundEscrowKAsset at h
      show refundAdmitB s a = true
      unfold refundAdmitB findUnresolved
      cases hfind : s.escrows.find? (fun r => decide (r.id = a.id ∧ r.resolved = false)) with
      | none => rw [hfind] at h; exact absurd h (by simp)
      | some r =>
          rw [hfind] at h; simp only at h
          by_cases hlive : r.creator ∈ s.accounts ∧ cellLifecycleLive s r.creator = true
          · exact decide_eq_true hlive.1
          · rw [if_neg hlive] at h; exact absurd h (by simp)
    · rw [if_neg hg] at h; exact absurd h (by simp)
  conserves := by
    intro s a s' h b
    unfold refundStep at h
    by_cases hg : refundSettleAuthB s a
    · rw [if_pos hg] at h
      have := refundEscrowKAsset_conserves_combined_per_asset (k := s) (k' := s') (id := a.id) b h
      rw [this]; ring
    · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — Obligation handlers: ALIASES of escrow create/slash/fulfill.

A dregg OBLIGATION is an escrow with the parties RENAMED: the `obligor` posts collateral (= the escrow
`creator`/refund target), the `beneficiary` is paid out on a breach (= the escrow `recipient`/release
target). The three obligation effects map exactly onto the escrow lifecycle:

  * `createObligationA` = `createEscrowA` (the obligor locks collateral for the beneficiary).
  * `slashObligationA`  = `releaseEscrowA` (on a proven BREACH, the collateral is RELEASED to the
    beneficiary — settle-to-recipient).
  * `fulfillObligationA` = `refundEscrowA` (on FULFILMENT, the collateral is REFUNDED to the obligor —
    settle-to-creator).

The DEADLINE predicate (an obligation breaches only AFTER its deadline; fulfilment must be BEFORE) is the
§8-DEFERRED face — it needs a clock/round oracle the kernel does not carry here, so we register the
EXECUTABLE settle math (authority + conservation) and document the deadline as deferred (see `§DEFER`).
Because these are definitional aliases, they inherit `createEscrowA`/`releaseEscrowA`/`refundEscrowA`'s
discharged obligation proofs for free. -/

/-- **`createObligationA` = `createEscrowA`.** The obligor (`creator`) locks `amount` of collateral for
the beneficiary (`recipient`). Same handler, obligation naming. -/
def createObligationA : EffectHandler CreateEscrowArgs := createEscrowA

/-- **`slashObligationA` = `releaseEscrowA`.** On a proven breach, collateral is RELEASED to the
beneficiary. Actor-gated over the beneficiary (= escrow recipient). Deadline-gate §8-deferred. -/
def slashObligationA : EffectHandler SettleArgs := releaseEscrowA

/-- **`fulfillObligationA` = `refundEscrowA`.** On fulfilment, collateral is REFUNDED to the obligor.
Actor-gated over the obligor (= escrow creator). Deadline-gate §8-deferred. -/
def fulfillObligationA : EffectHandler SettleArgs := refundEscrowA

/-! ## §4 — Note handlers: the double-spend gate + the grow-only commitment insert.

`noteSpendNullifier` inserts a nullifier IF it is not already present (rejecting a double-spend,
`apply.rs:942`); it touches ONLY `nullifiers`, so the combined per-asset measure is UNCHANGED at every
asset (`delta = 0`). `noteCreateCommitment` inserts a FRESH commitment into the grow-only set; a fresh
commitment cannot conflict, so it ALWAYS commits (total, `delta = 0`, self-limiting freshness — the
grow-only dual of the nullifier gate). Both are balance-NEUTRAL: `recTotalAssetWithEscrow` reads
`bal`+`escrows`, never `nullifiers`/`commitments`, so `conserves` is `rfl`-grade. -/

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

/-- `noteSpendNullifier` touches only `nullifiers`, so the bare-ledger and holding-store per-asset
measures are LITERALLY unchanged whenever it commits. -/
theorem noteSpendStep_measure_fixed (k k' : RecordKernelState) (a : NoteSpendArgs)
    (h : noteSpendStep k a = some k') (b : AssetId) :
    recTotalAsset k' b = recTotalAsset k b ∧ escrowHeldAsset k' b = escrowHeldAsset k b := by
  unfold noteSpendStep noteSpendNullifier at h
  by_cases hin : a.nf ∈ k.nullifiers
  · rw [if_pos hin] at h; exact absurd h (by simp)
  · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h
    exact ⟨rfl, rfl⟩

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
    obtain ⟨hbal, hheld⟩ := noteSpendStep_measure_fixed s s' a h b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

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
    obtain ⟨hbal, hheld⟩ := noteCreate_recTotalAsset s a.cm b
    unfold recTotalAssetWithEscrow
    rw [hbal, hheld]; ring

/-! ## §5 — The batch registry: the escrow/obligation/note cluster as coproduct entries.

Each handler is one well-typed `PackedHandler` — the obligation proofs are a TYPING condition on entry.
This list plugs straight into the generic `turn_conserves` from `Dregg2.Exec.Handler` (it is generic over
the registry). -/

/-- The escrow/obligation/note batch registry (the coproduct menu for this cluster). -/
def escrowBatchRegistry : Registry :=
  [ ⟨CreateEscrowArgs, createEscrowA⟩,
    ⟨SettleArgs, releaseEscrowA⟩,
    ⟨SettleArgs, refundEscrowA⟩,
    ⟨NoteSpendArgs, noteSpendA⟩,
    ⟨NoteCreateArgs, noteCreateA⟩ ]

/-- Build a closed escrow-create effect (tag `0`). -/
def createEscrowEffect (id : Nat) (actor creator recipient : CellId) (asset : AssetId) (amount : Int) :
    ClosedEffect :=
  { tag := 0, Args := CreateEscrowArgs,
    args := { id := id, actor := actor, creator := creator, recipient := recipient,
              asset := asset, amount := amount }, handler := createEscrowA }

/-- Build a closed escrow-release effect (tag `1`). -/
def releaseEscrowEffect (actor : CellId) (id : Nat) : ClosedEffect :=
  { tag := 1, Args := SettleArgs, args := { actor := actor, id := id }, handler := releaseEscrowA }

/-- Build a closed escrow-refund effect (tag `2`). -/
def refundEscrowEffect (actor : CellId) (id : Nat) : ClosedEffect :=
  { tag := 2, Args := SettleArgs, args := { actor := actor, id := id }, handler := refundEscrowA }

/-- Build a closed note-spend effect (tag `3`). -/
def noteSpendEffect (actor : CellId) (nf : Nat) : ClosedEffect :=
  { tag := 3, Args := NoteSpendArgs, args := { actor := actor, nf := nf }, handler := noteSpendA }

/-- Build a closed note-create effect (tag `4`). -/
def noteCreateEffect (actor : CellId) (cm : Nat) : ClosedEffect :=
  { tag := 4, Args := NoteCreateArgs, args := { actor := actor, cm := cm }, handler := noteCreateA }

/-! ## §6 — TEETH: the R2 attack, evaluated (`#eval`-verified hole-close).

A fixture with two accounts (0, 1), cell 0 holding 100 of asset 0, with self-authority. Cell 0 creates
an escrow (id 9) locking 40 of asset 0, recipient cell 1. Then: an UNAUTHORIZED actor (5, who owns
nothing and holds no cap) attempting to release/refund is REJECTED; the authorized recipient (release)
and creator (refund) succeed. -/

/-- The base fixture: cells 0,1 accounts; cell 0 holds 100 of asset 0; self-authority; both Live. -/
def es0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun _ => []
    bal := fun c a => if c = 0 ∧ a = 0 then 100 else 0 }

/-- The fixture after cell 0 creates escrow id 9: lock 40 of asset 0, creator 0, recipient 1. -/
def esLocked : Option RecordKernelState :=
  createEscrowStep es0 { id := 9, actor := 0, creator := 0, recipient := 1, asset := 0, amount := 40 }

-- §TEETH-1 (R2 ATTACK): an UNAUTHORIZED actor 5 RELEASING escrow 9 (recipient is 1, not 5) ⇒ REJECTED.
#guard ((esLocked.bind (fun k => execEffect (releaseEscrowEffect 5 9) k)).isSome) == false  --  false
-- §TEETH-2 (R2 ATTACK): an UNAUTHORIZED actor 5 REFUNDING escrow 9 (creator is 0, not 5) ⇒ REJECTED.
#guard ((esLocked.bind (fun k => execEffect (refundEscrowEffect 5 9) k)).isSome) == false  --  false
-- §TEETH-3 (HONEST RELEASE): the recipient (cell 1) releases escrow 9 ⇒ SUCCEEDS (actor-gate passes).
#guard ((esLocked.bind (fun k => execEffect (releaseEscrowEffect 1 9) k)).isSome)  --  true
-- §TEETH-4 (HONEST REFUND): the creator (cell 0) refunds escrow 9 ⇒ SUCCEEDS (actor-gate passes).
#guard ((esLocked.bind (fun k => execEffect (refundEscrowEffect 0 9) k)).isSome)  --  true
-- §TEETH-5 (CONSERVATION): an honest release conserves the combined per-asset measure (lock returns).
#guard ((esLocked.bind (fun k => execEffect (releaseEscrowEffect 1 9) k)).map
        (fun k => (recTotalAssetWithEscrow k 0, recTotalAsset k 0, escrowHeldAsset k 0))) == some (100, 100, 0)  --  some (100, 100, 0)
-- §TEETH-6 (CREATE conserves): create itself fixes the combined measure (ledger 60, held 40, total 100).
#guard (esLocked.map (fun k => (recTotalAssetWithEscrow k 0, recTotalAsset k 0, escrowHeldAsset k 0))) == some (100, 60, 40)  -- some (100, 60, 40)
-- §TEETH-7 (OBLIGATION alias): slash (=release) by the beneficiary 1 SUCCEEDS, by a stranger 5 REJECTED.
#guard ((esLocked.bind (fun k => slashObligationA.step k { actor := 1, id := 9 })).isSome)  --  true
#guard ((esLocked.bind (fun k => slashObligationA.step k { actor := 5, id := 9 })).isSome) == false  --  false
-- §TEETH-8 (NOTE double-spend): a first spend of nullifier 7 succeeds; a replay is REJECTED.
#guard ((execEffect (noteSpendEffect 0 7) es0).isSome)  --  true
#guard (((noteSpendStep es0 { actor := 0, nf := 7 }).bind
        (fun k => noteSpendStep k { actor := 0, nf := 7 })).isSome) == false  --  false
-- §TEETH-9 (NOTE create total): a note-create always commits and is balance-neutral.
#guard ((execEffect (noteCreateEffect 0 42) es0).map (fun k => (k.commitments, recTotalAssetWithEscrow k 0))) == some ([42], 100)  -- some ([42], 100)
-- §TEETH-10 (turn conserves): a turn [create; release-by-recipient] runs the foldlM and conserves.
#guard ((execTurn [createEscrowEffect 9 0 0 1 0 40, releaseEscrowEffect 1 9] es0).map
        (fun k => recTotalAssetWithEscrow k 0)) == some 100  --  some 100

/-! ## §7 — Axiom-hygiene pins (every handler keystone rests only on the three kernel axioms).

Pinning each handler def pins its obligation fields transitively (the literal CARRIES the proofs), and
each settle-actor / conservation helper is pinned directly. A `sorryAx` anywhere fails the pin AND the
build. -/

#assert_axioms createEscrowStep_authorized
#assert_axioms createEscrowA
#assert_axioms releaseEscrowA
#assert_axioms refundEscrowA
#assert_axioms createObligationA
#assert_axioms slashObligationA
#assert_axioms fulfillObligationA
#assert_axioms noteSpendStep_measure_fixed
#assert_axioms noteSpendA
#assert_axioms noteCreateA

/-! ## §DEFER — honest scope of this batch.

Deliberately OUT of this batch (documented, NOT a silent gap):

  * **Obligation DEADLINE gate.** A dregg obligation breaches only AFTER its deadline (slash valid
    post-deadline), and fulfilment must be BEFORE it. That predicate needs a clock/round oracle the
    `RecordKernelState` does not carry here, so `slashObligationA`/`fulfillObligationA` register the
    EXECUTABLE settle math (actor authority + per-asset conservation) and leave the deadline as the §8
    portal face. The settle handlers are a strict prefix of the deadline-gated versions — adding the
    deadline is one more conjunct in the gate, and the conservation proof is unchanged.

  * **`noteSpend` capability authority.** The note-spend gate here is the kernel's double-spend
    nullifier-set check (the real anti-replay invariant); the SPENDING PROOF (a STARK that the spender
    owns the note + correct nullifier derivation) is the §8 `CryptoPortal` face, entering as a portal
    obligation, not a `Bool` capability gate. `auth`/`admission` are default-true here because the gate
    that matters (double-spend) lives in the step and is `#eval`-teeth-verified.

  * **`createEscrowKAsset` recipient-liveness at create.** The create gate checks the CREATOR is live;
    the recipient's liveness is checked at SETTLE time (the kernel's `r.recipient ∈ accounts` gate,
    surfaced here as `releaseAdmitB`). This matches dregg1 (a recipient may be created between lock and
    release).
-/

end Dregg2.Exec.Handlers.Escrow
