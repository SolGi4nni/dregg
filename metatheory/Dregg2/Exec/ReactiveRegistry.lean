/-
# Dregg2.Exec.ReactiveRegistry — the reactive subsystem with a dedicated React replay domain.

DEBT-B classified the 33 deployed effects. `Promise`/`Notify` (`turn/src/executor/apply.rs`
`apply_promise :1315`, `apply_notify :1349`) mutate `self.reactive_registry.lock()` — an EXECUTOR-side
structure that is NOT a `RecordKernelState` field. So they have NO finite-map kernel commuting square,
correctly, and were named an honest OFF-KERNEL boundary. This module models the registry itself, so the
boundary becomes a PROVED subsystem:

  * The registry is modeled faithfully after `turn/src/reactive.rs` +
    `turn/src/pending.rs::PendingTurnRegistry` (a map keyed by the hole id, whose entry mirrors
    `PendingEntry { turn, condition, dependents, submitted_at, timeout_height }`; the id IS the wake-turn
    hash, `reactive.rs:217`).
  * `promiseStep`/`notifyStep` mirror `apply_promise`/`apply_notify`: a Pure actor guard, then a registry
    deposit, with the kernel component passed through VERBATIM. `promise_kernel_unchanged` /
    `notify_kernel_unchanged` turn the OFF-KERNEL claim into a THEOREM (the committed `RecordKernelState`
    is literally `= k`).
  * `reactStep` mirrors deployed `apply_react` after commit `64477cd9c`: its kernel leg is unchanged;
    its registry leg removes the resolved hole; and its one-shot leg inserts `pending_id` into a
    DEDICATED `ReactiveNullifierSet`. THE KEYSTONE `react_one_shot`/`no_double_react` proves no two
    `React`s on the same hole id both succeed without contaminating the faithful note-spend/FNSP
    nullifier sequence.

## HONEST SCOPE — deployed behaviour left off-kernel (named, not faked)
  * The proof/temporal gate `resolve_condition` (proof validity + timeout via a TRANSIENT proof ledger
    and `self.block_height`) is EXECUTOR-side — NOT `RecordKernelState`. It is abstracted by the Pure
    binding guard `φ`; the proof-validity/expiry check is not re-modeled here.
  * `expire` (`pending.rs::check_timeouts`) removes past-timeout holes; its `currentHeight` is an OFF-KERNEL
    block-height input, and a timed-out hole is DROPPED from the registry WITHOUT any nullifier spend — so
    it is correctly registry-only (kernel-neutral). Modeled structurally, height named off-kernel.
  * Cascading resolution + broken-promise propagation (`PendingEntry.dependents`, `ResolutionEvent`,
    synthetic receipts) are registry EVENT / receipt-log machinery with no kernel effect; `resolve` models
    only the entry REMOVAL (the one-shot registry tooth). The event/cascade emission is not modeled.

`FinReactSquare` is intentionally NOT consumed here: it models the superseded shared-note-nullifier
design. Sorry-free. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Exec.RecordKernel

namespace Dregg2.Exec.Reactive

open Dregg2.Exec

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — The registry model, mirrored from `turn/src/reactive.rs` + `turn/src/pending.rs`. -/

/-- **`ResolutionCondition`** — faithful mirror of `pending.rs::ResolutionCondition` (`pending.rs:57`),
the three conditions a promise-hole may await. `awaitCondition` carries the `ProofCondition` as an opaque
tag: its crypto/proof discharge is the OFF-KERNEL `resolve_condition` gate (see the module scope note),
not modeled here. -/
inductive ResolutionCondition where
  /-- `AwaitReceipt { turn_hash, federation_id }` — awaiting a (possibly remote) turn receipt. -/
  | awaitReceipt   (turnHash : Nat) (federationId : Option Nat)
  /-- `AwaitCondition(ProofCondition)` — awaiting a proof discharge (the tag; crypto is off-kernel). -/
  | awaitCondition (proofTag : Nat)
  /-- `AwaitHeight(u64)` — awaiting a block height. -/
  | awaitHeight    (height : Nat)
  deriving DecidableEq, Repr

/-- **`HoleEntry`** — one promise-hole, mirroring `pending.rs::PendingEntry` (`pending.rs:43`). The hole
`id` IS the wake-turn hash (`reactive.rs:217`, `notify` returns `wake.hash()`), so we carry `wake` as that
content hash and key the registry by it. `dependents` mirrors the cascade list (defaults empty, exactly as
`submit_pending_at` leaves it). `submittedAt`/`timeoutHeight` are the deposit's block-height bookkeeping. -/
structure HoleEntry where
  /-- The wake turn's content hash — the hole id (`reactive.rs:217`). -/
  wake          : Nat
  /-- The condition the recipient discharges to react (`PendingEntry.condition`). -/
  condition     : ResolutionCondition
  /-- Block height at which the hole times out (`PendingEntry.timeout_height`). -/
  timeoutHeight : Nat
  /-- Block height at which the hole was deposited (`PendingEntry.submitted_at`). -/
  submittedAt   : Nat
  /-- Turns waiting on THIS hole (`PendingEntry.dependents`); cascade is off-kernel event machinery. -/
  dependents    : List Nat := []
  deriving DecidableEq, Repr

/-- **`ReactiveRegistry`** — the reactive registry as an association list keyed by hole id, mirroring
`pending.rs::PendingTurnRegistry`'s `pending : HashMap<[u8;32], PendingEntry>` (`pending.rs:167`).
`lookup` is first-match, so a `deposit` (list-cons) shadows an older entry exactly as a `HashMap::insert`
overwrites. -/
abbrev ReactiveRegistry := List (Nat × HoleEntry)

/-- **`deposit`** — `PendingTurnRegistry::submit_pending_at` (`pending.rs:202`): insert the hole keyed by
its wake hash (its id). The kernel-backed `NotifyEdge` deposit. -/
def ReactiveRegistry.deposit (reg : ReactiveRegistry) (e : HoleEntry) : ReactiveRegistry :=
  (e.wake, e) :: reg

/-- **`lookup`** — `PendingTurnRegistry::get_pending` (`pending.rs:327`): first-match by id. -/
def ReactiveRegistry.lookup (reg : ReactiveRegistry) (id : Nat) : Option HoleEntry :=
  (reg.find? (fun p => p.1 == id)).map (·.2)

/-- **`resolve`** — `PendingTurnRegistry::resolve`'s `pending.remove(&turn_hash)` (`pending.rs:246`): the
hole is CONSUMED (removed). This is `reactive.rs`'s registry-removal one-shot tooth — a redundant second
tooth beside the load-bearing nullifier gate (`apply.rs:1536`). The cascade/event emission is off-kernel
receipt-log machinery, not modeled. -/
def ReactiveRegistry.resolve (reg : ReactiveRegistry) (id : Nat) : ReactiveRegistry :=
  reg.filter (fun p => p.1 != id)

/-- **`expire`** — `PendingTurnRegistry::check_timeouts` (`pending.rs:309`): drop holes past their timeout.
`currentHeight` is an OFF-KERNEL block-height input; a timed-out hole is removed from the registry WITHOUT
any nullifier spend (kernel-neutral) — so expiry cannot spend a hole (it can only forget it). -/
def ReactiveRegistry.expire (reg : ReactiveRegistry) (currentHeight : Nat) : ReactiveRegistry :=
  reg.filter (fun p => decide (currentHeight ≤ p.2.timeoutHeight))

/-! ## §2 — `promiseStep` / `notifyStep`: the OFF-KERNEL fact becomes a THEOREM.

Both mirror the deployed handlers: a Pure actor guard, then a registry `deposit`, with the kernel
component `k` threaded UNCHANGED. `promise_kernel_unchanged`/`notify_kernel_unchanged` prove that
committed step's `RecordKernelState` is literally `= k` — the honest OFF-KERNEL boundary, now a theorem. -/

/-- **`promiseStep`** — `apply_promise` (`apply.rs:1315`): guard `cell == actor` (a cell makes its OWN
standing commitments), then deposit the hole. The kernel `k` is passed through verbatim. -/
def promiseStep (k : RecordKernelState) (reg : ReactiveRegistry)
    (cell actor : CellId) (e : HoleEntry) : Option (RecordKernelState × ReactiveRegistry) :=
  if cell = actor then some (k, reg.deposit e) else none

/-- **`notifyStep`** — `apply_notify` (`apply.rs:1349`): guard `from == actor` (no spoofed provenance)
AND `wake.agent == to` (the deposited wake is the recipient's to discharge), then deposit. Kernel `k`
passed through verbatim. -/
def notifyStep (k : RecordKernelState) (reg : ReactiveRegistry)
    (from_ actor to_ wakeAgent : CellId) (e : HoleEntry) :
    Option (RecordKernelState × ReactiveRegistry) :=
  if from_ = actor ∧ wakeAgent = to_ then some (k, reg.deposit e) else none

/-- **`promise_kernel_unchanged` — the OFF-KERNEL claim, now a THEOREM.** A committed `Promise` step
leaves the kernel component EXACTLY `k`: `Promise` touches only the executor-side registry, never
`RecordKernelState`. (The prompt's `(promiseStep …).1 = k`, in fail-closed committed form.) -/
theorem promise_kernel_unchanged {k k' : RecordKernelState} {reg reg' : ReactiveRegistry}
    {cell actor : CellId} {e : HoleEntry}
    (h : promiseStep k reg cell actor e = some (k', reg')) : k' = k := by
  unfold promiseStep at h
  by_cases hc : cell = actor
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`notify_kernel_unchanged` — the OFF-KERNEL claim, now a THEOREM.** A committed `Notify` step leaves
the kernel component EXACTLY `k`: `Notify` deposits into the recipient's registry only. -/
theorem notify_kernel_unchanged {k k' : RecordKernelState} {reg reg' : ReactiveRegistry}
    {from_ actor to_ wakeAgent : CellId} {e : HoleEntry}
    (h : notifyStep k reg from_ actor to_ wakeAgent e = some (k', reg')) : k' = k := by
  unfold notifyStep at h
  by_cases hc : from_ = actor ∧ wakeAgent = to_
  · rw [if_pos hc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.1.symm
  · rw [if_neg hc] at h; exact absurd h (by simp)

/-! ## §3 — `reactStep`: separate registry, React replay set, and faithful note kernel. -/

/-- The abstract set image of Rust's canonical `pending::ReactiveNullifierSet`. Rust persists a sorted
`BTreeSet<Nullifier>` and domain-separates its CAS digest under `dregg-reactive-nullifiers-v1`; this
model keeps precisely the set semantics needed for insertion and replay rejection. -/
abbrev ReactiveNullifierSet := Finset Nat

/-- **`reactStep`** — the deployed combined transition after `64477cd9c`. A valid binding/proof guard
spends `pendingId` in the dedicated React replay set and resolves the registry entry. The faithful
`RecordKernelState` is threaded unchanged. A bad guard or repeated React fails closed. -/
def reactStep (k : RecordKernelState) (reg : ReactiveRegistry) (spent : ReactiveNullifierSet)
    (pendingId : Nat) (φ : RecordKernelState → Bool) :
    Option (RecordKernelState × ReactiveRegistry × ReactiveNullifierSet) :=
  if φ k then
    if pendingId ∈ spent then none
    else some (k, reg.resolve pendingId, insert pendingId spent)
  else none

/-- **`reactStep_kernel_unchanged`.** A committed React does not mutate the faithful note kernel. -/
theorem reactStep_kernel_unchanged {k k1 : RecordKernelState} {reg reg1 : ReactiveRegistry}
    {spent spent1 : ReactiveNullifierSet} {id : Nat} {φ : RecordKernelState → Bool}
    (h : reactStep k reg spent id φ = some (k1, reg1, spent1)) : k1 = k := by
  unfold reactStep at h
  by_cases hφ : φ k = true
  · rw [if_pos hφ] at h
    by_cases hmem : id ∈ spent
    · rw [if_pos hmem] at h; simp at h
    · rw [if_neg hmem] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact h.1.symm
  · rw [if_neg hφ] at h; simp at h

/-- In particular, React cannot append to or otherwise change the faithful FNSP note-nullifier image. -/
theorem reactStep_note_nullifiers_unchanged {k k1 : RecordKernelState}
    {reg reg1 : ReactiveRegistry} {spent spent1 : ReactiveNullifierSet}
    {id : Nat} {φ : RecordKernelState → Bool}
    (h : reactStep k reg spent id φ = some (k1, reg1, spent1)) :
    k1.nullifiers = k.nullifiers := by
  rw [reactStep_kernel_unchanged h]

/-- **`reactStep_inserts`.** A committed React records the hole id in the dedicated React replay set. -/
theorem reactStep_inserts {k k1 : RecordKernelState} {reg reg1 : ReactiveRegistry}
    {spent spent1 : ReactiveNullifierSet} {id : Nat} {φ : RecordKernelState → Bool}
    (h : reactStep k reg spent id φ = some (k1, reg1, spent1)) : id ∈ spent1 := by
  unfold reactStep at h
  by_cases hφ : φ k = true
  · rw [if_pos hφ] at h
    by_cases hmem : id ∈ spent
    · rw [if_pos hmem] at h; simp at h
    · rw [if_neg hmem] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, hspent⟩ := h
      rw [← hspent]
      simp
  · rw [if_neg hφ] at h; simp at h

/-- **`reactStep_rejects_spent` (the one-shot gate BITES).** A repeated React fails closed because the
id is already in the dedicated replay set. Membership in the note-spend set is irrelevant. -/
theorem reactStep_rejects_spent {k : RecordKernelState} {reg : ReactiveRegistry}
    {spent : ReactiveNullifierSet} {id : Nat} {φ : RecordKernelState → Bool}
    (hmem : id ∈ spent) : reactStep k reg spent id φ = none := by
  simp [reactStep, hmem]

/-- **THE KEYSTONE — `react_one_shot`.** Once a React succeeds, every later React on the same id
fails, using only the dedicated replay domain. -/
theorem react_one_shot {k k1 : RecordKernelState} {reg reg1 : ReactiveRegistry}
    {spent spent1 : ReactiveNullifierSet} {id : Nat}
    {φ φ' : RecordKernelState → Bool}
    (h1 : reactStep k reg spent id φ = some (k1, reg1, spent1)) :
    reactStep k1 reg1 spent1 id φ' = none :=
  reactStep_rejects_spent (reactStep_inserts h1)

/-- **`no_double_react` — the keystone as an impossibility.** No two Reacts on one hole both succeed. -/
theorem no_double_react {k k1 k2 : RecordKernelState} {reg reg1 reg2 : ReactiveRegistry}
    {spent spent1 spent2 : ReactiveNullifierSet} {id : Nat}
    {φ φ' : RecordKernelState → Bool}
    (h1 : reactStep k reg spent id φ = some (k1, reg1, spent1)) :
    reactStep k1 reg1 spent1 id φ' ≠ some (k2, reg2, spent2) := by
  rw [react_one_shot h1]; simp

#assert_axioms promise_kernel_unchanged
#assert_axioms notify_kernel_unchanged
#assert_axioms reactStep_kernel_unchanged
#assert_axioms reactStep_note_nullifiers_unchanged
#assert_axioms react_one_shot
#assert_axioms no_double_react

/-! ## §4 — TEETH (both polarities). Concrete fixtures: a first React on a fresh hole FIRES; a second on
the same hole BITES; a promise deposit/lookup/resolve round-trips. -/

section Teeth

/-- A concrete kernel: live account `0`, EMPTY nullifier set. -/
def k0 : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [], caps := fun _ => [], nullifiers := [] }

/-- A kernel whose faithful NOTE-SPEND domain already contains raw id `7`. This must not block React. -/
def kNote7 : RecordKernelState := { k0 with nullifiers := [7] }

/-- Empty and already-spent fixtures for the dedicated React replay domain. -/
def spent0 : ReactiveNullifierSet := ∅
def spent7 : ReactiveNullifierSet := {7}

/-- The empty registry. -/
def reg0 : ReactiveRegistry := []

/-- A promise-hole for wake `7`, awaiting height `100`. -/
def hole7 : HoleEntry :=
  { wake := 7, condition := ResolutionCondition.awaitHeight 100, timeoutHeight := 100, submittedAt := 10 }

-- Registry round-trip: a deposited hole is LOOKED UP; after resolve it is GONE; expiry drops it past timeout.
#guard ((reg0.deposit hole7).lookup 7).isSome                       -- deposit ⇒ live
#guard (((reg0.deposit hole7).resolve 7).lookup 7).isNone           -- resolve ⇒ consumed (one-shot removal)
#guard (((reg0.deposit hole7).expire 101).lookup 7).isNone          -- expire past timeout ⇒ dropped (no spend)
#guard (((reg0.deposit hole7).expire 50).lookup 7).isSome           -- expire before timeout ⇒ survives

-- React teeth on the combined state:
#guard (reactStep k0 reg0 spent0 7 (fun _ => true)).isSome          -- fresh + valid binding ⇒ FIRES
#guard ((reactStep k0 reg0 spent0 7 (fun _ => true)).map (fun p => p.1.nullifiers)) == some []
#guard ((reactStep k0 reg0 spent0 7 (fun _ => true)).map (fun p => decide (7 ∈ p.2.2))) == some true
#guard (reactStep k0 reg0 spent0 7 (fun _ => false)).isNone         -- bad binding ⇒ REJECT
#guard (reactStep k0 reg0 spent7 7 (fun _ => true)).isNone          -- React replay ⇒ REJECT
#guard (reactStep kNote7 reg0 spent0 7 (fun _ => true)).isSome      -- same raw NOTE id grants no block

/-- **POSITIVE tooth — a first React FIRES in the dedicated domain while note nullifiers stay empty.** -/
theorem react_first_fires :
    (reactStep k0 reg0 spent0 7 (fun _ => true)).map
      (fun p => (p.1.nullifiers, decide (7 ∈ p.2.2))) = some ([], true) := by
  rfl

/-- **DOMAIN-SEPARATION tooth.** An equal raw id in the faithful note-spend set neither spends nor
blocks the React id; only `spent7` has React authority. -/
theorem note_spend_id_does_not_block_react :
    (reactStep kNote7 reg0 spent0 7 (fun _ => true)).isSome := by
  decide

/-- **NEGATIVE tooth (bad binding) — the wake-hash guard BITES.** A React whose binding guard is false
(`wake.hash() ≠ pending_id`) fail-closes; the registry is untouched. -/
theorem react_rejects_bad_binding : reactStep k0 reg0 spent0 7 (fun _ => false) = none := by
  rfl

/-- **NEGATIVE tooth (double-react) — the one-shot gate BITES.** A second React on an ALREADY-reacted
hole (`7 ∈ spent7`) fail-closes even with a valid binding. -/
theorem react_second_rejected : reactStep k0 reg0 spent7 7 (fun _ => true) = none :=
  reactStep_rejects_spent (by decide)

/-- **The keystone FIRES end-to-end on the fixtures.** The first React on `7` succeeds, and THEN a second
React on `7` (any guard) is refused — no two Reacts on the same hole both succeed. -/
theorem react_one_shot_fires :
    ∀ k1 reg1 spent1,
      reactStep k0 reg0 spent0 7 (fun _ => true) = some (k1, reg1, spent1) →
      reactStep k1 reg1 spent1 7 (fun _ => true) = none :=
  fun _ _ _ h => react_one_shot h

end Teeth

end Dregg2.Exec.Reactive
