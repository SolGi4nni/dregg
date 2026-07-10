/-
# Dregg2.Circuit.FinReactSquare — DEBT-B effect-coverage: `React` closed as a nullifier spend.

`turn/src/executor/apply.rs :: apply_react` (Effect::React) discharges a promise-hole `pending_id` by
presenting a proof of its resolution condition. Its ONLY `RecordKernelState` mutation is a NULLIFIER
SPEND — byte-for-byte the same set-insert `Effect::NoteSpend` performs:

  apply_react (apply.rs:1405+)
    1. `pending_id` well-formed (non-zero)                                       — a guard
    2. `wake.hash() == pending_id.0` (the nullifier↔turn BINDING, apply.rs:1429) — a guard (Pure φ)
    3. `resolve_condition(...) == Resolved` (proof gate; uses a TRANSIENT proof
       ledger + the `reactive_registry` timeout — EXECUTOR-side, NOT kernel)    — off-kernel gate
    4. `note_nullifiers.insert(pending_id, 0)` with double-spend rejection       — THE kernel mutation
       (apply.rs:1518; the SAME set `apply_note_spend` advances, `RecordKernel.lean:966`
        `noteSpendNullifier`)
    5. `journal.record_note_spend(...)` + `reactive_registry.resolve(...)`       — receipt-log +
       EXECUTOR-side registry cleanup, NOT `RecordKernelState`

The `reactive_registry` read/cleanup (`self.reactive_registry.lock()`) is EXECUTOR-side: the Lean
kernel `RecordKernelState` has NO `reactive_registry` field (its fields are `accounts`/`cell`/`caps`/
`nullifiers`/`revoked`/`commitments`/`bal`/…), so it is CORRECTLY not modeled. The wake-hash==pending_id
check (2) is a `Pure` guard — a state-independent binding predicate, exactly like `noteSpendCompose`'s
§8 `spendProof` gate or `grantCapability`'s cross-cell permission φ. The double-spend rejection (4) is
carried INLINE by the covered `insFresh`/`noteSpendStmt` primitive — it is part of the nullifier
mutation, NOT a separate field, so reusing `noteSpendStmt` is the FAITHFUL model (it fail-closes on a
stale `pending_id`, the one-shot tooth apply.rs:1502 witnesses).

So `React`'s kernel step REDUCES to the COVERED noteSpend nullifier-advance under the wake-hash Pure
guard: `reactStmt pendingId φ = seq (guard φ) (noteSpendStmt pendingId)` — the SAME shape as
`NoteSpendCompose.noteSpendComposeStmt`. The whole term is in `FinInterp`'s side-condition-free `Pure`
fragment (`guard`, `insFresh`, `seq`), so its commuting square is `denote_finInterp` directly — no
`FiniteDiff`, no new primitive.

Builds ON committed `FinInterp` + the Argus `noteSpendStmt` cornerstone verbatim; edits NOTHING
committed. Sorry-free. `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Circuit.FinInterp
import Dregg2.Circuit.Argus.Effects.NoteSpend

namespace Dregg2.Circuit.FinReactSquare

open Dregg2.Exec
open Dregg2.Circuit.FinKernelState
open Dregg2.Circuit.FinInterp
open Dregg2.Circuit.Argus
  (RecStmt interp noteSpendStmt interp_noteSpendStmt_eq_noteSpendNullifier)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — `React` as an Argus IR term: the wake-hash Pure guard ∘ the covered noteSpend advance.

`reactKStep` states the kernel-level React step INDEPENDENTLY of the term (so §1's `interp_reactStmt`
is a genuine refinement, not a definitional unfold): on the wake-hash binding φ, run the covered
`noteSpendNullifier` double-spend-rejecting insert; else fail-closed (`none`), exactly apply.rs's
`wake_hash != pending_id` rejection. -/

/-- The kernel-level composed React step (modulo the receipt-log + off-kernel registry cleanup):
the base `noteSpendNullifier` double-spend gate (advancing the SAME `nullifiers` set as noteSpend)
COMPOSED UNDER the wake-hash binding guard φ. On `φ k = false` (wake-hash ≠ pending_id) it fail-closes,
matching apply.rs:1429; the nullifier is NOT advanced. -/
def reactKStep (k : RecordKernelState) (pendingId : Nat) (φ : RecordKernelState → Bool) :
    Option RecordKernelState :=
  if φ k then noteSpendNullifier k pendingId else none

/-- **`reactStmt pendingId φ`** — the React effect as an Argus IR term: the wake-hash binding guard
`guard φ` SEQ the COVERED base `noteSpendStmt pendingId` (= `insFresh (fun _ => pendingId)`, the
non-membership-and-insert of the `nullifiers` set). IDENTICAL in shape to
`NoteSpendCompose.noteSpendComposeStmt` — React's kernel mutation IS a noteSpend nullifier spend,
guarded by the nullifier↔turn binding. -/
def reactStmt (pendingId : Nat) (φ : RecordKernelState → Bool) : RecStmt :=
  RecStmt.seq (RecStmt.guard φ) (noteSpendStmt pendingId)

/-- **`interp_reactStmt_eq_reactKStep` — the cornerstone (executor IS the term, kernel level).**
`interp` of the React term IS the kernel-level composed step `reactKStep` — the wake-hash guard
composed with the base `noteSpendNullifier` non-membership, the SAME partial function apply_react runs
on the kernel. The base term's `interp` (= `noteSpendNullifier`,
`interp_noteSpendStmt_eq_noteSpendNullifier`) is reused VERBATIM under the wake-hash guard. -/
theorem interp_reactStmt_eq_reactKStep (pendingId : Nat) (φ : RecordKernelState → Bool)
    (k : RecordKernelState) :
    interp (reactStmt pendingId φ) k = reactKStep k pendingId φ := by
  simp only [reactStmt, interp, reactKStep]
  by_cases hφ : φ k = true
  · rw [if_pos hφ, if_pos hφ]
    simp only [Option.bind, interp_noteSpendStmt_eq_noteSpendNullifier]
  · rw [if_neg hφ, if_neg hφ]
    simp only [Option.bind]

#assert_axioms interp_reactStmt_eq_reactKStep

/-! ## §2 — THE COMMUTING SQUARE. `reactStmt` is a `Pure` term (`guard`, `insFresh`, `seq` — all in
`FinInterp`'s side-condition-free fragment; `nullifiers` is already-finite `List Nat`, carried
verbatim by `denote`), so its square is `denote_finInterp` directly — the SAME discharge as
`noteSpendComposeStmt_square`, no `FiniteDiff` and no new primitive. -/

/-- **`reactStmt_square` — R1's `hpres` for the React effect term.** The finite operational step
denotes to `interp reactStmt`: `(finInterp (reactStmt pendingId φ) f).map denote = interp (reactStmt
pendingId φ) (denote f)`. Proved by `denote_finInterp` over the `Pure` fragment — React reduces to the
COVERED noteSpend nullifier-advance under a Pure guard, so this is the identical Pure-fragment proof
`noteSpendCompose` uses. -/
theorem reactStmt_square (pendingId : Nat) (φ : RecordKernelState → Bool) (f : FinKernelState) :
    (finInterp (reactStmt pendingId φ) f).map denote = interp (reactStmt pendingId φ) (denote f) := by
  unfold reactStmt noteSpendStmt
  refine denote_finInterp _ ?_ f
  exact ⟨trivial, trivial⟩

#assert_axioms reactStmt_square

/-! ## §3 — TEETH (both polarities). A concrete kernel with an empty nullifier set; React advances
`[] → [pendingId]` when the binding holds, and fail-closes on BOTH a bad binding (guard false) AND a
stale nullifier (double-spend, the one-shot gate). -/

section Teeth

/-- A concrete kernel: live account `0`, EMPTY nullifier set (the React fixture). -/
def kReact : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [], caps := fun _ => [], nullifiers := [] }

/-- The same kernel with `pending_id = 7` ALREADY reacted (nullifier set `[7]`) — the double-spend
fixture (a second React of `7` must fail-closed, the one-shot tooth apply.rs:1502). -/
def kReact7 : RecordKernelState := { kReact with nullifiers := [7] }

-- React is two-gated, three-way non-vacuous on the nullifier set:
-- a valid binding on a fresh pending_id COMMITS and advances `[] → [7]`;
-- a bad binding (wake-hash ≠ pending_id) is REJECTED; a stale pending_id is REJECTED (one-shot).
#guard ((interp (reactStmt 7 (fun _ => true)) kReact).isSome)                                 -- bind ∧ fresh ⇒ commit
#guard (((interp (reactStmt 7 (fun _ => true)) kReact).map (fun k => k.nullifiers)) == some [7]) -- advances
#guard ((interp (reactStmt 7 (fun _ => false)) kReact).isNone)                                -- bad binding ⇒ reject
#guard ((interp (reactStmt 7 (fun _ => true)) kReact7).isNone)                                -- stale ⇒ reject (one-shot)
-- the finite interpreter agrees (the square's LHS is real, not vacuous):
#guard (((finInterp (reactStmt 7 (fun _ => true)) finInit).map (fun f => f.nullifiers)) == some [7])
#guard ((finInterp (reactStmt 7 (fun _ => false)) finInit).isNone)

/-- **POSITIVE tooth — React ADVANCES the nullifier set `[] → [pendingId]`.** On the fresh fixture with
a valid wake-hash binding, React commits and the spent-note set grows from `[]` to `[7]` (the same
insert noteSpend performs): the nullifier advance is a real, observable mutation. -/
theorem reactStmt_advances :
    (interp (reactStmt 7 (fun _ => true)) kReact).map (fun k => k.nullifiers) = some [7] := by
  rw [interp_reactStmt_eq_reactKStep]; decide

/-- **POSITIVE tooth (fin side) — the SQUARE fires concretely.** Transporting through `reactStmt_square`
(the finite step's denotation), the nullifier set advances `[] → [7]`: the finite operational step
denotes exactly to the executor's nullifier advance. -/
theorem reactStmt_square_advances :
    ((finInterp (reactStmt 7 (fun _ => true)) finInit).map denote).map (fun k => k.nullifiers)
      = some [7] := by
  rw [reactStmt_square, interp_reactStmt_eq_reactKStep]; decide

/-- **NEGATIVE tooth (bad binding) — the wake-hash guard BITES.** When `wake.hash() ≠ pending_id`
(the binding guard is false), React fail-closes (`= none`) and the nullifier is NOT advanced — exactly
apply.rs:1429's nullifier↔turn-binding rejection. Two-valued: not `:= True`. -/
theorem reactStmt_rejects_bad_binding :
    interp (reactStmt 7 (fun _ => false)) kReact = none := by
  rw [interp_reactStmt_eq_reactKStep]; decide

/-- **NEGATIVE tooth (double-spend) — the one-shot gate BITES.** A second React of an ALREADY-reacted
`pending_id` (`7 ∈ nullifiers`) with a VALID binding still fail-closes (`= none`): the base noteSpend
double-spend rejection SURVIVES inside React (apply.rs:1502 "already reacted (one-shot)"). The covered
nullifier-advance's teeth are React's teeth. -/
theorem reactStmt_rejects_double_react :
    interp (reactStmt 7 (fun _ => true)) kReact7 = none := by
  rw [interp_reactStmt_eq_reactKStep]; decide

#assert_axioms reactStmt_advances
#assert_axioms reactStmt_square_advances
#assert_axioms reactStmt_rejects_bad_binding
#assert_axioms reactStmt_rejects_double_react

end Teeth

end Dregg2.Circuit.FinReactSquare
