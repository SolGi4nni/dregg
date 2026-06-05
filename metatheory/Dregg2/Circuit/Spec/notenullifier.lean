/-
# Dregg2.Circuit.Spec.notenullifier — INDEPENDENT full-state spec + executor⟺spec for the
`note-nullifier` effect family (variant `noteSpendA`).

This module is the `note-nullifier` corner of the spec⟺executor discipline that
`Dregg2.Circuit.Transfer` (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) established
for the conservative `Transfer` effect, transposed exactly as `cellstatelog` transposed it onto the
observation log. Where `Transfer` moves the conserved `balance` measure across two cells, the
`note-nullifier` family GROWS the spent-note nullifier SET — the anti-replay / double-spend gate.

## The effect (the executor's `noteSpendA` arm, `TurnExecutorFull.lean:3538`)

    | .noteSpendA nf actor              => noteSpendChainA s nf actor

where (`TurnExecutorFull.lean:2012`)

    noteSpendChainA s nf actor :=
      match noteSpendNullifier s.kernel nf with
      | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log }
      | none    => none

and (`RecordKernel.lean:1265`)

    noteSpendNullifier k nf :=
      if nf ∈ k.nullifiers then none
      else some { k with nullifiers := nf :: k.nullifiers }

So a committed `noteSpendA`:

  * **GUARD** — `nf ∉ s.kernel.nullifiers` (the DOUBLE-SPEND rejection / anti-replay gate;
    dregg1 `apply_note_spend` fails-closed "double-spend: nullifier already in note_nullifiers set",
    `apply.rs:945`). There is **NO authority gate** on the spend at the ledger layer — the §8 STARK
    spending proof + nullifier derivation is the THEOREM-level portal, carried elsewhere; the
    ledger-side gate this arm enforces is the set membership.
  * **TOUCHED components** — TWO. (1) the nullifier SET `kernel.nullifiers`: `nf` is consed onto the
    front (`nf :: nullifiers`). (2) the receipt chain `log`: a single self-`Turn` row
    `escrowReceiptA actor = { actor, src := actor, dst := actor, amt := 0 }` is prepended.
  * **FRAME** — every OTHER `RecordKernelState` field is LITERALLY unchanged: the 16 non-`nullifiers`
    kernel fields (`accounts cell caps escrows revoked commitments bal queues swiss slotCaveats
    factories lifecycle deathCert delegate delegations sealedBoxes`).

## What this module proves (the Transfer pattern, transposed onto the nullifier domain)

  1. `NoteSpendSpec st nf actor st'` — the INDEPENDENT declarative full-state post-state: the guard
     ∧ the EXACT nullifier-set post-state ∧ the EXACT log post-state ∧ EVERY one of the 16 OTHER
     kernel fields unchanged (the FRAME). No frame clause names `execFullA`/`noteSpendChainA`/
     `noteSpendNullifier`.
  2. `execFullA_noteSpend_iff_spec` — `execFullA st (.noteSpendA …) = some st' ↔ NoteSpendSpec …`,
     BOTH directions. The `→` VALIDATES the executor against the independent spec: all 17 kernel
     fields + the log are checked, so had the executor silently mutated ANY OTHER kernel field the
     frame clause would make this proof FAIL.
  3. `noteSpendChainA_correct` — the post-state helper `noteSpendChainA` validated DECLARATIVELY (its
     nullifier-set growth, its log row, and its kernel-frame), the `recTransfer_correct` analog for
     this family.
  4. `#assert_axioms` on every theorem (whitelist `{propext, Classical.choice, Quot.sound}`).

No `sorry`/`admit`/`axiom`/`native_decide`.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.NoteNullifier

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (double-spend rejection; NO authority gate).

The ENTIRE guard `execFullA`'s `noteSpendA` arm enforces at the ledger layer before committing: the
nullifier has NOT already been spent. Unlike `Transfer.admitGuard` (a six-way conjunction with
authority/non-negativity/availability/…), `noteSpendGuard` is the single anti-replay conjunct —
the §8 STARK spending proof is the theorem-layer portal, not a ledger gate. Stated INDEPENDENTLY of
the executor. -/
def noteSpendGuard (st : RecChainedState) (nf : Nat) : Prop :=
  nf ∉ st.kernel.nullifiers

/-! ## §2 — the receipt the executor appends (the touched log post-image).

The exact `Turn` row a committed note-spend prepends to the log: a self-receipt on `actor` with zero
amount (note effects move SETS, never balance, so `amt = 0`). Re-exported from `escrowReceiptA` so
the spec's log clause is the genuine executor receipt; pinned declaratively in
`noteSpendChainA_correct` below. -/
abbrev noteSpendReceipt (actor : CellId) : Turn := escrowReceiptA actor

/-! ## §3 — kernel extensionality from the 17 field equalities.

A helper turning the spec's 16 frame equalities + the new nullifier-set value back into a single
`RecordKernelState` equality (so the `←` reconstruction can rebuild the kernel record). Stated/proved
by destructuring both records — structure eta is what makes "17 fields equal ⇒ records equal" a `rfl`
after the substitutions. (The `nullifiers` field is supplied its post-spend value, not the pre-value
— this is the one TOUCHED kernel field.) -/
theorem recKernel_ext {k k' : RecordKernelState}
    (h1 : k'.accounts = k.accounts) (h2 : k'.cell = k.cell) (h3 : k'.caps = k.caps)
    (h4 : k'.escrows = k.escrows) (h5 : k'.nullifiers = k.nullifiers) (h6 : k'.revoked = k.revoked)
    (h7 : k'.commitments = k.commitments) (h8 : k'.bal = k.bal) (h9 : k'.queues = k.queues)
    (h10 : k'.swiss = k.swiss) (h11 : k'.slotCaveats = k.slotCaveats)
    (h12 : k'.factories = k.factories) (h13 : k'.lifecycle = k.lifecycle)
    (h14 : k'.deathCert = k.deathCert) (h15 : k'.delegate = k.delegate)
    (h16 : k'.delegations = k.delegations) (h17 : k'.sealedBoxes = k.sealedBoxes) :
    k' = k := by
  cases k; cases k'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
  rfl

/-! ## §4 — `noteSpendChainA_correct` — the post-state helper validated DECLARATIVELY.

The `recTransfer_correct` analog: rather than blindly trusting `noteSpendChainA`, we PIN what a
committed run does — its nullifier set grows by exactly `nf` (head-consed), its log grows by exactly
the receipt (head-consed), and every OTHER kernel field is literally unchanged. So the spec's
nullifier-set + log + frame clauses genuinely encode the helper's behaviour. Only stated for the
committed (`nf ∉ nullifiers`) case, since that is the post-state the spec characterizes. -/
theorem noteSpendChainA_correct (st : RecChainedState) (nf : Nat) (actor : CellId)
    (hfresh : nf ∉ st.kernel.nullifiers) :
    ∃ st', noteSpendChainA st nf actor = some st'
      ∧ st'.kernel.nullifiers = nf :: st.kernel.nullifiers
      ∧ st'.log = noteSpendReceipt actor :: st.log
      ∧ st'.kernel.accounts = st.kernel.accounts
      ∧ st'.kernel.cell = st.kernel.cell
      ∧ st'.kernel.caps = st.kernel.caps
      ∧ st'.kernel.escrows = st.kernel.escrows
      ∧ st'.kernel.revoked = st.kernel.revoked
      ∧ st'.kernel.commitments = st.kernel.commitments
      ∧ st'.kernel.bal = st.kernel.bal
      ∧ st'.kernel.queues = st.kernel.queues
      ∧ st'.kernel.swiss = st.kernel.swiss
      ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
      ∧ st'.kernel.factories = st.kernel.factories
      ∧ st'.kernel.lifecycle = st.kernel.lifecycle
      ∧ st'.kernel.deathCert = st.kernel.deathCert
      ∧ st'.kernel.delegate = st.kernel.delegate
      ∧ st'.kernel.delegations = st.kernel.delegations
      ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes := by
  refine ⟨{ kernel := { st.kernel with nullifiers := nf :: st.kernel.nullifiers },
            log := noteSpendReceipt actor :: st.log }, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [noteSpendChainA, noteSpendNullifier, noteSpendReceipt, if_neg hfresh]
  all_goals rfl

/-! ## §5 — the FULL-STATE declarative spec of a committed `noteSpendA` (the INDEPENDENT reference).

`NoteSpendSpec` is the WHOLE truth of a committed note-spend, written INDEPENDENTLY of the executor
(no `execFullA`/`noteSpendChainA`/`noteSpendNullifier` term in any clause): the guard holds; the
post-state's `nullifiers` is exactly `nf` consed onto the old set; the post-state's `log` is exactly
the receipt consed onto the old log (the TWO TOUCHED components); and EVERY one of the 16 OTHER
`RecordKernelState` components is LITERALLY unchanged (the FRAME — missing any one reintroduces a
ghost). -/
def NoteSpendSpec (st : RecChainedState) (nf : Nat) (actor : CellId)
    (st' : RecChainedState) : Prop :=
  noteSpendGuard st nf
  -- the TOUCHED component #1: the nullifier set grows by exactly `nf` (head-consed).
  ∧ st'.kernel.nullifiers = nf :: st.kernel.nullifiers
  -- the TOUCHED component #2: the receipt chain grows by exactly the note-spend receipt.
  ∧ st'.log = noteSpendReceipt actor :: st.log
  -- the FRAME: all 16 OTHER kernel fields LITERALLY unchanged.
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.escrows = st.kernel.escrows
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.queues = st.kernel.queues
  ∧ st'.kernel.swiss = st.kernel.swiss
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-! ## §6 — `execFullA_noteSpend_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions). -/

/-- **`execFullA_noteSpend_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full
record executor commits a `noteSpendA` into `st'` IFF `st'` is EXACTLY the spec'd full post-state.

The `→` direction VALIDATES `execFullA` against the independent spec: ALL 17 kernel fields AND the
log are checked, so had the executor silently mutated `bal`/`caps`/`escrows`/any OTHER kernel field,
the corresponding frame clause would make this proof FAIL. The `←` reconstructs the committed state
from the spec. This is the executor corner of the `note-nullifier` spec⟺executor square. -/
theorem execFullA_noteSpend_iff_spec (st : RecChainedState) (nf : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.noteSpendA nf actor) = some st'
      ↔ NoteSpendSpec st nf actor st' := by
  unfold execFullA NoteSpendSpec noteSpendGuard
  -- collapse the executor arm to the `noteSpendNullifier` membership test.
  simp only [noteSpendChainA, noteSpendNullifier, noteSpendReceipt]
  by_cases hfresh : nf ∈ st.kernel.nullifiers
  · -- DOUBLE-SPEND: the guard fails, the executor returns `none`, the spec is unsatisfiable.
    rw [if_pos hfresh]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg, _⟩; exact absurd hfresh hg
  · -- FRESH nullifier: the executor commits; validate it against the full spec, both ways.
    rw [if_neg hfresh]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      -- the committed post-state is `{ kernel := { st.kernel with nullifiers := nf :: … },
      --   log := escrowReceiptA actor :: st.log }`; read every component off it.
      exact ⟨hfresh, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · rintro ⟨_, hnull, hlog, h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
        h17⟩
      -- rebuild `st'` from the nullifier post-image + log post-image + the 16 frame equalities.
      have hk : st'.kernel = { st.kernel with nullifiers := nf :: st.kernel.nullifiers } := by
        apply recKernel_ext
        · simpa using h1
        · simpa using h2
        · simpa using h3
        · simpa using h4
        · simpa using hnull
        · simpa using h6
        · simpa using h7
        · simpa using h8
        · simpa using h9
        · simpa using h10
        · simpa using h11
        · simpa using h12
        · simpa using h13
        · simpa using h14
        · simpa using h15
        · simpa using h16
        · simpa using h17
      cases st' with
      | mk k' lg' =>
        simp only at hk hlog
        subst hk hlog
        rfl

/-! ## §7 — corollaries: the domain facts a committed note-spend produces (executor side).

Convenience projections of `execFullA_noteSpend_iff_spec` for downstream callers: a committed spend
GROWS the nullifier set by exactly `nf`, GROWS the log by exactly the receipt, and FRAMES every OTHER
kernel field. These are the `note-nullifier` analogs of `recKExec_src_debit`/`recKExec_dst_credit`. -/

/-- A committed `noteSpendA` conses EXACTLY `nf` onto the nullifier set (anti-replay teeth: the spent
set strictly grows by the consumed nullifier). -/
theorem execFullA_noteSpend_nullifiers {st st' : RecChainedState} {nf : Nat} {actor : CellId}
    (h : execFullA st (.noteSpendA nf actor) = some st') :
    st'.kernel.nullifiers = nf :: st.kernel.nullifiers :=
  ((execFullA_noteSpend_iff_spec st nf actor st').mp h).2.1

/-- A committed `noteSpendA` prepends EXACTLY the note-spend receipt to the log (the observation clock
ticks by exactly one audited row). -/
theorem execFullA_noteSpend_log {st st' : RecChainedState} {nf : Nat} {actor : CellId}
    (h : execFullA st (.noteSpendA nf actor) = some st') :
    st'.log = noteSpendReceipt actor :: st.log :=
  ((execFullA_noteSpend_iff_spec st nf actor st').mp h).2.2.1

/-- A committed `noteSpendA` consumes a FRESH nullifier — `nf` was NOT already in the spent set (the
guard projection). The post-state membership `nf ∈ st'.kernel.nullifiers` follows from
`execFullA_noteSpend_nullifiers`; THIS records the pre-state freshness the gate enforced. -/
theorem execFullA_noteSpend_fresh {st st' : RecChainedState} {nf : Nat} {actor : CellId}
    (h : execFullA st (.noteSpendA nf actor) = some st') :
    nf ∉ st.kernel.nullifiers :=
  ((execFullA_noteSpend_iff_spec st nf actor st').mp h).1

/-- A committed `noteSpendA` leaves the per-asset balance ledger `bal` UNCHANGED — note effects move
the nullifier SET, never balance (the conservation-neutrality of the family, read off the frame). -/
theorem execFullA_noteSpend_bal_frame {st st' : RecChainedState} {nf : Nat} {actor : CellId}
    (h : execFullA st (.noteSpendA nf actor) = some st') :
    st'.kernel.bal = st.kernel.bal :=
  ((execFullA_noteSpend_iff_spec st nf actor st').mp h).2.2.2.2.2.2.2.2.2.1

/-- The executor COMMITS a `noteSpendA` IFF the nullifier is fresh (the guard projection of the
spec ↔). The fail-closed double-spend gate, as a commitment criterion. -/
theorem execFullA_noteSpend_commits_iff (st : RecChainedState) (nf : Nat) (actor : CellId) :
    (∃ st', execFullA st (.noteSpendA nf actor) = some st') ↔ noteSpendGuard st nf := by
  constructor
  · rintro ⟨st', h⟩
    exact ((execFullA_noteSpend_iff_spec st nf actor st').mp h).1
  · intro hg
    obtain ⟨st', h, _⟩ := noteSpendChainA_correct st nf actor hg
    exact ⟨st', by unfold execFullA; exact h⟩

/-! ## §8 — NON-VACUITY: the executor REJECTS a double-spend (fail-closed).

A spec that accepts everything is worthless. The dual of Transfer's `rejects_*` lemmas: a spend whose
nullifier is ALREADY in the spent set is REJECTED — `execFullA` returns `none`. This is the
anti-replay gate having teeth — the real double-spend prevention (a SET, not a scalar flag). -/

/-- **`execFullA_noteSpend_rejects_double` — PROVED.** A `noteSpendA` whose nullifier `nf` is ALREADY
spent (`nf ∈ nullifiers`) is REJECTED by the executor (`= none`). The anti-replay gate is genuinely a
gate — no nullifier can be spent twice. -/
theorem execFullA_noteSpend_rejects_double (st : RecChainedState) (nf : Nat) (actor : CellId)
    (hspent : nf ∈ st.kernel.nullifiers) :
    execFullA st (.noteSpendA nf actor) = none := by
  unfold execFullA
  simp only [noteSpendChainA, noteSpendNullifier, if_pos hspent]

/-- The spec is itself UNSATISFIABLE on an already-spent nullifier (the guard conjunct fails) — so
the ↔ is not vacuously true on double-spend inputs. -/
theorem noteSpendSpec_false_on_double (st : RecChainedState) (nf : Nat) (actor : CellId)
    (st' : RecChainedState) (hspent : nf ∈ st.kernel.nullifiers) :
    ¬ NoteSpendSpec st nf actor st' := by
  intro h; exact h.1 hspent

/-! ## §9 — concrete `#guard` witnesses: a fresh spend commits; a repeat spend is rejected. -/

/-- A concrete chained pre-state: live accounts {0, 1}, empty nullifier set, empty log. -/
def st0 : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun _ => .record [], caps := fun _ => [] }
    log    := [] }

-- A fresh spend (nf = 77 ∉ []) commits:
#guard (execFullA st0 (.noteSpendA 77 0)).isSome  -- true
-- ...its committed nullifier set is exactly [77] (the consumed nullifier, head-consed onto []):
#guard ((execFullA st0 (.noteSpendA 77 0)).map (fun s => s.kernel.nullifiers)) == some [77]  -- true
-- ...its committed log has length 1 (exactly one receipt prepended onto the empty log):
#guard ((execFullA st0 (.noteSpendA 77 0)).map (fun s => s.log.length)) == some 1  -- true
-- ...and the prepended receipt row carries (actor=0, src=actor=0, dst=actor=0, amt=0):
#guard ((execFullA st0 (.noteSpendA 77 0)).bind (fun s => s.log.head?)).map
        (fun r => (r.actor, r.src, r.dst, r.amt)) == some (0, 0, 0, (0 : Int))  -- true
-- A REPEAT spend of the same nullifier into the already-spent state is REJECTED (fail-closed):
#guard (((execFullA st0 (.noteSpendA 77 0)).bind
          (fun s => execFullA s (.noteSpendA 77 0))).isNone)  -- true

/-! ## §10 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recKernel_ext
#assert_axioms noteSpendChainA_correct
#assert_axioms execFullA_noteSpend_iff_spec
#assert_axioms execFullA_noteSpend_nullifiers
#assert_axioms execFullA_noteSpend_log
#assert_axioms execFullA_noteSpend_fresh
#assert_axioms execFullA_noteSpend_bal_frame
#assert_axioms execFullA_noteSpend_commits_iff
#assert_axioms execFullA_noteSpend_rejects_double
#assert_axioms noteSpendSpec_false_on_double

end Dregg2.Circuit.Spec.NoteNullifier
