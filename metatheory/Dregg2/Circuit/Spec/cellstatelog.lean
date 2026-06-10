/-
# Dregg2.Circuit.Spec.cellstatelog — INDEPENDENT full-state spec + executor⟺spec for the
`cell-state-log` effect family (variant `emitEventA`).

This module is the `cell-state-log` corner of the spec⟺executor discipline that
`Dregg2.Circuit.Transfer` (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) established
for the conservative `Transfer` effect. Where Transfer moves the conserved `balance` measure across
two cells, the `cell-state-log` family writes the **observation log** and NOTHING in the kernel.

## The effect (the executor's `emitEventA` arm, `TurnExecutorFull.lean:3492`)

    | .emitEventA actor cell topic data =>
        if cell ∈ s.kernel.accounts then some (emitStep s actor cell topic data) else none

where (`TurnExecutorFull.lean:1264`)

    emitStep s actor cell topic data :=
      { kernel := s.kernel,
        log    := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }

So a committed `emitEventA`:

  * **GUARD** — `cell ∈ s.kernel.accounts` (dregg1 `apply_emit_event`'s ONLY gate is cell-existence;
    there is **NO authority gate** — anyone may emit on a live cell — and **no** non-negativity /
    availability / distinctness check that `Transfer` carries).
  * **TOUCHED component** — the receipt chain `log`: a single self-`Turn` row
    `{ actor, src := cell, dst := cell, amt := 0 }` is prepended (the `topic`/`data` ride the
    receipt's `src`/`dst` markers — note the executor does NOT route `topic`/`data` onto the receipt:
    the row carries `cell` in BOTH `src` and `dst` and `0` in `amt`, INDEPENDENT of the event
    payload; see `frameGaps` below).
  * **FRAME** — the ENTIRE `RecordKernelState` is LITERALLY unchanged: all 17 kernel fields
    (`accounts cell caps escrows nullifiers revoked commitments bal queues swiss slotCaveats
    factories lifecycle deathCert delegate delegations sealedBoxes`).

## What this module proves (the Transfer pattern, transposed onto the log domain)

  1. `EmitEventSpec st actor cell topic data st'` — the INDEPENDENT declarative full-state post-state:
     the guard ∧ the EXACT log post-state ∧ EVERY one of the 17 kernel fields unchanged (the FRAME).
     No frame clause names `execFullA`/`emitStep`.
  2. `execFullA_emitEvent_iff_spec` — `execFullA st (.emitEventA …) = some st' ↔ EmitEventSpec …`,
     BOTH directions. The `→` VALIDATES the executor against the independent spec: all 17 kernel
     fields + the log are checked, so had the executor silently mutated ANY kernel field the frame
     clause would make this proof FAIL.
  3. `emitStep_correct` — the post-state helper `emitStep` validated DECLARATIVELY (its log row and
     its kernel-frame), the `recTransfer_correct` analog for this family.
  4. `#assert_axioms` on every theorem (whitelist `{propext, Classical.choice, Quot.sound}`).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStateLog

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (cell-existence; NO authority gate).

The ENTIRE guard `execFullA`'s `emitEventA` arm checks before committing: the target cell is live.
Unlike `Transfer.admitGuard` (a six-way conjunction with authority/non-negativity/availability/…),
`emitGuard` is the single cell-liveness conjunct — dregg1's `apply_emit_event` runs no authority
check (anyone may post an observation on a live cell). Stated INDEPENDENTLY of the executor. -/
def emitGuard (st : RecChainedState) (cell : CellId) : Prop :=
  cell ∈ st.kernel.accounts

/-! ## §2 — the receipt the executor appends (the touched-component post-image).

The exact `Turn` row a committed emit prepends to the log: a self-receipt on `cell` with zero
amount. Defined as DATA (no executor term), so the spec's log clause is a literal post-image, not a
re-export of `emitStep`. -/
def emitReceipt (actor cell : CellId) : Turn :=
  { actor := actor, src := cell, dst := cell, amt := 0 }

/-! ## §3 — `emitStep_correct` — the post-state helper validated DECLARATIVELY.

The `recTransfer_correct` analog: rather than blindly trusting `emitStep`, we PIN what it does — its
log grows by exactly the `emitReceipt` row (head), the tail is the old log, and the kernel is
literally unchanged. So the spec's `st'.log = emitReceipt … :: st.log` ∧ kernel-frame clauses
encode the helper's behaviour. -/
theorem emitStep_correct (st : RecChainedState) (actor cell : CellId) (topic data : Int) :
    (emitStep st actor cell topic data).log = emitReceipt actor cell :: st.log
    ∧ (emitStep st actor cell topic data).kernel = st.kernel := by
  refine ⟨?_, ?_⟩
  · simp only [emitStep, emitReceipt]
  · simp only [emitStep]

/-! ## §3b — kernel extensionality from the 17 field equalities.

A helper turning the spec's 17 per-field frame equalities back into a single `RecordKernelState`
equality (so the `←` reconstruction can rebuild the kernel record). Stated/proved by destructuring
both records — the structure eta is what makes "17 fields equal ⇒ records equal" a `rfl` after the
substitutions. -/
theorem recKernel_ext {k k' : RecordKernelState}
    (h1 : k'.accounts = k.accounts) (h2 : k'.cell = k.cell) (h3 : k'.caps = k.caps)
    (h4 : k'.nullifiers = k.nullifiers) (h5 : k'.revoked = k.revoked)
    (h6 : k'.commitments = k.commitments) (h7 : k'.bal = k.bal) (h10 : k'.slotCaveats = k.slotCaveats)
    (h11 : k'.factories = k.factories) (h12 : k'.lifecycle = k.lifecycle)
    (h13 : k'.deathCert = k.deathCert) (h14 : k'.delegate = k.delegate)
    (h15 : k'.delegations = k.delegations)
    (h17 : k'.delegationEpoch = k.delegationEpoch) (h18 : k'.delegationEpochAt = k.delegationEpochAt) :
    k' = k := by
  cases k; cases k'
  simp only at h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18
  subst h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18
  rfl

/-! ## §4 — the FULL-STATE declarative spec of a committed `emitEventA` (the INDEPENDENT reference).

`EmitEventSpec` is the WHOLE truth of a committed emit, written INDEPENDENTLY of the executor (no
`execFullA`/`emitStep` term in any clause): the guard holds; the post-state's `log` is exactly the
receipt prepended to the old log (the TOUCHED component); and EVERY one of the 17 `RecordKernelState`
components is LITERALLY unchanged (the FRAME — missing any one reintroduces a ghost). -/
def EmitEventSpec (st : RecChainedState) (actor cell : CellId) (topic data : Int)
    (st' : RecChainedState) : Prop :=
  emitGuard st cell
  -- the TOUCHED component: the receipt chain grows by exactly the emit receipt.
  ∧ st'.log = emitReceipt actor cell :: st.log
  -- the FRAME: all 17 kernel fields LITERALLY unchanged.
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.bal = st.kernel.bal
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt

/-! ## §5 — `execFullA_emitEvent_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions). -/

/-- **`execFullA_emitEvent_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full
record executor commits an `emitEventA` into `st'` IFF `st'` is EXACTLY the spec'd full post-state.

The `→` direction VALIDATES `execFullA` against the independent spec: ALL 17 kernel fields AND the
log are checked, so had the executor silently mutated `bal`/`nullifiers`/`caps`/any kernel field, the
corresponding frame clause would make this proof FAIL. The `←` reconstructs the committed state from
the spec. This is the executor corner of the `cell-state-log` spec⟺executor square. -/
theorem execFullA_emitEvent_iff_spec (st : RecChainedState) (actor cell : CellId) (topic data : Int)
    (st' : RecChainedState) :
    execFullA st (.emitEventA actor cell topic data) = some st'
      ↔ EmitEventSpec st actor cell topic data st' := by
  unfold execFullA EmitEventSpec emitGuard
  by_cases hlive : cell ∈ st.kernel.accounts
  · rw [if_pos hlive]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      -- the committed post-state is `emitStep …`; read its log + every kernel field off `emitStep`.
      refine ⟨hlive, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      simp only [emitStep, emitReceipt]
    · rintro ⟨_, hlog, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12, h13, h14, h15, h17, h18⟩
      -- rebuild `st'` from the log post-image + the 17 kernel-field equalities.
      have hk : st'.kernel = st.kernel :=
        recKernel_ext h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18
      cases st' with
      | mk k' lg' =>
        simp only at hk hlog
        subst hk hlog
        simp only [emitStep, emitReceipt]
  · rw [if_neg hlive]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg, _⟩; exact absurd hg hlive

/-! ## §6 — corollaries: the two domain facts a committed emit produces (executor side).

Convenience projections of `execFullA_emitEvent_iff_spec` for downstream callers: a committed emit
GROWS the log by exactly the receipt, and FRAMES the entire kernel. These are the `cell-state-log`
analogs of `recKExec_src_debit`/`recKExec_dst_credit` (the per-component executor facts). -/

/-- A committed `emitEventA` prepends EXACTLY the emit receipt to the log (the observation clock
ticks by exactly one audited row). -/
theorem execFullA_emitEvent_log {st st' : RecChainedState} {actor cell : CellId} {topic data : Int}
    (h : execFullA st (.emitEventA actor cell topic data) = some st') :
    st'.log = emitReceipt actor cell :: st.log :=
  ((execFullA_emitEvent_iff_spec st actor cell topic data st').mp h).2.1

/-- A committed `emitEventA` leaves the ENTIRE kernel unchanged (the full kernel-frame: every one of
the 17 fields is fixed, so the kernel record itself is `st.kernel`). -/
theorem execFullA_emitEvent_kernel {st st' : RecChainedState} {actor cell : CellId}
    {topic data : Int}
    (h : execFullA st (.emitEventA actor cell topic data) = some st') :
    st'.kernel = st.kernel := by
  obtain ⟨_, _, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12, h13, h14, h15, h17, h18⟩ := (execFullA_emitEvent_iff_spec st actor cell topic data st').mp h
  exact recKernel_ext h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18

/-- The executor COMMITS an `emitEventA` IFF the cell is live (the guard projection of the spec ↔). -/
theorem execFullA_emitEvent_commits_iff (st : RecChainedState) (actor cell : CellId)
    (topic data : Int) :
    (∃ st', execFullA st (.emitEventA actor cell topic data) = some st') ↔ emitGuard st cell := by
  constructor
  · rintro ⟨st', h⟩
    exact ((execFullA_emitEvent_iff_spec st actor cell topic data st').mp h).1
  · intro hg
    refine ⟨emitStep st actor cell topic data, ?_⟩
    unfold execFullA emitGuard at *
    rw [if_pos hg]

/-! ## §7 — NON-VACUITY: the executor REJECTS an emit on a DEAD cell (fail-closed).

A spec that accepts everything is worthless. The dual of Transfer's `rejects_*` lemmas: an emit whose
target cell is NOT a live account is REJECTED — `execFullA` returns `none`. This is the cell-existence
gate having teeth. -/

/-- **`execFullA_emitEvent_rejects_dead`.** An `emitEventA` whose target `cell` is NOT a
live account (`cell ∉ accounts`) is REJECTED by the executor (`= none`). The one gate this effect
carries is a gate. -/
theorem execFullA_emitEvent_rejects_dead (st : RecChainedState) (actor cell : CellId)
    (topic data : Int) (hdead : cell ∉ st.kernel.accounts) :
    execFullA st (.emitEventA actor cell topic data) = none := by
  unfold execFullA
  rw [if_neg hdead]

/-- The spec is itself UNSATISFIABLE on a dead cell (the guard conjunct fails) — so the ↔ is not
vacuously true on dead-cell inputs. -/
theorem emitSpec_false_on_dead (st : RecChainedState) (actor cell : CellId) (topic data : Int)
    (st' : RecChainedState) (hdead : cell ∉ st.kernel.accounts) :
    ¬ EmitEventSpec st actor cell topic data st' := by
  intro h; exact hdead h.1

/-! ## §8 — concrete `#guard` witnesses: a live-cell emit commits; a dead-cell emit is rejected. -/

/-- A concrete chained pre-state: live accounts {0, 1}, empty log. -/
def st0 : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun _ => .record [], caps := fun _ => [] }
    log    := [] }

-- A live-cell emit (cell 1 ∈ {0,1}) commits:
#guard (execFullA st0 (.emitEventA 5 1 9 42)).isSome  -- true
-- ...its committed log has length 1 (exactly one receipt prepended onto the empty log):
#guard ((execFullA st0 (.emitEventA 5 1 9 42)).map (fun s => s.log.length)) == some 1  -- true
-- ...and the prepended receipt row carries (actor=5, src=cell=1, dst=cell=1, amt=0)
-- (component-wise — the payload `topic`/`data` do NOT ride the receipt; see frameGaps):
#guard ((execFullA st0 (.emitEventA 5 1 9 42)).bind (fun s => s.log.head?)).map
        (fun r => (r.actor, r.src, r.dst, r.amt)) == some (5, 1, 1, (0 : Int))  -- true
-- A dead-cell emit (cell 7 ∉ {0,1}) is REJECTED:
#guard (execFullA st0 (.emitEventA 5 7 9 42)).isNone  -- true

/-! ## §9 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms emitStep_correct
#assert_axioms recKernel_ext
#assert_axioms execFullA_emitEvent_iff_spec
#assert_axioms execFullA_emitEvent_log
#assert_axioms execFullA_emitEvent_kernel
#assert_axioms execFullA_emitEvent_commits_iff
#assert_axioms execFullA_emitEvent_rejects_dead
#assert_axioms emitSpec_false_on_dead

end Dregg2.Circuit.Spec.CellStateLog
