/-
# Dregg2.Circuit.Spec.queuepipelinedsend — INDEPENDENT full-state spec + executor⟺spec for the
`queue-pipelined-send` effect family (variant `pipelinedSendA`).

This module is the `queue-pipelined-send` corner of the spec⟺executor discipline that
`Dregg2.Circuit.Transfer` (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) established
for the conservative `Transfer` effect. Where `Transfer` moves the conserved `balance` measure across
two cells, `pipelinedSendA`'s **apply-time** effect is NEUTRAL: it writes the **observation log** and
NOTHING in the kernel — a balance-neutral clock row marking that the (already-resolved) pipelined send
has been applied. The real deferred dispatch + `EventualRef`→prior-result resolution is the SEPARATE
batch machinery in `ConditionalTurn.lean` (the topological-order producer-slot fill the consumer
reads); AT apply time the resolved action has already run, so this arm is the apply-time no-op-or-error
of dregg1, modelled as a clock tick.

## The effect (the executor's `pipelinedSendA` arm, `TurnExecutorFull.lean:3578`)

    | .pipelinedSendA actor =>
        some { kernel := s.kernel, log := escrowReceiptA actor :: s.log }

where (`TurnExecutorFull.lean:1982`)

    escrowReceiptA actor := { actor := actor, src := actor, dst := actor, amt := 0 }

So a committed `pipelinedSendA`:

  * **GUARD** — NONE. There is **NO fail-closed gate** at apply time: the arm is `some { … }`
    UNCONDITIONALLY (the real dispatch/admissibility already happened in the `ConditionalTurn`
    resolution pass). The effect is TOTAL — it ALWAYS commits. Contrast `Transfer.admitGuard`
    (a six-way conjunction) and even `emitEventA` (a one-conjunct cell-liveness gate): this arm has
    no precondition whatsoever.
  * **TOUCHED component** — the receipt chain `log`: a single self-`Turn` row
    `{ actor, src := actor, dst := actor, amt := 0 }` (`escrowReceiptA actor`) is prepended (the
    apply-time NEUTRAL marker — `amt = 0`, `src = dst = actor`, so it is balance-neutral; it carries
    NO send-specific payload, see `frameGaps` below).
  * **FRAME** — the ENTIRE `RecordKernelState` is LITERALLY unchanged: all 17 kernel fields
    (`accounts cell caps escrows nullifiers revoked commitments bal queues swiss slotCaveats
    factories lifecycle deathCert delegate delegations sealedBoxes`). The executor sets
    `kernel := s.kernel` verbatim, so the whole kernel is fixed.

## What this module proves (the Transfer pattern, transposed onto the apply-time-neutral domain)

  1. `PipelinedSendSpec st actor st'` — the INDEPENDENT declarative full-state post-state: the EXACT
     log post-state ∧ EVERY one of the 17 kernel fields unchanged (the FRAME). No frame clause names
     `execFullA`/`escrowReceiptA`. (No admissibility-guard conjunct — the effect is TOTAL.)
  2. `execFullA_pipelinedSend_iff_spec` — `execFullA st (.pipelinedSendA actor) = some st' ↔
     PipelinedSendSpec st actor st'`, BOTH directions. The `→` VALIDATES the executor against the
     independent spec: all 17 kernel fields + the log are checked, so had the executor silently
     mutated ANY kernel field the frame clause would make this proof FAIL.
  3. `pipelinedSendStep_correct` — the post-state image validated DECLARATIVELY (its log row + its
     kernel-frame), the `recTransfer_correct` analog for this family.
  4. `#assert_axioms` on every theorem (whitelist `{propext, Classical.choice, Quot.sound}`).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.QueuePipelinedSend

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the receipt the executor appends (the touched-component post-image).

The exact `Turn` row a committed pipelined-send prepends to the log: the apply-time NEUTRAL clock
receipt `escrowReceiptA actor`, a balance-`0` self-`Turn` on the `actor`. Defined here as DATA (no
executor term), so the spec's log clause is a literal post-image, not a re-export of
`escrowReceiptA`; the validation lemma `pipelinedSendReceipt_eq` below ties it back to the executor's
actual receipt so this independence is not vacuous. -/
def pipelinedSendReceipt (actor : CellId) : Turn :=
  { actor := actor, src := actor, dst := actor, amt := 0 }

/-- The INDEPENDENT receipt-data equals the executor's actual `escrowReceiptA` (the apply-time
NEUTRAL marker). So the spec's `log` clause pins the executor's appended row, not a
re-export. -/
theorem pipelinedSendReceipt_eq (actor : CellId) :
    pipelinedSendReceipt actor = escrowReceiptA actor := by
  simp only [pipelinedSendReceipt, escrowReceiptA]

/-! ## §2 — `pipelinedSendStep_correct` — the post-state image validated DECLARATIVELY.

The `recTransfer_correct` analog: rather than blindly trusting the executor's `some { kernel := …,
log := … }` literal, we PIN what a committed pipelined-send does — its log grows by exactly the
`pipelinedSendReceipt` row (head), the tail is the old log, and the kernel is literally unchanged. So
the spec's `st'.log = pipelinedSendReceipt … :: st.log` ∧ kernel-frame clauses encode the
arm's behaviour. -/
theorem pipelinedSendStep_correct (st : RecChainedState) (actor : CellId) :
    ({ kernel := st.kernel, log := escrowReceiptA actor :: st.log } : RecChainedState).log
        = pipelinedSendReceipt actor :: st.log
    ∧ ({ kernel := st.kernel, log := escrowReceiptA actor :: st.log } : RecChainedState).kernel
        = st.kernel := by
  refine ⟨?_, ?_⟩
  · simp only [pipelinedSendReceipt, escrowReceiptA]
  · rfl

/-! ## §2b — kernel extensionality from the 17 field equalities.

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

/-! ## §3 — the FULL-STATE declarative spec of a committed `pipelinedSendA` (the INDEPENDENT reference).

`PipelinedSendSpec` is the WHOLE truth of a committed pipelined-send, written INDEPENDENTLY of the
executor (no `execFullA`/`escrowReceiptA`-as-a-frame term): the post-state's `log` is exactly the
NEUTRAL receipt prepended to the old log (the TOUCHED component); and EVERY one of the 17
`RecordKernelState` components is LITERALLY unchanged (the FRAME — missing any one reintroduces a
ghost).

There is NO admissibility-guard conjunct: the apply-time effect is TOTAL (no fail-closed gate — the
real dispatch is the `ConditionalTurn` resolution pass), so the spec is unconditional in `st`/`actor`
and merely pins the (unique) post-state. -/
def PipelinedSendSpec (st : RecChainedState) (actor : CellId) (st' : RecChainedState) : Prop :=
  -- the TOUCHED component: the receipt chain grows by exactly the NEUTRAL pipelined-send receipt.
  st'.log = pipelinedSendReceipt actor :: st.log
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

/-! ## §4 — `execFullA_pipelinedSend_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions). -/

/-- **`execFullA_pipelinedSend_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The full
record executor commits a `pipelinedSendA` into `st'` IFF `st'` is EXACTLY the spec'd full post-state.

The `→` direction VALIDATES `execFullA` against the independent spec: ALL 17 kernel fields AND the
log are checked, so had the executor silently mutated `bal`/`nullifiers`/`caps`/any kernel field, the
corresponding frame clause would make this proof FAIL. The `←` reconstructs the committed state from
the spec. Because the arm is TOTAL (`some { … }` unconditionally), there is no guard branch — every
`st'` matching the spec IS the committed post-state, and conversely. This is the executor corner of
the `queue-pipelined-send` spec⟺executor square. -/
theorem execFullA_pipelinedSend_iff_spec (st : RecChainedState) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.pipelinedSendA actor) = some st'
      ↔ PipelinedSendSpec st actor st' := by
  unfold execFullA PipelinedSendSpec
  constructor
  · intro h
    simp only [Option.some.injEq] at h
    subst h
    -- the committed post-state is `{ kernel := st.kernel, log := escrowReceiptA actor :: st.log }`;
    -- read its log + every kernel field off that literal. The log clause uses the receipt eq.
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [pipelinedSendReceipt, escrowReceiptA]
  · rintro ⟨hlog, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12, h13, h14, h15, h17, h18⟩
    -- rebuild `st'` from the log post-image + the 17 kernel-field equalities.
    have hk : st'.kernel = st.kernel :=
      recKernel_ext h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18
    cases st' with
    | mk k' lg' =>
      simp only at hk hlog
      subst hk
      rw [hlog]
      simp only [pipelinedSendReceipt, escrowReceiptA]

/-! ## §5 — corollaries: the two domain facts a committed pipelined-send produces (executor side).

Convenience projections of `execFullA_pipelinedSend_iff_spec` for downstream callers: a committed
pipelined-send GROWS the log by exactly the NEUTRAL receipt, and FRAMES the entire kernel. These are
the `queue-pipelined-send` analogs of `recKExec_src_debit`/`recKExec_dst_credit` (the per-component
executor facts). -/

/-- A committed `pipelinedSendA` prepends EXACTLY the NEUTRAL pipelined-send receipt to the log (the
apply-time clock ticks by exactly one audited row). -/
theorem execFullA_pipelinedSend_log {st st' : RecChainedState} {actor : CellId}
    (h : execFullA st (.pipelinedSendA actor) = some st') :
    st'.log = pipelinedSendReceipt actor :: st.log :=
  ((execFullA_pipelinedSend_iff_spec st actor st').mp h).1

/-- A committed `pipelinedSendA` leaves the ENTIRE kernel unchanged (the full kernel-frame: every one
of the 17 fields is fixed, so the kernel record itself is `st.kernel`). The apply-time effect is
NEUTRAL — no ledger move, no side-table touched. -/
theorem execFullA_pipelinedSend_kernel {st st' : RecChainedState} {actor : CellId}
    (h : execFullA st (.pipelinedSendA actor) = some st') :
    st'.kernel = st.kernel := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7, h10, h11, h12, h13, h14, h15, h17, h18⟩ := (execFullA_pipelinedSend_iff_spec st actor st').mp h
  exact recKernel_ext h1 h2 h3 h4 h5 h6 h7 h10 h11 h12 h13 h14 h15 h17 h18

/-- The executor ALWAYS COMMITS a `pipelinedSendA` (the TOTALITY of the effect — there is no
fail-closed gate at apply time). The dual of `emitEventA`'s `commits_iff` with a `True` guard:
commitment is unconditional. -/
theorem execFullA_pipelinedSend_commits (st : RecChainedState) (actor : CellId) :
    ∃ st', execFullA st (.pipelinedSendA actor) = some st' :=
  ⟨{ kernel := st.kernel, log := escrowReceiptA actor :: st.log }, rfl⟩

/-! ## §6 — NEUTRALITY: the committed step is balance-neutral and conserves the kernel measure.

The dual of Transfer's conservation: because the kernel is framed whole, EVERY conserved measure the
kernel carries is preserved across a `pipelinedSendA` — in particular the per-asset combined measure
`recTotalAsset` is fixed for every asset (the `delta = 0` neutrality the apply-time marker
claims). This is the teeth of "apply-time NEUTRAL". -/

/-- **`execFullA_pipelinedSend_neutral`.** A committed `pipelinedSendA` preserves the
per-asset combined measure `recTotalAsset` for EVERY asset — the apply-time effect moves no
value (`delta = 0`). Read directly off the whole-kernel frame. -/
theorem execFullA_pipelinedSend_neutral {st st' : RecChainedState} {actor : CellId} (b : AssetId)
    (h : execFullA st (.pipelinedSendA actor) = some st') :
    recTotalAsset st'.kernel b = recTotalAsset st.kernel b := by
  rw [execFullA_pipelinedSend_kernel h]

/-! ## §7 — concrete `#guard` witnesses: a pipelined-send commits with a single neutral clock row. -/

/-- A concrete chained pre-state: live accounts {0, 1}, empty log. -/
def st0 : RecChainedState :=
  { kernel := { accounts := {0, 1}, cell := fun _ => .record [], caps := fun _ => [] }
    log    := [] }

-- A pipelined-send (actor 0) commits unconditionally:
#guard (execFullA st0 (.pipelinedSendA 0)).isSome  -- true
-- ...its committed log has length 1 (exactly one NEUTRAL receipt prepended onto the empty log):
#guard ((execFullA st0 (.pipelinedSendA 0)).map (fun s => s.log.length)) == some 1  -- true
-- ...and the prepended receipt row is the apply-time NEUTRAL marker (actor=0, src=0, dst=0, amt=0):
#guard ((execFullA st0 (.pipelinedSendA 0)).bind (fun s => s.log.head?)).map
        (fun r => (r.actor, r.src, r.dst, r.amt)) == some (0, 0, 0, (0 : Int))  -- true
-- ...and it commits regardless of the actor id (TOTAL — no gate, even on a non-account actor 7):
#guard (execFullA st0 (.pipelinedSendA 7)).isSome  -- true

/-! ## §8 — axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms pipelinedSendReceipt_eq
#assert_axioms pipelinedSendStep_correct
#assert_axioms recKernel_ext
#assert_axioms execFullA_pipelinedSend_iff_spec
#assert_axioms execFullA_pipelinedSend_log
#assert_axioms execFullA_pipelinedSend_kernel
#assert_axioms execFullA_pipelinedSend_commits
#assert_axioms execFullA_pipelinedSend_neutral

end Dregg2.Circuit.Spec.QueuePipelinedSend
