/-
# Dregg2.Circuit.Spec.queuepipelinefanout — an INDEPENDENT full-state spec + executor⟺spec for the
effect family **queue-pipeline-fanout** (`queuePipelineStepA`).

This is a LEAF module copying the REFERENCE pattern of `Dregg2/Circuit/Transfer.lean`
(`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) for the FAN-OUT routing step:

    execFullA s (.queuePipelineStepA srcId owner sinkCells sinkIds)
      = queuePipelineStepA s srcId owner sinkCells sinkIds            (TurnExecutorFull.lean:3577)

The pipeline step (dregg1 `apply_queue_pipeline_step`, `apply.rs:3747`) DEQUEUEs the FIFO head of a
source queue `srcId` (owner-only, fail-closed if absent / not-owner / EMPTY — `apply.rs:3754`/`:3766`)
and RE-ENQUEUEs that one moved head message into EACH sink (the fan-out, each sink ACL-gated per
`stateAuthB owner sink` BUG#114, fail-closed if absent / FULL / unauthorized — `apply.rs:3812`). The
`sinkCells`/`sinkIds` are paired position-wise. The step is BALANCE-NEUTRAL — it moves a MESSAGE
(queue side-table), never balance.

Unlike `Transfer` (a single branch over one `if`), this arm is a COMPOSITION: a `queueDequeueK`
followed by the recursive `pipelineFanoutK` fold. So the admissibility witness is EXISTENTIAL (the
moved head `m` and the intermediate kernel `k1`). The touched component is `queues` only; the
post-`queues` is pinned by `pipelineFanoutK k1 owner m … = some s'.kernel` — the same discipline
`TransferSpec` uses when it pins the touched `cell` map by `k'.cell = recTransfer …` (a helper for the
touched component is the reference style; the FRAME clauses below use NO helper).

## What this module proves (the §6b apex-truth shape)

  * `pipelineFanoutK_frame`   — DECLARATIVE validation of the fan-out fold's post-state helper: the
                                fold touches ONLY `queues`; ALL 16 other kernel fields LITERALLY
                                unchanged (the `recTransfer_correct` analog — the helper is validated,
                                not trusted).
  * `queueDequeueK_frame`     — same for the source dequeue.
  * `QueuePipelineFanoutSpec` — the INDEPENDENT full-state declarative spec: admissibility guard ∧ the
                                EXACT post-`queues` (the touched component) ∧ EVERY other kernel field
                                (16 of them) + the `log` LITERALLY unchanged-except-the-one-routing-row
                                (the FRAME, NO executor helper in any frame clause).
  * `execFullA_iff_spec`      — execFullA st (.queuePipelineStepA …) = some st' ↔ spec (BOTH ways). The
                                `→` VALIDATES the executor against the independent spec: had the
                                executor silently mutated `bal`/`nullifiers`/`caps`/… the frame proof
                                would FAIL.
  * `queuePipelineStepA_iff_spec` — the same characterization at the bare `queuePipelineStepA` layer.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.QueuePipelineFanout

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState (stateAuthB)
open Dregg2.Tactics

/-! ## §1 — FRAME for the source dequeue (`queueDequeueK`).

`queueDequeueK k id actor` either fails or returns `({ k with queues := … }, m)` — so its post-kernel
touches ONLY `queues`. We validate this DECLARATIVELY (every one of the 16 non-`queues` fields is
literally `k`'s), so the spec's touched-component clause genuinely encodes a queues-only rewrite. -/

/-- **`queueDequeueK_frame` — the source-dequeue post-state touches ONLY `queues`.** Every one of the
16 non-`queues` kernel fields is literally unchanged. (The dequeued head `m` is the FIFO order witness,
not constrained here.) -/
theorem queueDequeueK_frame {k k' : RecordKernelState} {id : Nat} {actor : CellId} {m : Nat}
    (h : queueDequeueK k id actor = some (k', m)) :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
    ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
    ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
    ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
    ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
    ∧ k'.sealedBoxes = k.sealedBoxes := by
  unfold queueDequeueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases ho : actor = q.owner
      · rw [if_pos ho] at h
        cases hd : qbufDequeue q.buffer with
        | none           => rw [hd] at h; exact absurd h (by simp)
        | some hr        =>
            obtain ⟨mh, rest⟩ := hr
            rw [hd] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨hk, _⟩ := h; subst hk
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg ho] at h; exact absurd h (by simp)

/-! ## §2 — FRAME for one enqueue (`queueEnqueueK`) and the fan-out fold (`pipelineFanoutK`).

Each `queueEnqueueK k id m` either fails or returns `{ k with queues := … }` — queues-only. The
fan-out fold `pipelineFanoutK` chains those, so the WHOLE fan-out is queues-only. We prove it by
induction on the sink list, the `recTransfer_correct` analog for the fold. -/

/-- **`queueEnqueueK_frame` — one fan-out enqueue touches ONLY `queues`.** -/
theorem queueEnqueueK_frame {k k' : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k') :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
    ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
    ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
    ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
    ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
    ∧ k'.sealedBoxes = k.sealedBoxes := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-- **`pipelineFanoutK_frame` — DECLARATIVE validation of the FAN-OUT fold's post-state.** The fan-out
re-enqueue fold touches ONLY `queues`: ALL 16 other kernel fields are LITERALLY unchanged. This is the
`recTransfer_correct` analog — the touched-component helper is VALIDATED (the fold is queues-only),
not trusted. Proved by induction on the sink list. -/
theorem pipelineFanoutK_frame {k k' : RecordKernelState} {actor : CellId} {m : Nat}
    {sinks : List CellId} {sids : List Nat}
    (h : pipelineFanoutK k actor m sinks sids = some k') :
    k'.accounts = k.accounts ∧ k'.cell = k.cell ∧ k'.caps = k.caps
    ∧ k'.escrows = k.escrows ∧ k'.nullifiers = k.nullifiers ∧ k'.revoked = k.revoked
    ∧ k'.commitments = k.commitments ∧ k'.bal = k.bal ∧ k'.swiss = k.swiss
    ∧ k'.slotCaveats = k.slotCaveats ∧ k'.factories = k.factories ∧ k'.lifecycle = k.lifecycle
    ∧ k'.deathCert = k.deathCert ∧ k'.delegate = k.delegate ∧ k'.delegations = k.delegations
    ∧ k'.sealedBoxes = k.sealedBoxes := by
  induction sinks generalizing k sids with
  | nil =>
      cases sids <;>
        (simp only [pipelineFanoutK, Option.some.injEq] at h; subst h;
         exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
  | cons sink rest ih =>
      cases sids with
      | nil => simp only [pipelineFanoutK] at h; exact absurd h (by simp)
      | cons sid sids' =>
          simp only [pipelineFanoutK] at h
          by_cases hg : stateAuthB k.caps actor sink = true
          · rw [if_pos hg] at h
            cases hq : queueEnqueueK k sid m with
            | none    => rw [hq] at h; exact absurd h (by simp)
            | some k1 =>
                rw [hq] at h
                -- one enqueue frames each of the 16 fields …
                obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ :=
                  queueEnqueueK_frame hq
                -- … then the tail of the fold frames them too; chain by transitivity.
                obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16⟩ := ih h
                exact ⟨t1.trans e1, t2.trans e2, t3.trans e3, t4.trans e4, t5.trans e5, t6.trans e6,
                       t7.trans e7, t8.trans e8, t9.trans e9, t10.trans e10, t11.trans e11,
                       t12.trans e12, t13.trans e13, t14.trans e14, t15.trans e15, t16.trans e16⟩
          · rw [if_neg hg] at h; exact absurd h (by simp)

/-! ## §3 — the routing receipt row + the admissibility guard. -/

/-- The single routing-receipt row a committed pipeline step appends, on the `owner` (the source
dequeuer) — a bal-`0` self-row (dregg1 records the routing on the source dequeuer). -/
def routingRow (owner : CellId) : Turn := { actor := owner, src := owner, dst := owner, amt := 0 }

/-- **The full admissibility guard the executor checks**, as a `Prop`: there EXIST a moved FIFO head
`m` and an intermediate kernel `k1` such that the SOURCE dequeue succeeds (owner-only, source present
and NON-EMPTY) AND the SINK fan-out succeeds (each sink present, not FULL, actor authorized per-sink —
BUG#114). The existential is intrinsic — the step is a COMPOSITION, not a single branch — so the
witness `(k1, m)` is the moved head and the post-dequeue kernel. -/
def admitGuard (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) : Prop :=
  ∃ k1 m, queueDequeueK s.kernel srcId owner = some (k1, m)
          ∧ (pipelineFanoutK k1 owner m sinkCells sinkIds).isSome

/-! ## §4 — `QueuePipelineFanoutSpec` — the INDEPENDENT full-state declarative spec.

The COMPLETE state transition of a committed pipeline step. The touched component is `queues` (its
post-value is pinned via the dequeue-then-fanout witness, exactly as `TransferSpec` pins the touched
`cell` via `recTransfer`); the `log` gains EXACTLY one routing row; and EVERY one of the 16 non-`queues`
kernel fields is LITERALLY unchanged (the FRAME — NO executor helper in any frame clause). Missing ANY
field would reintroduce a ghost. Enumerated: `accounts cell caps escrows nullifiers revoked commitments
bal swiss slotCaveats factories lifecycle deathCert delegate delegations sealedBoxes` (16) + `queues`
(touched) + `log`. -/
def QueuePipelineFanoutSpec (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState) : Prop :=
  -- (A) admissibility: the source dequeue + sink fan-out both succeed, with witness `(k1, m)`.
  (∃ k1 m, queueDequeueK s.kernel srcId owner = some (k1, m)
            ∧ pipelineFanoutK k1 owner m sinkCells sinkIds = some s'.kernel)
  -- (B) the log gains EXACTLY one routing row (on the owner).
  ∧ s'.log = routingRow owner :: s.log
  -- (C) THE FRAME — every non-`queues` kernel field LITERALLY unchanged (no executor helper here).
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.cell = s.kernel.cell
  ∧ s'.kernel.caps = s.kernel.caps ∧ s'.kernel.escrows = s.kernel.escrows
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes

/-! ## §5 — `queuePipelineStepA ⟺ spec` (BOTH directions, FULL state). -/

/-- **`queuePipelineStepA_iff_spec` — EXECUTOR ⟺ SPEC at the bare layer (both directions, FULL state).**
The bare `queuePipelineStepA` commits IFF `s'` is EXACTLY the spec'd full post-state. The `→` direction
VALIDATES the executor against the independent spec — all 18 components (16 frame + queues-touched +
log) are checked, so had the executor silently mutated any framed field the proof would FAIL. The `←`
reconstructs the committed state from the spec. -/
theorem queuePipelineStepA_iff_spec (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState) :
    queuePipelineStepA s srcId owner sinkCells sinkIds = some s'
      ↔ QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s' := by
  unfold queuePipelineStepA QueuePipelineFanoutSpec
  constructor
  · -- → : a committed step yields the spec (validates the executor against the frame).
    intro h
    cases hd : queueDequeueK s.kernel srcId owner with
    | none    => rw [hd] at h; exact absurd h (by simp)
    | some kr =>
        obtain ⟨k1, m⟩ := kr
        rw [hd] at h; simp only at h
        cases hf : pipelineFanoutK k1 owner m sinkCells sinkIds with
        | none    => rw [hf] at h; exact absurd h (by simp)
        | some k2 =>
            rw [hf] at h; simp only [Option.some.injEq] at h; subst h
            -- the touched-component witness: dequeue = (k1,m), fanout = some k2 = s'.kernel.
            refine ⟨⟨k1, m, rfl, hf⟩, rfl, ?_⟩
            -- the frame: chain the dequeue frame with the fan-out frame for each of the 16 fields.
            obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16⟩ :=
              queueDequeueK_frame hd
            obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ :=
              pipelineFanoutK_frame hf
            exact ⟨f1.trans d1, f2.trans d2, f3.trans d3, f4.trans d4, f5.trans d5, f6.trans d6,
                   f7.trans d7, f8.trans d8, f9.trans d9, f10.trans d10, f11.trans d11, f12.trans d12,
                   f13.trans d13, f14.trans d14, f15.trans d15, f16.trans d16⟩
  · -- ← : the spec reconstructs the committed step (the touched-component witness IS the executor run).
    rintro ⟨⟨k1, m, hd, hf⟩, hlog, _⟩
    -- the committed post-state is `{ kernel := s'.kernel, log := routingRow :: s.log }`; the spec's
    -- log clause says `s'.log = routingRow :: s.log`, so the record equals `s'` componentwise.
    cases s' with
    | mk k' l' =>
        simp only at hf hlog
        subst hlog
        simp only [hd, hf, routingRow]

/-! ## §6 — `execFullA ⟺ spec` (the executor-entry corner; both directions). -/

/-- **`execFullA_iff_spec` — the EXECUTOR ENTRY ⟺ SPEC (both directions, FULL state).** The dispatched
`execFullA` on the `.queuePipelineStepA` action commits IFF `s'` is EXACTLY the spec'd full post-state.
The arm is `execFullA s (.queuePipelineStepA …) = queuePipelineStepA s …` (TurnExecutorFull.lean:3577),
so this lifts `queuePipelineStepA_iff_spec` to the executor entry. The `→` validates the dispatched
executor against the independent spec; the `←` reconstructs. -/
theorem execFullA_iff_spec (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState) :
    execFullA s (.queuePipelineStepA srcId owner sinkCells sinkIds) = some s'
      ↔ QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s' := by
  show queuePipelineStepA s srcId owner sinkCells sinkIds = some s'
        ↔ QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s'
  exact queuePipelineStepA_iff_spec s srcId owner sinkCells sinkIds s'

/-- **`execFullA_admits` — soundness, executor form.** A state matching the spec is exactly a state the
executor admits the action into; in particular the admissibility guard holds. -/
theorem execFullA_admits (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState)
    (h : execFullA s (.queuePipelineStepA srcId owner sinkCells sinkIds) = some s') :
    admitGuard s srcId owner sinkCells sinkIds := by
  obtain ⟨⟨k1, m, hd, hf⟩, _⟩ := (execFullA_iff_spec s srcId owner sinkCells sinkIds s').mp h
  exact ⟨k1, m, hd, by rw [hf]; rfl⟩

/-! ## §7 — NON-VACUITY: the spec REJECTS bad inputs.

A spec that accepts everything is worthless. The executor (hence the spec) is a genuine GATE: an
ABSENT/NOT-OWNER/EMPTY source dequeue, or an ABSENT/FULL/UNAUTHORIZED sink, makes the step `none` ⇒ the
spec is unsatisfiable. -/

/-- **`spec_rejects_no_dequeue` — PROVED.** If the source dequeue fails (queue absent / not-owner /
EMPTY — the BUG#114 owner gate + emptiness gate), NO post-state satisfies the spec. -/
theorem spec_rejects_no_dequeue (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState)
    (hbad : queueDequeueK s.kernel srcId owner = none) :
    ¬ QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s' := by
  rintro ⟨⟨k1, m, hd, _⟩, _⟩
  rw [hbad] at hd; exact absurd hd (by simp)

/-- **`spec_rejects_fanout_fail` — PROVED.** If the source dequeue succeeds with head `m` into `k1` but
the sink fan-out fails (some sink absent / FULL / unauthorized — BUG#114 sink-auth gate), NO post-state
satisfies the spec. -/
theorem spec_rejects_fanout_fail (s : RecChainedState) (srcId : Nat) (owner : CellId)
    (sinkCells : List CellId) (sinkIds : List Nat) (s' : RecChainedState) (k1 : RecordKernelState)
    (m : Nat) (hd : queueDequeueK s.kernel srcId owner = some (k1, m))
    (hbad : pipelineFanoutK k1 owner m sinkCells sinkIds = none) :
    ¬ QueuePipelineFanoutSpec s srcId owner sinkCells sinkIds s' := by
  rintro ⟨⟨k1', m', hd', hf'⟩, _⟩
  rw [hd] at hd'; simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨hk, hm⟩ := hd'; subst hk; subst hm
  rw [hbad] at hf'; exact absurd hf' (by simp)

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms queueDequeueK_frame
#assert_axioms queueEnqueueK_frame
#assert_axioms pipelineFanoutK_frame
#assert_axioms queuePipelineStepA_iff_spec
#assert_axioms execFullA_iff_spec
#assert_axioms execFullA_admits
#assert_axioms spec_rejects_no_dequeue
#assert_axioms spec_rejects_fanout_fail

end Dregg2.Circuit.Spec.QueuePipelineFanout
