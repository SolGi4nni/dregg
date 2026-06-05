/-
# Dregg2.Circuit.Spec.escrowholdingrefund — INDEPENDENT full-state spec + executor⟺spec for the
`escrow-holding-refund` effect family (the `FullActionA.refundEscrowA` and `.fulfillObligationA`
variants).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the per-asset escrow REFUND that the unified action executor `execFullA` actually dispatches. Both
`refundEscrowA` AND `fulfillObligationA` route to the SAME chained step:

    execFullA s (.refundEscrowA id actor)      = refundEscrowChainA s id actor   -- TurnExecutorFull.lean:3527
    execFullA s (.fulfillObligationA id actor) = refundEscrowChainA s id actor   -- TurnExecutorFull.lean:3533

so a SINGLE spec covers BOTH variants (the executor is literally the same term; `fulfillObligationA`
is `refundEscrowA`'s dispatch-alias — the obligor-only + before-deadline fulfill gate is the §8/
theorem-layer carrier, NOT a state move, exactly as the task statement notes). The chained step:

    refundEscrowChainA s id actor = match refundEscrowKAsset s.kernel id with        -- :1999
      | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log } | none => none

`refundEscrowKAsset` (`RecordKernel.lean:1516`) is fail-closed:

    refundEscrowKAsset k id = match k.escrows.find? (fun r => r.id = id ∧ r.resolved = false) with
      | some r => if r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
                  then some (settleEscrowRawAsset k id r.creator r.asset r.amount) else none
      | none   => none

i.e. the ADMISSIBILITY guard is: the unresolved record `r` with this `id` EXISTS, AND its `creator`
(the refund target) is a LIVE account AND its lifecycle admits effects. On commit `settleEscrowRawAsset`
(`RecordKernel.lean:1481`) rewrites EXACTLY two kernel components:

    bal     := recBalCreditCell k.bal r.creator r.asset r.amount   -- single-cell, single-asset CREDIT
    escrows := markResolved k.escrows id                           -- mark the found record resolved

and the chained `log` gets `escrowReceiptA actor` prepended. EVERY OTHER kernel field (the 15 besides
`bal`/`escrows`) is LITERALLY unchanged (`settleEscrowRawAsset` is `{ k with bal := …, escrows := … }`).

## What is proved (the apex reference truth, BOTH directions)

  * `RefundEscrowSpec st id actor st'` — the INDEPENDENT declarative full-state post-condition: there
    EXISTS the found unresolved record `r` (the admissibility witness) whose creator is live; the
    post-`bal` ledger is the single-cell credit (`recBalCreditCell` at (creator, r.asset)); the post-
    `escrows` is `markResolved`; the `log` advanced by exactly `escrowReceiptA actor ::`; AND the FRAME
    — every one of the OTHER 15 RecordKernelState components LITERALLY unchanged (`accounts cell caps
    nullifiers revoked commitments queues swiss slotCaveats factories lifecycle deathCert delegate
    delegations sealedBoxes`). No frame clause mentions the executor. All 17 kernel fields + log are
    enumerated — missing ANY reintroduces a ghost.

  * `refundEscrowChainA_iff_spec` — refundEscrowChainA ⟺ spec (BOTH directions). The `→` VALIDATES the
    executor against the independent spec (all 17 kernel fields + log checked, so a silently mutated
    field would make the proof FAIL); the `←` reconstructs the committed state from the spec witness.

  * `execFullA_refundEscrowA_iff_spec` / `execFullA_fulfillObligationA_iff_spec` — the SAME ⟺ stated on
    each unified-action variant (both dispatch to `refundEscrowChainA`, so the spec is shared).

  * `settleEscrowRawAsset_correct` — the post-state helper validated DECLARATIVELY: the credit lands on
    (creator, r.asset) by `r.amount`, every other (cell,asset) ledger entry is untouched, the record is
    marked resolved, and ALL 15 other kernel fields are preserved — so the spec's post-state clauses
    genuinely encode credit ∧ ledger-frame ∧ resolve ∧ field-frame, not blind trust.

  * Non-vacuity: `…_rejects_missing` (no unresolved record with this id ⇒ none), `…_rejects_dead_creator`
    (refund target not a live account ⇒ none) — each forged input fails a guard leg ⇒ the executor
    returns `none` ⇒ no spec post-state exists.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.EscrowHoldingRefund

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the match predicate + admissibility guard (the `refundEscrowKAsset` body, extracted).

`refundEscrowKAsset` looks up the FIRST unresolved record carrying `id`, then gates on the refund
target (the record's `creator`) being a live account whose lifecycle admits effects. The whole guard
is "such a record exists AND its creator passes the settle-liveness gate". -/

/-- The find-predicate `refundEscrowKAsset` uses to locate the unresolved record carrying `id`
(matches the decidable `r.id = id ∧ r.resolved = false`). -/
def matchPred (id : Nat) : EscrowRecord → Bool := fun r => decide (r.id = id ∧ r.resolved = false)

/-- The full admissibility guard `refundEscrowKAsset` checks, as a `Prop` carrying the found record:
an unresolved record `r` with this `id` EXISTS, and its `creator` (the refund target) is a LIVE
account whose lifecycle admits effects. -/
def admitRefund (k : RecordKernelState) (id : Nat) (r : EscrowRecord) : Prop :=
  k.escrows.find? (matchPred id) = some r
    ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true

/-! ## §2 — the post-state helper `settleEscrowRawAsset`, validated DECLARATIVELY.

`settleEscrowRawAsset k id target asset amount` = `{ k with bal := recBalCreditCell k.bal target asset
amount, escrows := markResolved k.escrows id }`. We pin EXACTLY what it does — single-cell credit at
(target, asset), every other (cell,asset) untouched, `escrows` marked resolved, and all 15 other
kernel fields preserved — so the spec's post-state clauses are genuine, not blind trust. -/

/-- **`settleEscrowRawAsset_correct`** — the settle helper validated declaratively. The credit lands
on `(target, asset)` by `amount`; every other `(cell,asset)` ledger entry is untouched; the `escrows`
field becomes `markResolved …`; and the 15 OTHER kernel fields are each literally unchanged. -/
theorem settleEscrowRawAsset_correct (k : RecordKernelState) (id target : CellId) (asset : AssetId)
    (amount : ℤ) :
    (settleEscrowRawAsset k id target asset amount).bal target asset = k.bal target asset + amount
    ∧ (∀ c b, ¬ (c = target ∧ b = asset) →
        (settleEscrowRawAsset k id target asset amount).bal c b = k.bal c b)
    ∧ (settleEscrowRawAsset k id target asset amount).escrows = markResolved k.escrows id
    ∧ (settleEscrowRawAsset k id target asset amount).accounts = k.accounts
    ∧ (settleEscrowRawAsset k id target asset amount).cell = k.cell
    ∧ (settleEscrowRawAsset k id target asset amount).caps = k.caps
    ∧ (settleEscrowRawAsset k id target asset amount).nullifiers = k.nullifiers
    ∧ (settleEscrowRawAsset k id target asset amount).revoked = k.revoked
    ∧ (settleEscrowRawAsset k id target asset amount).commitments = k.commitments
    ∧ (settleEscrowRawAsset k id target asset amount).queues = k.queues
    ∧ (settleEscrowRawAsset k id target asset amount).swiss = k.swiss
    ∧ (settleEscrowRawAsset k id target asset amount).slotCaveats = k.slotCaveats
    ∧ (settleEscrowRawAsset k id target asset amount).factories = k.factories
    ∧ (settleEscrowRawAsset k id target asset amount).lifecycle = k.lifecycle
    ∧ (settleEscrowRawAsset k id target asset amount).deathCert = k.deathCert
    ∧ (settleEscrowRawAsset k id target asset amount).delegate = k.delegate
    ∧ (settleEscrowRawAsset k id target asset amount).delegations = k.delegations
    ∧ (settleEscrowRawAsset k id target asset amount).sealedBoxes = k.sealedBoxes := by
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · show recBalCreditCell k.bal target asset amount target asset = k.bal target asset + amount
    unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]
  · intro c b hne
    show recBalCreditCell k.bal target asset amount c b = k.bal c b
    unfold recBalCreditCell; rw [if_neg hne]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`RefundEscrowSpec` is the COMPLETE declarative post-state of a committed refund, written INDEPENDENTLY
of the executor: the admissibility witness `r` exists & passes the settle-liveness gate; the post-`bal`
ledger is the single-cell credit to `r.creator` at `r.asset`; the `escrows` field is `markResolved …`;
the chained `log` advances by exactly `escrowReceiptA actor ::`; and EVERY OTHER state component — all
15 non-`bal`/non-`escrows` RecordKernelState fields — is LITERALLY unchanged (the FRAME). No frame
clause references the executor. -/

/-- **The full-state declarative spec of a committed refund** — the INDEPENDENT reference semantics.
There exists the found unresolved record `r` whose creator passes the settle-liveness gate
(`admitRefund`); the post-`bal` is the single-cell credit (`recBalCreditCell` at (creator, r.asset),
validated by `settleEscrowRawAsset_correct`); the post-`escrows` is `markResolved`; the chained `log`
is `escrowReceiptA actor :: st.log`; and every one of the 15 other RecordKernelState components is
unchanged. -/
def RefundEscrowSpec (st : RecChainedState) (id : Nat) (actor : CellId) (st' : RecChainedState) : Prop :=
  ∃ r : EscrowRecord,
    admitRefund st.kernel id r
    ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal r.creator r.asset r.amount
    ∧ st'.kernel.escrows = markResolved st.kernel.escrows id
    ∧ st'.log = escrowReceiptA actor :: st.log
    -- THE FRAME: every non-`bal`/non-`escrows` RecordKernelState field, literally unchanged (15 of them).
    ∧ st'.kernel.accounts = st.kernel.accounts
    ∧ st'.kernel.cell = st.kernel.cell
    ∧ st'.kernel.caps = st.kernel.caps
    ∧ st'.kernel.nullifiers = st.kernel.nullifiers
    ∧ st'.kernel.revoked = st.kernel.revoked
    ∧ st'.kernel.commitments = st.kernel.commitments
    ∧ st'.kernel.queues = st.kernel.queues
    ∧ st'.kernel.swiss = st.kernel.swiss
    ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
    ∧ st'.kernel.factories = st.kernel.factories
    ∧ st'.kernel.lifecycle = st.kernel.lifecycle
    ∧ st'.kernel.deathCert = st.kernel.deathCert
    ∧ st'.kernel.delegate = st.kernel.delegate
    ∧ st'.kernel.delegations = st.kernel.delegations
    ∧ st'.kernel.sealedBoxes = st.kernel.sealedBoxes

/-- **`refundEscrowChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The chained
refund executor commits into `st'` IFF `st'` is EXACTLY the spec'd full post-state. The `→` VALIDATES
`refundEscrowChainA` against the independent spec — all 17 kernel components (`bal`, `escrows`, and the
15 frame fields) AND the log are checked, so a silently mutated field would make the proof FAIL; the
`←` reconstructs the committed state from the spec witness `r`. -/
theorem refundEscrowChainA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    refundEscrowChainA st id actor = some st' ↔ RefundEscrowSpec st id actor st' := by
  unfold refundEscrowChainA RefundEscrowSpec admitRefund refundEscrowKAsset
  cases hf : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
    dsimp only
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨r, ⟨hfind, _⟩, _⟩
      -- the spec's `find? = some r` contradicts `find? = none`
      rw [show (fun r => decide (r.id = id ∧ r.resolved = false))
            = matchPred id from rfl] at hf
      rw [hf] at hfind; exact absurd hfind (by simp)
  | some r =>
    dsimp only
    by_cases hg : r.creator ∈ st.kernel.accounts ∧ cellLifecycleLive st.kernel r.creator = true
    · rw [if_pos hg]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨r, ⟨?_, hg.1, hg.2⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl⟩
        rw [show (fun r => decide (r.id = id ∧ r.resolved = false)) = matchPred id from rfl] at hf
        exact hf
      · rintro ⟨r', ⟨hfind, _⟩, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
          h13, h14, h15⟩
        -- the spec's found record is THIS `r` (find? is functional)
        rw [show (fun r => decide (r.id = id ∧ r.resolved = false)) = matchPred id from rfl] at hf
        rw [hf] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        -- reconstruct st' field-by-field from the spec
        obtain ⟨k', l'⟩ := st'
        obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
        simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        rfl
    · rw [if_neg hg]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r', ⟨hfind, hlive, hlc⟩, _⟩
        -- the spec's found record is THIS `r`, so its creator passes the gate — contradiction with hg
        rw [show (fun r => decide (r.id = id ∧ r.resolved = false)) = matchPred id from rfl] at hf
        rw [hf] at hfind
        simp only [Option.some.injEq] at hfind
        subst hfind
        exact absurd ⟨hlive, hlc⟩ hg

/-- **`execFullA_refundEscrowA_iff_spec` — the UNIFIED-ACTION executor corner (refund variant).** The
action executor `execFullA` dispatches `.refundEscrowA id actor` to `refundEscrowChainA s id actor`, so
committing the unified action into `st'` is EXACTLY the full-state spec. -/
theorem execFullA_refundEscrowA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.refundEscrowA id actor) = some st' ↔ RefundEscrowSpec st id actor st' := by
  show refundEscrowChainA st id actor = some st' ↔ RefundEscrowSpec st id actor st'
  exact refundEscrowChainA_iff_spec st id actor st'

/-- **`execFullA_fulfillObligationA_iff_spec` — the UNIFIED-ACTION executor corner (fulfill variant).**
`.fulfillObligationA id actor` is the dispatch-ALIAS of `.refundEscrowA`: `execFullA` routes it to the
SAME `refundEscrowChainA s id actor` (fulfill RETURNS the stake to the obligor = the record's creator,
exactly the escrow refund; the obligor-only + before-deadline gate is the §8/theorem-layer carrier).
So it meets the IDENTICAL full-state spec. -/
theorem execFullA_fulfillObligationA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.fulfillObligationA id actor) = some st' ↔ RefundEscrowSpec st id actor st' := by
  show refundEscrowChainA st id actor = some st' ↔ RefundEscrowSpec st id actor st'
  exact refundEscrowChainA_iff_spec st id actor st'

/-! ## §4 — the post-state facts a committed refund produces (the credit/frame corollaries).

These read off `RefundEscrowSpec` + `settleEscrowRawAsset_correct` to expose the genuine value
movement (the refund credit to the creator) — the conserved-slice projection of the full spec. -/

/-- **`refundEscrow_credits_creator`** — a committed refund credits the record's `creator` (the refund
target) at the record's asset by the record's amount. -/
theorem refundEscrow_credits_creator (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) (r : EscrowRecord)
    (h : execFullA st (.refundEscrowA id actor) = some st')
    (hr : st.kernel.escrows.find? (matchPred id) = some r) :
    st'.kernel.bal r.creator r.asset = st.kernel.bal r.creator r.asset + r.amount := by
  obtain ⟨r', ⟨hfind, _⟩, hbal, _⟩ := (execFullA_refundEscrowA_iff_spec st id actor st').mp h
  rw [hr] at hfind; simp only [Option.some.injEq] at hfind; subst hfind
  rw [hbal]
  unfold recBalCreditCell; rw [if_pos ⟨rfl, rfl⟩]

/-- **`refundEscrow_other_untouched`** — a committed refund leaves every other `(cell,asset)` ledger
entry untouched (the per-asset ledger frame). -/
theorem refundEscrow_other_untouched (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) (r : EscrowRecord)
    (h : execFullA st (.refundEscrowA id actor) = some st')
    (hr : st.kernel.escrows.find? (matchPred id) = some r)
    (c : CellId) (b : AssetId) (hne : ¬ (c = r.creator ∧ b = r.asset)) :
    st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨r', ⟨hfind, _⟩, hbal, _⟩ := (execFullA_refundEscrowA_iff_spec st id actor st').mp h
  rw [hr] at hfind; simp only [Option.some.injEq] at hfind; subst hfind
  rw [hbal]
  unfold recBalCreditCell; rw [if_neg hne]

/-- **`refundEscrow_resolves`** — a committed refund marks the escrow holding-store record resolved
(`markResolved`), so the parked value leaves the unresolved set. -/
theorem refundEscrow_resolves (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.refundEscrowA id actor) = some st') :
    st'.kernel.escrows = markResolved st.kernel.escrows id := by
  obtain ⟨_, _, _, hesc, _⟩ := (execFullA_refundEscrowA_iff_spec st id actor st').mp h
  exact hesc

/-! ## §5 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Here each forged input
fails a guard conjunct ⇒ `execFullA st (.refundEscrowA …) = none` ⇒ no spec post-state exists. -/

/-- **`refundEscrow_rejects_missing` — PROVED.** No unresolved record carrying `id` ⇒ the refund does
NOT commit (the existence leg fails). -/
theorem refundEscrow_rejects_missing (st : RecChainedState) (id : Nat) (actor : CellId)
    (hbad : st.kernel.escrows.find? (matchPred id) = none) :
    execFullA st (.refundEscrowA id actor) = none := by
  show refundEscrowChainA st id actor = none
  unfold refundEscrowChainA refundEscrowKAsset
  rw [show (fun r => decide (r.id = id ∧ r.resolved = false)) = matchPred id from rfl, hbad]

/-- **`refundEscrow_rejects_dead_creator` — PROVED.** The found record's `creator` (refund target) is
NOT a live account ⇒ the refund does NOT commit (the settle-liveness leg fails) — crediting a
non-account would silently DESTROY value. -/
theorem refundEscrow_rejects_dead_creator (st : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord) (hr : st.kernel.escrows.find? (matchPred id) = some r)
    (hbad : r.creator ∉ st.kernel.accounts) :
    execFullA st (.refundEscrowA id actor) = none := by
  show refundEscrowChainA st id actor = none
  unfold refundEscrowChainA refundEscrowKAsset
  rw [show (fun r => decide (r.id = id ∧ r.resolved = false)) = matchPred id from rfl, hr]
  dsimp only
  rw [if_neg (by rintro ⟨h, _⟩; exact hbad h)]

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms settleEscrowRawAsset_correct
#assert_axioms refundEscrowChainA_iff_spec
#assert_axioms execFullA_refundEscrowA_iff_spec
#assert_axioms execFullA_fulfillObligationA_iff_spec
#assert_axioms refundEscrow_credits_creator
#assert_axioms refundEscrow_other_untouched
#assert_axioms refundEscrow_resolves
#assert_axioms refundEscrow_rejects_missing
#assert_axioms refundEscrow_rejects_dead_creator

end Dregg2.Circuit.Spec.EscrowHoldingRefund
