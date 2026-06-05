/-
# Dregg2.Circuit.Spec.bridgeoutboundcancel — INDEPENDENT full-state spec + executor⟺spec for the
`bridge-outbound-cancel` effect family (the `FullActionA.bridgeCancelA` variant — Phase 4 of dregg1's
two-phase cross-chain bridge, `cancel_bridge`/`cell/src/note_bridge.rs`, `turn/src/executor/apply.rs`).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the bridge-outbound-CANCEL effect that the unified action executor `execFullA` dispatches:

    execFullA s (.bridgeCancelA id actor) = bridgeCancelChainA s id actor          -- TurnExecutorFull:3552
    bridgeCancelChainA s id actor
      = if bridgeAuthOK s.kernel id actor then
          match bridgeCancelKAsset s.kernel id with
          | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log } | none => none
        else none

Unlike the LOCK (a single `if` over caller-supplied parameters), the CANCEL arm is gated TWICE on the
COMMITTED holding-store via the SAME `find?` lookup — the parked record is read from state, NOT
caller-supplied:

  * `bridgeAuthOK k id actor` (`TurnExecutorFull:2801`):
        match k.escrows.find? (·.id = id ∧ ·.resolved = false) with
        | some r => r.bridge == true && r.creator == actor   -- (A) the AUTHORITY gate (recorded creator only)
        | none   => false
  * `bridgeCancelKAsset k id` (`RecordKernel.lean:1753`):
        match k.escrows.find? (·.id = id ∧ ·.resolved = false) with
        | some r => if r.bridge = true ∧ r.creator ∈ k.accounts ∧ cellLifecycleLive k r.creator = true
                    then some (settleEscrowRawAsset k id r.creator r.asset r.amount) else none
        | none   => none

So the FULL admissibility guard a committed cancel checks is, on the FOUND record `r`:

    k.escrows.find? (·.id = id ∧ ·.resolved = false) = some r              -- a PARKED record with `id` exists
  ∧ r.bridge = true                                                        -- it is a BRIDGE record (not ordinary escrow)
  ∧ r.creator = actor                                                      -- (A) AUTHORITY: only the recorded creator/originator
  ∧ r.creator ∈ k.accounts                                                 -- (B) REFUND-TARGET MEMBERSHIP (settle-liveness)
  ∧ cellLifecycleLive k r.creator = true                                   -- (C) REFUND-TARGET LIFECYCLE-LIVE (D3 fail-closed teeth)

(The TIMEOUT gate — "the §8-layer the timeout was reached without a receipt" — is carried at the
effect/theorem layer, NOT in this state arm, exactly as the task notes; this module specs the LEDGER
move only.) On commit `settleEscrowRawAsset` (`RecordKernel.lean:1481`) produces:
  * `bal` ledger: a SINGLE-cell, single-asset CREDIT of `+r.amount` to `(r.creator, r.asset)`
    (`recBalCreditCell k.bal r.creator r.asset r.amount`) — the value REFUNDED to the originator,
  * `escrows` store: `markResolved k.escrows id` — the FIRST unresolved record with `id` marked resolved,
  * EVERY OTHER kernel field (15 of them) and the chained `log` (advanced by `escrowReceiptA actor ::`)
    are the FRAME.

## What is proved (the apex reference truth, BOTH directions)

  * `BridgeOutboundCancelSpec st id actor st'` — the INDEPENDENT declarative full-state post-condition:
    there is a found record `r` satisfying the admissibility guard (`cancelGuard`), the EXACT post-`bal`
    ledger (`recBalCreditCell … r.creator r.asset r.amount` — the +amount refund credit), the EXACT
    post-`escrows` store (`markResolved … id`), the chained `log` advanced by exactly `escrowReceiptA
    actor ::`, AND the FRAME — every one of the 15 OTHER RecordKernelState components LITERALLY
    unchanged (`accounts cell caps nullifiers revoked commitments queues swiss slotCaveats factories
    lifecycle deathCert delegate delegations sealedBoxes`). No frame clause mentions the executor.
    All 17 kernel components + log are enumerated.

  * `settleEscrowRawAsset_correct` — the post-state helper validated DECLARATIVELY (the `bal` credit at
    `(target,asset)`, the other-`(cell,asset)` ledger-frame, the `escrows := markResolved … id`), so
    the spec's `bal`/`escrows` clauses genuinely encode credit ∧ ledger-frame ∧ resolve rather than
    blind trust.

  * `bridgeCancelChainA_iff_spec` — the ⟺ stated on the chained step `bridgeCancelChainA`.
  * `execFullA_bridgeCancelA_iff_spec` — execFullA ⟺ spec for the `bridgeCancelA` variant (BOTH
    directions). The `→` VALIDATES the executor against the independent spec (all 17 kernel fields +
    log are checked, so a silently mutated field would make the proof FAIL); `←` reconstructs.

  * Post-state corollaries: `bridgeCancel_refund` (per-asset credit at `(r.creator,r.asset)`),
    `bridgeCancel_other_untouched` (per-asset ledger frame), `bridgeCancel_resolves_record`
    (`escrows = markResolved …`).

  * Non-vacuity: `…_rejects_no_record`, `…_rejects_nonbridge`, `…_rejects_noncreator`,
    `…_rejects_dead_creator`, `…_rejects_nonlive_creator` — each forged input fails a guard leg ⇒ the
    executor returns `none` ⇒ no spec post-state exists. A spec that accepts everything is worthless.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.BridgeOutboundCancel

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (the `bridgeAuthOK` ∧ `bridgeCancelKAsset`-match conjunction).

A committed cancel passes through BOTH `bridgeAuthOK` (the recorded-creator authority gate) and the
`bridgeCancelKAsset` match-gate, and BOTH read the SAME `find?` record. We extract that as a `Prop`
existentially binding the found record `r` (the parked bridge record the cancel resolves). The guard
is INDEPENDENT of the executor: it names `find?`/`accounts`/`cellLifecycleLive` (the committed state),
not the executor's `bridgeCancelChainA`/`bridgeCancelKAsset` bodies. -/

/-- The full bridge-outbound-cancel admissibility guard, as a `Prop` over the FOUND record `r`: a
parked, unresolved BRIDGE record with `id` exists, the caller IS its recorded creator/originator (the
authority gate), and that creator is a LIVE account (the D3 settle-liveness teeth — crediting a frozen
cell would silently destroy value, so it fails closed). -/
def cancelGuard (k : RecordKernelState) (id : Nat) (actor : CellId) (r : EscrowRecord) : Prop :=
  k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r
    ∧ r.bridge = true ∧ r.creator = actor ∧ r.creator ∈ k.accounts
    ∧ cellLifecycleLive k r.creator = true

/-! ## §2 — the post-state helper, validated DECLARATIVELY.

`settleEscrowRawAsset` (`RecordKernel.lean:1481`) is the post-state the executor installs on commit. We
pin EXACTLY what it does — credit `(target,asset)` by `+amount` on the `bal` ledger (leaving every
other `(cell,asset)` untouched) and replace `escrows` with `markResolved k.escrows id` — so the spec's
`bal`/`escrows` clauses are genuine credit ∧ ledger-frame ∧ resolve, not blind trust. -/

/-- **`settleEscrowRawAsset_correct`** — the cancel post-state helper validated declaratively: the
settle credits `(target,asset)` by `+amount`, leaves every other `(cell,asset)` ledger entry
untouched, and sets `escrows` to `markResolved k.escrows id`. -/
theorem settleEscrowRawAsset_correct (k : RecordKernelState) (id target : CellId) (asset : AssetId)
    (amount : ℤ) :
    (settleEscrowRawAsset k id target asset amount).bal target asset = k.bal target asset + amount
    ∧ (∀ c b, ¬ (c = target ∧ b = asset) →
        (settleEscrowRawAsset k id target asset amount).bal c b = k.bal c b)
    ∧ (settleEscrowRawAsset k id target asset amount).escrows = markResolved k.escrows id := by
  refine ⟨?_, ?_, rfl⟩
  · show recBalCreditCell k.bal target asset amount target asset = k.bal target asset + amount
    unfold recBalCreditCell
    rw [if_pos ⟨rfl, rfl⟩]
  · intro c b hcd
    show recBalCreditCell k.bal target asset amount c b = k.bal c b
    unfold recBalCreditCell
    rw [if_neg hcd]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`BridgeOutboundCancelSpec` is the COMPLETE declarative post-state of a committed `bridgeCancelA`,
written INDEPENDENTLY of the executor: there is a found record `r` for which the guard holds; the
post-`bal` ledger is the single-cell single-asset CREDIT to `(r.creator, r.asset)`; the post-`escrows`
store is `markResolved st.escrows id`; the chained `log` advances by exactly `escrowReceiptA actor ::`;
and EVERY OTHER state component — all 15 non-`bal`, non-`escrows` RecordKernelState fields — is
LITERALLY unchanged (the FRAME). No frame clause references the executor's bodies. -/

/-- **The full-state declarative spec of a committed `bridgeCancelA`** — the INDEPENDENT reference
semantics. There exists a found record `r` with `cancelGuard` holding; the post-`bal` ledger credits
`(r.creator,r.asset)` by `r.amount` (`recBalCreditCell`, validated by `settleEscrowRawAsset_correct`);
the post-`escrows` store is `markResolved st.escrows id`; the chained `log` is `escrowReceiptA actor ::
st.log`; and every one of the 15 other RecordKernelState components is unchanged. -/
def BridgeOutboundCancelSpec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) : Prop :=
  ∃ r : EscrowRecord,
    cancelGuard st.kernel id actor r
    ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal r.creator r.asset r.amount
    ∧ st'.kernel.escrows = markResolved st.kernel.escrows id
    ∧ st'.log = escrowReceiptA actor :: st.log
    -- THE FRAME: every non-`bal`, non-`escrows` RecordKernelState field, literally unchanged (15).
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

/-! ### §3a — a `bridgeAuthOK` characterization (the recorded-creator gate, on the found record). -/

/-- `bridgeAuthOK k id actor = true` IFF there is a found unresolved record `r` that is a bridge record
whose recorded creator IS the caller. Pins the authority gate to the committed side-table. -/
theorem bridgeAuthOK_iff (k : RecordKernelState) (id : Nat) (actor : CellId) :
    bridgeAuthOK k id actor = true
      ↔ ∃ r, k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r
              ∧ r.bridge = true ∧ r.creator = actor := by
  unfold bridgeAuthOK
  cases hfind : k.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none => simp
  | some r =>
      constructor
      · intro h
        have h' := (Bool.and_eq_true _ _).mp h
        exact ⟨r, rfl, by simpa using h'.1, by simpa using h'.2⟩
      · rintro ⟨r', hr', hb, hc⟩
        obtain rfl : r' = r := (Option.some.inj hr').symm
        rw [Bool.and_eq_true]
        exact ⟨by simpa using hb, by simpa using hc⟩

/-- **`bridgeCancelChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
bridge-cancel step. `bridgeCancelChainA` commits a cancel into `st'` IFF `st'` is EXACTLY the spec'd
full post-state. The `→` VALIDATES `bridgeCancelChainA` against the independent spec — all 17 kernel
components (`bal` + `escrows` + the 15 frame fields) AND the log are checked, so a silently mutated
field would make the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem bridgeCancelChainA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    bridgeCancelChainA st id actor = some st'
      ↔ BridgeOutboundCancelSpec st id actor st' := by
  unfold bridgeCancelChainA BridgeOutboundCancelSpec cancelGuard bridgeAuthOK bridgeCancelKAsset
  cases hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) with
  | none =>
      simp only [hfind]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨r, ⟨hr, _⟩, _⟩; exact absurd hr (by simp)
  | some r =>
      simp only [hfind]
      by_cases hauth : (r.bridge == true && r.creator == actor) = true
      · -- AUTHORITY gate passes
        have hb : r.bridge = true := by
          have := (Bool.and_eq_true _ _).mp hauth; simpa using this.1
        have hca : r.creator = actor := by
          have := (Bool.and_eq_true _ _).mp hauth; simpa using this.2
        rw [if_pos hauth]
        by_cases hmatch : r.bridge = true ∧ r.creator ∈ st.kernel.accounts
            ∧ cellLifecycleLive st.kernel r.creator = true
        · -- match-gate passes ⇒ commit
          rw [if_pos hmatch]
          simp only [settleEscrowRawAsset]
          constructor
          · intro h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨r, ⟨rfl, hb, hca, hmatch.2.1, hmatch.2.2⟩, ?_⟩
            refine ⟨rfl, rfl, rfl, ?_⟩            -- bal, escrows, log
            refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩  -- accounts cell caps nullifiers revoked
            refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩  -- commitments queues swiss slotCaveats factories
            exact ⟨rfl, rfl, rfl, rfl, rfl⟩       -- lifecycle deathCert delegate delegations sealedBoxes
          · rintro ⟨r', ⟨hr', _, _, _, _⟩, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9,
              h10, h11, h12, h13, h14, h15⟩
            -- the found record is unique: r' = r
            obtain rfl : r' = r := (Option.some.inj hr').symm
            obtain ⟨k', l'⟩ := st'
            obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
            simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
            subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
            rfl
        · -- match-gate fails (creator non-member or non-live) ⇒ none, and no spec record can hold
          rw [if_neg hmatch]
          constructor
          · intro h; exact absurd h (by simp)
          · rintro ⟨r', ⟨hr', hb', hca', hmem', hlive'⟩, _⟩
            obtain rfl : r' = r := (Option.some.inj hr').symm
            exact absurd ⟨hb', hmem', hlive'⟩ hmatch
      · -- AUTHORITY gate fails ⇒ none, and no spec record can hold the authority leg
        rw [if_neg hauth]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨r', ⟨hr', hb', hca', _, _⟩, _⟩
          obtain rfl : r' = r := (Option.some.inj hr').symm
          exact absurd (by rw [Bool.and_eq_true]; exact ⟨by simpa using hb', by simpa using hca'⟩) hauth

/-- **`execFullA_bridgeCancelA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA` dispatches
`.bridgeCancelA …` to `bridgeCancelChainA s …`, so committing the unified action into `st'` is EXACTLY
the full-state spec. This is the variant-level executor⟺spec. -/
theorem execFullA_bridgeCancelA_iff_spec (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) :
    execFullA st (.bridgeCancelA id actor) = some st'
      ↔ BridgeOutboundCancelSpec st id actor st' := by
  show bridgeCancelChainA st id actor = some st' ↔ BridgeOutboundCancelSpec st id actor st'
  exact bridgeCancelChainA_iff_spec st id actor st'

/-! ## §4 — the post-state facts a committed step produces (refund / resolve / ledger-frame corollaries).

These read off `BridgeOutboundCancelSpec` + `settleEscrowRawAsset_correct` to expose the genuine effect
(the per-asset refund credit at `(r.creator,r.asset)`, the resolved record, the untouched other ledger
entries). -/

/-- **`bridgeCancel_refund`** — a committed cancel CREDITS the originator's (`r.creator`) asset-`r.asset`
ledger by `+r.amount` (the value REFUNDED from the bridge holding-store back to the locker after the
timeout). -/
theorem bridgeCancel_refund (st : RecChainedState) (id : Nat) (actor : CellId) (st' : RecChainedState)
    (h : execFullA st (.bridgeCancelA id actor) = some st') :
    ∃ r, cancelGuard st.kernel id actor r ∧
      st'.kernel.bal r.creator r.asset = st.kernel.bal r.creator r.asset + r.amount := by
  obtain ⟨r, hg, hbal, _⟩ := (execFullA_bridgeCancelA_iff_spec st id actor st').mp h
  refine ⟨r, hg, ?_⟩
  rw [hbal]
  exact (settleEscrowRawAsset_correct st.kernel id r.creator r.asset r.amount).1

/-- **`bridgeCancel_other_untouched`** — a committed cancel leaves every other `(cell,asset)` ledger
entry untouched (the per-asset ledger frame — no cross-cell or cross-asset laundering at the refund). -/
theorem bridgeCancel_other_untouched (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.bridgeCancelA id actor) = some st') :
    ∃ r, cancelGuard st.kernel id actor r ∧
      ∀ c b, ¬ (c = r.creator ∧ b = r.asset) → st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨r, hg, hbal, _⟩ := (execFullA_bridgeCancelA_iff_spec st id actor st').mp h
  refine ⟨r, hg, ?_⟩
  intro c b hcd
  rw [hbal]
  exact (settleEscrowRawAsset_correct st.kernel id r.creator r.asset r.amount).2.1 c b hcd

/-- **`bridgeCancel_resolves_record`** — a committed cancel sets `escrows` to `markResolved … id` (the
parked record leaves the unresolved set — the lock is released and the value returned). -/
theorem bridgeCancel_resolves_record (st : RecChainedState) (id : Nat) (actor : CellId)
    (st' : RecChainedState) (h : execFullA st (.bridgeCancelA id actor) = some st') :
    st'.kernel.escrows = markResolved st.kernel.escrows id := by
  obtain ⟨_, _, _, hesc, _⟩ := (execFullA_bridgeCancelA_iff_spec st id actor st').mp h
  exact hesc

/-! ## §5 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Here each forged input
fails a guard conjunct ⇒ `execFullA st (.bridgeCancelA …) = none` ⇒ no spec post-state exists. -/

/-- **`bridgeCancel_rejects_no_record` — PROVED.** A cancel for an `id` with NO parked unresolved record
does NOT commit (the find? leg fails — `bridgeAuthOK` returns false on `none`). -/
theorem bridgeCancel_rejects_no_record (st : RecChainedState) (id : Nat) (actor : CellId)
    (hbad : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = none) :
    execFullA st (.bridgeCancelA id actor) = none := by
  show bridgeCancelChainA st id actor = none
  unfold bridgeCancelChainA bridgeAuthOK
  rw [hbad]
  rw [if_neg (by simp)]

/-- **`bridgeCancel_rejects_nonbridge` — PROVED.** A cancel whose found record is NOT bridge-tagged (an
ordinary escrow row sharing the holding-store) does NOT commit (the bridge leg of `bridgeAuthOK` fails). -/
theorem bridgeCancel_rejects_nonbridge (st : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord)
    (hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hbad : r.bridge = false) :
    execFullA st (.bridgeCancelA id actor) = none := by
  show bridgeCancelChainA st id actor = none
  unfold bridgeCancelChainA bridgeAuthOK
  rw [hfind]; simp [hbad]

/-- **`bridgeCancel_rejects_noncreator` — PROVED (the cancel-side authority teeth).** A cancel by anyone
OTHER than the recorded creator/originator does NOT commit (the `bridgeAuthOK` creator leg fails — a
stranger who merely knows the `id` cannot trigger the refund of a victim's parked lock). -/
theorem bridgeCancel_rejects_noncreator (st : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord)
    (hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hbad : r.creator ≠ actor) :
    execFullA st (.bridgeCancelA id actor) = none := by
  show bridgeCancelChainA st id actor = none
  unfold bridgeCancelChainA bridgeAuthOK
  have hbeq : (r.creator == actor) = false := by simpa using hbad
  rw [hfind]; simp [hbeq]

/-- **`bridgeCancel_rejects_dead_creator` — PROVED.** A cancel whose found record's creator (the refund
target) is NOT an account does NOT commit (the settle-MEMBERSHIP leg of the match-gate fails — crediting
a non-account would silently destroy value). Requires the authority gate to have passed (else
`rejects_noncreator`/`rejects_nonbridge` apply). -/
theorem bridgeCancel_rejects_dead_creator (st : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord)
    (hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hbad : r.creator ∉ st.kernel.accounts) :
    execFullA st (.bridgeCancelA id actor) = none := by
  show bridgeCancelChainA st id actor = none
  unfold bridgeCancelChainA bridgeCancelKAsset
  by_cases hauth : bridgeAuthOK st.kernel id actor = true
  · rw [if_pos hauth]
    simp only [hfind, if_neg (show ¬ (r.bridge = true ∧ r.creator ∈ st.kernel.accounts
      ∧ cellLifecycleLive st.kernel r.creator = true) from by rintro ⟨_, hmem, _⟩; exact hbad hmem)]
  · rw [if_neg hauth]

/-- **`bridgeCancel_rejects_nonlive_creator` — PROVED (the D3 fail-closed teeth).** A cancel whose found
record's creator is a Sealed/Destroyed cell (`cellLifecycleLive = false`) does NOT commit — even if it
is still a member, a frozen cell cannot be credited the refund. Requires the authority gate to have
passed. -/
theorem bridgeCancel_rejects_nonlive_creator (st : RecChainedState) (id : Nat) (actor : CellId)
    (r : EscrowRecord)
    (hfind : st.kernel.escrows.find? (fun r => decide (r.id = id ∧ r.resolved = false)) = some r)
    (hbad : cellLifecycleLive st.kernel r.creator = false) :
    execFullA st (.bridgeCancelA id actor) = none := by
  show bridgeCancelChainA st id actor = none
  unfold bridgeCancelChainA
  by_cases hauth : bridgeAuthOK st.kernel id actor = true
  · rw [if_pos hauth, bridgeCancelKAsset_nonlive_fails hfind hbad]
  · rw [if_neg hauth]

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms settleEscrowRawAsset_correct
#assert_axioms bridgeAuthOK_iff
#assert_axioms bridgeCancelChainA_iff_spec
#assert_axioms execFullA_bridgeCancelA_iff_spec
#assert_axioms bridgeCancel_refund
#assert_axioms bridgeCancel_other_untouched
#assert_axioms bridgeCancel_resolves_record
#assert_axioms bridgeCancel_rejects_no_record
#assert_axioms bridgeCancel_rejects_nonbridge
#assert_axioms bridgeCancel_rejects_noncreator
#assert_axioms bridgeCancel_rejects_dead_creator
#assert_axioms bridgeCancel_rejects_nonlive_creator

end Dregg2.Circuit.Spec.BridgeOutboundCancel
