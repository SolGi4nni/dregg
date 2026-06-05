/-
# Dregg2.Circuit.Spec.escrowholdingcreate — INDEPENDENT full-state spec + executor⟺spec for the
`escrow-holding-create` effect family (the `FullActionA.createEscrowA` / `.createObligationA`
variants).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the off-ledger escrow-LOCK create effect that the unified action executor `execFullA` dispatches:

    execFullA s (.createEscrowA id actor creator recipient asset amount)
      = createEscrowChainA s id actor creator recipient asset amount         -- TurnExecutorFull:3524
    createEscrowChainA s id actor creator recipient asset amount
      = match createEscrowKAsset s.kernel id actor creator recipient asset amount with
        | some k' => some { kernel := k', log := escrowReceiptA actor :: s.log } | none => none

    execFullA s (.createObligationA id actor obligor beneficiary asset stake)
      = createEscrowChainA s id actor obligor beneficiary asset stake          -- TurnExecutorFull:3528
    -- `createObligationA` is a DEFINITIONAL ALIAS of `createEscrowA` on the same chained step, so the
    -- obligation variant inherits the create spec verbatim (`execFullA_createObligationA_iff_spec`).

`createEscrowKAsset` (`RecordKernel.lean:1490`) is the EXECUTABLE per-asset lock create. Its
admissibility guard is the conjunction:

    authorizedB caps {actor, src:=creator, dst:=recipient, amt:=amount} = true  -- (1) AUTHORITY
  ∧ 0 ≤ amount                                                                   -- (2) NON-NEGATIVITY
  ∧ amount ≤ k.bal creator asset                                                 -- (3) AVAILABILITY in asset
  ∧ creator ∈ k.accounts                                                         -- (4) CREATOR LIVENESS
  ∧ ¬ (∃ r ∈ k.escrows, r.id = id)                                              -- (5) ID FRESHNESS

and on commit it produces `createEscrowRawAsset` (`RecordKernel.lean:1471`):
  * `bal` ledger: a SINGLE-cell, single-asset DEBIT of `amount` from `(creator, asset)`
    (`recBalCreditCell k.bal creator asset (-amount)`),
  * `escrows` store: PREPEND an unresolved `EscrowRecord {id, creator, recipient, amount,
    resolved:=false, asset}`,
  * EVERY OTHER kernel field (15 of them) and the chained `log` (advanced by `escrowReceiptA actor ::`)
    are the FRAME.

## What is proved (the apex reference truth, BOTH directions)

  * `EscrowHoldingCreateSpec st id actor creator recipient asset amount st'` — the INDEPENDENT
    declarative full-state post-condition: the admissibility guard, the EXACT post-`bal` ledger
    (`recBalCreditCell … (-amount)`), the EXACT post-`escrows` store (the prepended unresolved record),
    the chained `log` advanced by exactly `escrowReceiptA actor ::`, AND the FRAME — every one of the
    15 OTHER RecordKernelState components LITERALLY unchanged (`accounts cell caps nullifiers revoked
    commitments queues swiss slotCaveats factories lifecycle deathCert delegate delegations
    sealedBoxes`). No frame clause mentions the executor. Missing ANY field reintroduces a ghost — all
    17 kernel components + log are enumerated.

  * `createEscrowKAsset_correct` — the post-state helper (`createEscrowRawAsset`) validated
    DECLARATIVELY (the `bal` debit at `(creator,asset)`, the other-`(cell,asset)` ledger-frame, the
    `escrows` prepend), so the spec's `bal`/`escrows` clauses genuinely encode debit ∧ ledger-frame ∧
    park-record rather than blind trust.

  * `createEscrowChainA_iff_spec` — the ⟺ stated on the chained step `createEscrowChainA`.
  * `execFullA_createEscrowA_iff_spec` — execFullA ⟺ spec for the `createEscrowA` variant (BOTH
    directions). The `→` VALIDATES the executor against the independent spec (all 17 kernel fields +
    log are checked, so a silently mutated field would make the proof FAIL); `←` reconstructs.
  * `execFullA_createObligationA_iff_spec` — the obligation variant (same chained step), proved via the
    alias.

  * Non-vacuity: `…_rejects_unauthorized`, `…_rejects_negative`, `…_rejects_overdraft`,
    `…_rejects_dead_creator`, `…_rejects_id_reuse` — each forged input fails a guard leg ⇒ the executor
    returns `none` ⇒ no spec post-state exists. A spec that accepts everything would be worthless.

No `sorry`/`admit`/`axiom`/`native_decide`. `#assert_axioms` whitelists exactly
`{propext, Classical.choice, Quot.sound}` on every keystone.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.EscrowHoldingCreate

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (the `createEscrowKAsset` `if`, extracted as a `Prop`).

Exactly the five conjuncts `createEscrowKAsset` (`RecordKernel.lean:1490`) checks before it commits.
Note the AVAILABILITY conjunct reads the GENUINE per-asset ledger `k.bal creator asset` — NOT the
legacy scalar `balOf (k.cell creator)`; and the create gate checks CREATOR liveness but (faithfully to
dregg1) NOT recipient liveness, plus an ID-FRESHNESS leg unique to the side-table create. -/

/-- The full per-asset escrow-create admissibility guard `createEscrowKAsset` checks, as a `Prop`. -/
def createGuard (k : RecordKernelState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) : Prop :=
  authorizedB k.caps { actor := actor, src := creator, dst := recipient, amt := amount } = true
    ∧ 0 ≤ amount ∧ amount ≤ k.bal creator asset ∧ creator ∈ k.accounts
    ∧ ¬ (∃ r ∈ k.escrows, r.id = id)

/-- The unresolved `EscrowRecord` a create parks (its declarative form, mirroring the executor's
literal). Stated HERE so the spec's `escrows` clause does not reference the executor's body. -/
def parkedRecord (id : Nat) (creator recipient : CellId) (asset : AssetId) (amount : ℤ) :
    EscrowRecord :=
  { id := id, creator := creator, recipient := recipient,
    amount := amount, resolved := false, asset := asset }

/-! ## §2 — the post-state helper, validated DECLARATIVELY.

`createEscrowRawAsset` (`RecordKernel.lean:1471`) is the post-state the executor installs on commit. We
pin EXACTLY what it does — debit `(creator,asset)` by `amount` on the `bal` ledger (leaving every other
`(cell,asset)` untouched) and PREPEND the unresolved record onto `escrows` — so the spec's
`bal`/`escrows` clauses are genuine debit ∧ ledger-frame ∧ park-record, not blind trust. -/

/-- **`createEscrowKAsset_correct`** — the create post-state helper validated declaratively: the lock
debits `(creator,asset)` by `amount`, leaves every other `(cell,asset)` ledger entry untouched, and
prepends exactly the unresolved record onto the holding-store. -/
theorem createEscrowKAsset_correct (k : RecordKernelState) (id : Nat) (creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) :
    (createEscrowRawAsset k id creator recipient asset amount).bal creator asset
        = k.bal creator asset - amount
    ∧ (∀ c b, ¬ (c = creator ∧ b = asset) →
        (createEscrowRawAsset k id creator recipient asset amount).bal c b = k.bal c b)
    ∧ (createEscrowRawAsset k id creator recipient asset amount).escrows
        = parkedRecord id creator recipient asset amount :: k.escrows := by
  refine ⟨?_, ?_, rfl⟩
  · show recBalCreditCell k.bal creator asset (-amount) creator asset = k.bal creator asset - amount
    unfold recBalCreditCell
    rw [if_pos ⟨rfl, rfl⟩]; ring
  · intro c b hcd
    show recBalCreditCell k.bal creator asset (-amount) c b = k.bal c b
    unfold recBalCreditCell
    rw [if_neg hcd]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`EscrowHoldingCreateSpec` is the COMPLETE declarative post-state of a committed `createEscrowA`,
written INDEPENDENTLY of the executor: the guard holds; the post-`bal` ledger is the single-cell
single-asset debit; the post-`escrows` store is the prepended unresolved record; the chained `log`
advances by exactly `escrowReceiptA actor ::`; and EVERY OTHER state component — all 15 non-`bal`,
non-`escrows` RecordKernelState fields — is LITERALLY unchanged (the FRAME). No frame clause references
`createEscrowChainA`/`createEscrowKAsset`/`createEscrowRawAsset`'s executor terms. -/

/-- **The full-state declarative spec of a committed `createEscrowA`** — the INDEPENDENT reference
semantics. The guard holds (`createGuard`); the post-`bal` ledger debits `(creator,asset)` by `amount`
(`recBalCreditCell`, validated by `createEscrowKAsset_correct`); the post-`escrows` store is
`parkedRecord :: st.escrows`; the chained `log` is `escrowReceiptA actor :: st.log`; and every one of
the 15 other RecordKernelState components is unchanged. -/
def EscrowHoldingCreateSpec (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState) : Prop :=
  createGuard st.kernel id actor creator recipient asset amount
  ∧ st'.kernel.bal = recBalCreditCell st.kernel.bal creator asset (-amount)
  ∧ st'.kernel.escrows = parkedRecord id creator recipient asset amount :: st.kernel.escrows
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

/-- **`createEscrowChainA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
escrow-create step. `createEscrowChainA` commits a lock into `st'` IFF `st'` is EXACTLY the spec'd full
post-state. The `→` VALIDATES `createEscrowChainA` against the independent spec — all 17 kernel
components (`bal` + `escrows` + the 15 frame fields) AND the log are checked, so a silently mutated
field would make the proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem createEscrowChainA_iff_spec (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState) :
    createEscrowChainA st id actor creator recipient asset amount = some st'
      ↔ EscrowHoldingCreateSpec st id actor creator recipient asset amount st' := by
  unfold createEscrowChainA EscrowHoldingCreateSpec createGuard
  unfold createEscrowKAsset
  by_cases hg : authorizedB st.kernel.caps
        { actor := actor, src := creator, dst := recipient, amt := amount } = true
      ∧ 0 ≤ amount ∧ amount ≤ st.kernel.bal creator asset ∧ creator ∈ st.kernel.accounts
      ∧ ¬ (∃ r ∈ st.kernel.escrows, r.id = id)
  · rw [if_pos hg]
    simp only [createEscrowRawAsset, parkedRecord]
    constructor
    · intro h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hbal, hesc, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      -- reconstruct st' from the spec: its kernel matches the create post-state field-by-field,
      -- and its log matches `escrowReceiptA actor :: st.log`.
      obtain ⟨k', l'⟩ := st'
      obtain ⟨acc, cell, caps, esc, nul, rev, com, bal, q, sw, sc, fac, lc, dc, dg, dgs, sb⟩ := k'
      simp only at hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hbal hesc hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execFullA_createEscrowA_iff_spec` — the UNIFIED-ACTION executor corner.** `execFullA` dispatches
`.createEscrowA …` to `createEscrowChainA s …`, so committing the unified action into `st'` is EXACTLY
the full-state spec. This is the variant-level executor⟺spec. -/
theorem execFullA_createEscrowA_iff_spec (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (st' : RecChainedState) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = some st'
      ↔ EscrowHoldingCreateSpec st id actor creator recipient asset amount st' := by
  show createEscrowChainA st id actor creator recipient asset amount = some st'
        ↔ EscrowHoldingCreateSpec st id actor creator recipient asset amount st'
  exact createEscrowChainA_iff_spec st id actor creator recipient asset amount st'

/-- **`execFullA_createObligationA_iff_spec` — the OBLIGATION alias.** `execFullA` dispatches
`.createObligationA id actor obligor beneficiary asset stake` to the SAME chained step
`createEscrowChainA s id actor obligor beneficiary asset stake` (obligor=creator, beneficiary=recipient,
stake=amount), so the obligation variant satisfies the identical full-state create spec. -/
theorem execFullA_createObligationA_iff_spec (st : RecChainedState) (id : Nat)
    (actor obligor beneficiary : CellId) (asset : AssetId) (stake : ℤ) (st' : RecChainedState) :
    execFullA st (.createObligationA id actor obligor beneficiary asset stake) = some st'
      ↔ EscrowHoldingCreateSpec st id actor obligor beneficiary asset stake st' := by
  show createEscrowChainA st id actor obligor beneficiary asset stake = some st'
        ↔ EscrowHoldingCreateSpec st id actor obligor beneficiary asset stake st'
  exact createEscrowChainA_iff_spec st id actor obligor beneficiary asset stake st'

/-! ## §4 — the post-state facts a committed step produces (debit / park / ledger-frame corollaries).

These read off `EscrowHoldingCreateSpec` + `createEscrowKAsset_correct` to expose the genuine effect
(the per-asset debit at `(creator,asset)`, the parked record, the untouched other ledger entries). -/

/-- **`escrowCreate_debit`** — a committed create debits the creator's asset-`asset` ledger by `amount`
(the value parked off-ledger into the holding-store). -/
theorem escrowCreate_debit (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.createEscrowA id actor creator recipient asset amount) = some st') :
    st'.kernel.bal creator asset = st.kernel.bal creator asset - amount := by
  obtain ⟨_, hbal, _⟩ := (execFullA_createEscrowA_iff_spec st id actor creator recipient asset amount st').mp h
  rw [hbal]
  exact (createEscrowKAsset_correct st.kernel id creator recipient asset amount).1

/-- **`escrowCreate_other_untouched`** — a committed create leaves every other `(cell,asset)` ledger
entry untouched (the per-asset ledger frame). -/
theorem escrowCreate_other_untouched (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.createEscrowA id actor creator recipient asset amount) = some st')
    (c : CellId) (b : AssetId) (hcd : ¬ (c = creator ∧ b = asset)) :
    st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨_, hbal, _⟩ := (execFullA_createEscrowA_iff_spec st id actor creator recipient asset amount st').mp h
  rw [hbal]
  exact (createEscrowKAsset_correct st.kernel id creator recipient asset amount).2.1 c b hcd

/-- **`escrowCreate_parks_record`** — a committed create prepends exactly the unresolved record onto
the holding-store (the off-ledger lock). -/
theorem escrowCreate_parks_record (st : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (st' : RecChainedState)
    (h : execFullA st (.createEscrowA id actor creator recipient asset amount) = some st') :
    st'.kernel.escrows = parkedRecord id creator recipient asset amount :: st.kernel.escrows := by
  obtain ⟨_, _, hesc, _⟩ := (execFullA_createEscrowA_iff_spec st id actor creator recipient asset amount st').mp h
  exact hesc

/-! ## §5 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Here each forged input
fails a guard conjunct ⇒ `execFullA st (.createEscrowA …) = none` ⇒ no spec post-state exists. -/

/-- **`escrowCreate_rejects_unauthorized` — PROVED.** An unauthorized actor's create does NOT commit
(the AUTHORITY leg fails) ⇒ no `st'` satisfies the spec. -/
theorem escrowCreate_rejects_unauthorized (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : authorizedB st.kernel.caps
        { actor := actor, src := creator, dst := recipient, amt := amount } = false) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = none := by
  show createEscrowChainA st id actor creator recipient asset amount = none
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]

/-- **`escrowCreate_rejects_negative` — PROVED.** A negative-amount create does NOT commit (the
NON-NEGATIVITY leg fails) — no value can be conjured by a negative lock. -/
theorem escrowCreate_rejects_negative (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ 0 ≤ amount) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = none := by
  show createEscrowChainA st id actor creator recipient asset amount = none
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, h, _⟩; exact hbad h)]

/-- **`escrowCreate_rejects_overdraft` — PROVED.** A lock of more than the creator holds in asset
`asset` (`¬ amount ≤ k.bal creator asset`) does NOT commit (the AVAILABILITY leg fails). -/
theorem escrowCreate_rejects_overdraft (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ¬ amount ≤ st.kernel.bal creator asset) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = none := by
  show createEscrowChainA st id actor creator recipient asset amount = none
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, h, _⟩; exact hbad h)]

/-- **`escrowCreate_rejects_dead_creator` — PROVED.** A lock out of a non-account creator does NOT
commit (the CREATOR-LIVENESS leg fails). -/
theorem escrowCreate_rejects_dead_creator (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : creator ∉ st.kernel.accounts) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = none := by
  show createEscrowChainA st id actor creator recipient asset amount = none
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact hbad h)]

/-- **`escrowCreate_rejects_id_reuse` — PROVED.** A create whose `id` is ALREADY in use does NOT commit
(the ID-FRESHNESS leg fails) — locks cannot collide on the holding-store key. -/
theorem escrowCreate_rejects_id_reuse (st : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (hbad : ∃ r ∈ st.kernel.escrows, r.id = id) :
    execFullA st (.createEscrowA id actor creator recipient asset amount) = none := by
  show createEscrowChainA st id actor creator recipient asset amount = none
  unfold createEscrowChainA createEscrowKAsset
  rw [if_neg (by rintro ⟨_, _, _, _, h⟩; exact h hbad)]

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms createEscrowKAsset_correct
#assert_axioms createEscrowChainA_iff_spec
#assert_axioms execFullA_createEscrowA_iff_spec
#assert_axioms execFullA_createObligationA_iff_spec
#assert_axioms escrowCreate_debit
#assert_axioms escrowCreate_other_untouched
#assert_axioms escrowCreate_parks_record
#assert_axioms escrowCreate_rejects_unauthorized
#assert_axioms escrowCreate_rejects_negative
#assert_axioms escrowCreate_rejects_overdraft
#assert_axioms escrowCreate_rejects_dead_creator
#assert_axioms escrowCreate_rejects_id_reuse

end Dregg2.Circuit.Spec.EscrowHoldingCreate
