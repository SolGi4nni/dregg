/-
# Dregg2.Circuit.Spec.balancemovement — INDEPENDENT full-state spec + executor⟺spec for the
`balance-movement` effect family (the `FullActionA.balanceA` variant).

This is a LEAF module (imported by nothing; gated standalone). It is the `Transfer.lean` reference
pattern (`TransferSpec` + `recKExec_iff_spec` + `recTransfer_correct`) re-derived INDEPENDENTLY for
the per-asset value-movement effect that the unified action executor `execFullA` actually dispatches:

    execFullA s (.balanceA t a) = recCexecAsset s t a              -- TurnExecutorFull.lean:3480
    recCexecAsset s t a         = match recKExecAsset s.kernel t a with
                                  | some k' => some { kernel := k', log := t :: s.log } | none => none

`recKExecAsset` (`RecordKernel.lean:719`) is the EXECUTABLE per-asset transition over the GENUINE
`bal : CellId → AssetId → ℤ` ledger (NOT the legacy scalar `balOf (cell …)` slice). Its admissibility
guard is the conjunction:

    authorizedB caps t = true       -- (1) AUTHORITY: actor held a cap over `src`
  ∧ 0 ≤ t.amt                        -- (2) NON-NEGATIVITY
  ∧ t.amt ≤ k.bal t.src a            -- (3) AVAILABILITY *in asset `a`*  (per-asset, NOT balOf cell)
  ∧ t.src ≠ t.dst                    -- (4) DISTINCTNESS
  ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts   -- (5),(6) LIVENESS

and on commit it rewrites ONLY the `bal` ledger's `a` column (`recTransferBal`), debiting `src` and
crediting `dst`; every other (cell,asset) pair AND every other RecordKernelState field is untouched,
while the chained log gets `t` prepended.

## What is proved (the apex reference truth, BOTH directions)

  * `BalanceMovementSpec st t a st'` — the INDEPENDENT declarative full-state post-condition: the
    admissibility guard, the EXACT post-`bal` ledger (`recTransferBal`), AND the FRAME — every one of
    the 17 RecordKernelState components except `bal` LITERALLY unchanged (`accounts cell caps escrows
    nullifiers revoked commitments queues swiss slotCaveats factories lifecycle deathCert delegate
    delegations sealedBoxes`) AND the RecChainedState `log` advanced by exactly `t ::`. No frame clause
    mentions the executor. Missing ANY field reintroduces a ghost — all 17 + log are enumerated.

  * `execFullA_balanceA_iff_spec` — execFullA ⟺ spec (BOTH directions). The `→` VALIDATES the
    executor against the independent spec (all 17 kernel fields + log are checked, so a silently
    mutated `caps`/`nullifiers`/… would make the proof FAIL); the `←` reconstructs the committed
    state. This is the executor corner of the spec⟺executor triangle for value-movement.

  * `recCexecAsset_iff_spec` — the same ⟺ stated directly on the chained per-asset executor
    `recCexecAsset` (the arm `execFullA` dispatches to), for downstream reuse.

  * `recTransferBal_correct` — the post-`bal` ledger helper validated DECLARATIVELY (debit at
    (src,a), credit at (dst,a), every other (cell,asset) untouched), so the spec's
    `bal = recTransferBal …` clause encodes debit ∧ credit ∧ ledger-frame.

  * Non-vacuity: `…_rejects_unauthorized`, `…_rejects_overdraft`, `…_rejects_self`,
    `…_rejects_dead_src` — each forged input fails a guard leg ⇒ the executor returns `none` ⇒ no
    spec post-state exists. A spec that accepts everything would be worthless.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.BalanceMovement

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

/-! ## §1 — the admissibility guard (the `recKExecAsset` `if`, extracted as a `Prop`).

Exactly the six conjuncts `recKExecAsset` (`RecordKernel.lean:719`) checks before it commits. Note
the AVAILABILITY conjunct reads the GENUINE per-asset ledger `k.bal t.src a` — NOT the legacy scalar
`balOf (k.cell t.src)`. -/

/-- The full per-asset admissibility guard `recKExecAsset` / `recCexecAsset` checks, as a `Prop`. -/
def admitGuardA (k : RecordKernelState) (t : Turn) (a : AssetId) : Prop :=
  authorizedB k.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ k.bal t.src a
    ∧ t.src ≠ t.dst ∧ t.src ∈ k.accounts ∧ t.dst ∈ k.accounts
    ∧ acceptsEffects k t.dst = true

/-! ## §2 — the post-`bal` ledger helper, validated DECLARATIVELY.

`recTransferBal` (`RecordKernel.lean:708`) is the post-ledger the executor installs. We pin EXACTLY
what it does — debit `(src,a)`, credit `(dst,a)`, leave every other `(cell,asset)` untouched — so the
spec's `bal = recTransferBal …` clause is genuine debit ∧ credit ∧ ledger-frame, not blind trust. -/

/-- **`recTransferBal_correct`** — the per-asset ledger helper validated declaratively: a movement of
asset `a` debits `(src,a)` by `amt`, credits `(dst,a)` by `amt`, and leaves every other
`(cell, asset)` pair untouched (other cells in column `a`, AND every other asset column entirely). -/
theorem recTransferBal_correct (bal : CellId → AssetId → ℤ) (src dst : CellId) (a : AssetId) (amt : ℤ)
    (hne : src ≠ dst) :
    recTransferBal bal src dst a amt src a = bal src a - amt
    ∧ recTransferBal bal src dst a amt dst a = bal dst a + amt
    ∧ (∀ c b, ¬ (c = src ∧ b = a) → ¬ (c = dst ∧ b = a) → recTransferBal bal src dst a amt c b = bal c b) := by
  refine ⟨?_, ?_, ?_⟩
  · show (if a = a then (if src = src then bal src a - amt
            else if src = dst then bal src a + amt else bal src a) else bal src a) = bal src a - amt
    rw [if_pos rfl, if_pos rfl]
  · have hdne : dst ≠ src := fun h => hne h.symm
    show (if a = a then (if dst = src then bal dst a - amt
            else if dst = dst then bal dst a + amt else bal dst a) else bal dst a) = bal dst a + amt
    rw [if_pos rfl, if_neg hdne, if_pos rfl]
  · intro c b hcs hcd
    unfold recTransferBal
    by_cases hb : b = a
    · subst hb
      rw [if_pos rfl]
      have hcsrc : c ≠ src := fun h => hcs ⟨h, rfl⟩
      have hcdst : c ≠ dst := fun h => hcd ⟨h, rfl⟩
      rw [if_neg hcsrc, if_neg hcdst]
    · rw [if_neg hb]

/-! ## §3 — FULL-STATE SEMANTIC SPEC (the INDEPENDENT reference) + executor⟺spec.

`BalanceMovementSpec` is the COMPLETE declarative post-state of a committed `balanceA`, written
INDEPENDENTLY of the executor: the guard holds; the post-`bal` ledger is the debit/credit movement;
the chained log advances by exactly `t ::`; and EVERY OTHER state component — all 16 non-`bal`
RecordKernelState fields — is LITERALLY unchanged (the FRAME). No frame clause references
`recCexecAsset`/`recKExecAsset`/`recTransferBal`'s executor terms. -/

/-- **The full-state declarative spec of a committed `balanceA`** — the INDEPENDENT reference
semantics. The guard holds (`admitGuardA`); the post-`bal` ledger is the per-asset debit/credit
(`recTransferBal`, validated by `recTransferBal_correct`); the chained `log` is `t :: st.log`; and
every one of the 16 non-`bal` RecordKernelState components is unchanged. -/
def BalanceMovementSpec (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState) : Prop :=
  admitGuardA st.kernel t a
  ∧ st'.kernel.bal = recTransferBal st.kernel.bal t.src t.dst a t.amt
  ∧ st'.log = t :: st.log
  -- THE FRAME: every non-`bal` RecordKernelState field, literally unchanged (16 of them).
  ∧ st'.kernel.accounts = st.kernel.accounts
  ∧ st'.kernel.cell = st.kernel.cell
  ∧ st'.kernel.caps = st.kernel.caps
  ∧ st'.kernel.nullifiers = st.kernel.nullifiers
  ∧ st'.kernel.revoked = st.kernel.revoked
  ∧ st'.kernel.commitments = st.kernel.commitments
  ∧ st'.kernel.slotCaveats = st.kernel.slotCaveats
  ∧ st'.kernel.factories = st.kernel.factories
  ∧ st'.kernel.lifecycle = st.kernel.lifecycle
  ∧ st'.kernel.deathCert = st.kernel.deathCert
  ∧ st'.kernel.delegate = st.kernel.delegate
  ∧ st'.kernel.delegations = st.kernel.delegations
  ∧ st'.kernel.delegationEpoch = st.kernel.delegationEpoch
  ∧ st'.kernel.delegationEpochAt = st.kernel.delegationEpochAt
  ∧ st'.kernel.heaps = st.kernel.heaps

/-- **`recCexecAsset_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions)** on the chained
per-asset executor. `recCexecAsset` commits a movement into `st'` IFF `st'` is EXACTLY the spec'd full
post-state. The `→` VALIDATES `recCexecAsset` against the independent spec — all 17 kernel components
(`bal` + the 16 frame fields) AND the log are checked, so a silently mutated field would make the
proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem recCexecAsset_iff_spec (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState) :
    recCexecAsset st t a = some st' ↔ BalanceMovementSpec st t a st' := by
  unfold recCexecAsset BalanceMovementSpec admitGuardA
  unfold recKExecAsset
  by_cases hadm : acceptsEffects st.kernel t.dst
  · by_cases hg : authorizedB st.kernel.caps t = true ∧ 0 ≤ t.amt ∧ t.amt ≤ st.kernel.bal t.src a
        ∧ t.src ≠ t.dst ∧ t.src ∈ st.kernel.accounts ∧ t.dst ∈ st.kernel.accounts
    · rw [if_pos hadm, if_pos hg]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        subst h
        rcases hg with ⟨ha, hnn, havail, hne, hsrc, hdst⟩
        exact ⟨⟨ha, hnn, havail, hne, hsrc, hdst, hadm⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
               rfl, rfl, rfl⟩
      · rintro ⟨hguard, hbal, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
        obtain ⟨k', l'⟩ := st'
        obtain ⟨acc, cell, caps, nul, rev, com, bal, sc, fac, lc, dc, dg, dgs, dge, dgea, hp⟩ := k'
        simp only at hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        subst hbal hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
        rfl
    · rw [if_pos hadm, if_neg hg]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨hguard, _⟩
        rcases hguard with ⟨ha, hnn, havail, hne, hsrc, hdst, _⟩
        exact absurd ⟨ha, hnn, havail, hne, hsrc, hdst⟩ hg
  · rw [if_neg hadm]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hguard, _⟩; rcases hguard with ⟨_, _, _, _, _, _, hadm'⟩; exact absurd hadm' hadm

/-- **`execFullA_balanceA_iff_spec` — the UNIFIED-ACTION executor corner.** The action executor
`execFullA` dispatches `.balanceA t a` to `recCexecAsset s t a`, so committing the unified action into
`st'` is EXACTLY the full-state spec. This is the variant-level executor⟺spec. -/
theorem execFullA_balanceA_iff_spec (st : RecChainedState) (t : Turn) (a : AssetId)
    (st' : RecChainedState) :
    execFullA st (.balanceA t a) = some st' ↔ BalanceMovementSpec st t a st' := by
  show recCexecAsset st t a = some st' ↔ BalanceMovementSpec st t a st'
  exact recCexecAsset_iff_spec st t a st'

/-! ## §4 — the post-state facts a committed step produces (the debit/credit/conserve corollaries).

These read off `BalanceMovementSpec` + `recTransferBal_correct` to expose the genuine value movement
(debit/credit at `(src,a)`/`(dst,a)`) — the conserved-slice projection of the full spec. -/

/-- **`balanceMovement_debit`** — a committed movement debits the source's asset-`a` balance by `amt`. -/
theorem balanceMovement_debit (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState)
    (h : execFullA st (.balanceA t a) = some st') :
    st'.kernel.bal t.src a = st.kernel.bal t.src a - t.amt := by
  obtain ⟨hg, hbal, _⟩ := (execFullA_balanceA_iff_spec st t a st').mp h
  rw [hbal]
  exact (recTransferBal_correct st.kernel.bal t.src t.dst a t.amt hg.2.2.2.1).1

/-- **`balanceMovement_credit`** — a committed movement credits the destination's asset-`a` balance
by `amt`. -/
theorem balanceMovement_credit (st : RecChainedState) (t : Turn) (a : AssetId) (st' : RecChainedState)
    (h : execFullA st (.balanceA t a) = some st') :
    st'.kernel.bal t.dst a = st.kernel.bal t.dst a + t.amt := by
  obtain ⟨hg, hbal, _⟩ := (execFullA_balanceA_iff_spec st t a st').mp h
  rw [hbal]
  exact (recTransferBal_correct st.kernel.bal t.src t.dst a t.amt hg.2.2.2.1).2.1

/-- **`balanceMovement_other_untouched`** — a committed movement leaves every other `(cell,asset)`
ledger entry untouched (the per-asset ledger frame). -/
theorem balanceMovement_other_untouched (st : RecChainedState) (t : Turn) (a : AssetId)
    (st' : RecChainedState) (h : execFullA st (.balanceA t a) = some st')
    (c : CellId) (b : AssetId) (hcs : ¬ (c = t.src ∧ b = a)) (hcd : ¬ (c = t.dst ∧ b = a)) :
    st'.kernel.bal c b = st.kernel.bal c b := by
  obtain ⟨_, hbal, _⟩ := (execFullA_balanceA_iff_spec st t a st').mp h
  rw [hbal]
  exact (recTransferBal_correct st.kernel.bal t.src t.dst a t.amt (by
    obtain ⟨hg, _⟩ := (execFullA_balanceA_iff_spec st t a st').mp h; exact hg.2.2.2.1)).2.2 c b hcs hcd

/-! ## §5 — NON-VACUITY: the executor REJECTS bad inputs (each guard leg, fail-closed).

A spec a worthless executor could meet (accept everything) would be vacuous. Here each forged input
fails a guard conjunct ⇒ `execFullA st (.balanceA t a) = none` ⇒ no spec post-state exists. -/

/-- **`balanceMovement_rejects_unauthorized`.** An unauthorized actor's movement does NOT
commit (the AUTHORITY leg fails) ⇒ no `st'` satisfies the spec. -/
theorem balanceMovement_rejects_unauthorized (st : RecChainedState) (t : Turn) (a : AssetId)
    (hbad : authorizedB st.kernel.caps t = false) :
    execFullA st (.balanceA t a) = none := by
  show recCexecAsset st t a = none
  unfold recCexecAsset recKExecAsset
  by_cases hadm : acceptsEffects st.kernel t.dst
  · rw [if_pos hadm]
    rw [if_neg (by rw [hbad]; rintro ⟨h, _⟩; exact absurd h (by simp))]
  · rw [if_neg hadm]

/-- **`balanceMovement_rejects_overdraft`.** A movement of more than the source holds in
asset `a` (`¬ t.amt ≤ k.bal t.src a`) does NOT commit (the AVAILABILITY leg fails). -/
theorem balanceMovement_rejects_overdraft (st : RecChainedState) (t : Turn) (a : AssetId)
    (hbad : ¬ t.amt ≤ st.kernel.bal t.src a) :
    execFullA st (.balanceA t a) = none := by
  show recCexecAsset st t a = none
  unfold recCexecAsset recKExecAsset
  by_cases hadm : acceptsEffects st.kernel t.dst
  · rw [if_pos hadm]
    rw [if_neg (by rintro ⟨_, _, h, _⟩; exact hbad h)]
  · rw [if_neg hadm]

/-- **`balanceMovement_rejects_self`.** A self-movement (`src = dst`) does NOT commit (the
DISTINCTNESS leg fails) — no value can be conjured by moving to oneself. -/
theorem balanceMovement_rejects_self (st : RecChainedState) (t : Turn) (a : AssetId)
    (hbad : t.src = t.dst) :
    execFullA st (.balanceA t a) = none := by
  show recCexecAsset st t a = none
  unfold recCexecAsset recKExecAsset
  by_cases hadm : acceptsEffects st.kernel t.dst
  · rw [if_pos hadm]
    rw [if_neg (by rintro ⟨_, _, _, h, _⟩; exact h hbad)]
  · rw [if_neg hadm]

/-- **`balanceMovement_rejects_dead_src`.** A movement out of a non-account source does NOT
commit (the source-LIVENESS leg fails). -/
theorem balanceMovement_rejects_dead_src (st : RecChainedState) (t : Turn) (a : AssetId)
    (hbad : t.src ∉ st.kernel.accounts) :
    execFullA st (.balanceA t a) = none := by
  show recCexecAsset st t a = none
  unfold recCexecAsset recKExecAsset
  by_cases hadm : acceptsEffects st.kernel t.dst
  · rw [if_pos hadm]
    rw [if_neg (by rintro ⟨_, _, _, _, h, _⟩; exact hbad h)]
  · rw [if_neg hadm]

/-- **`balanceMovement_rejects_sealed_dst` (R1).** A transfer into a non-Live destination
(Sealed/Destroyed ⇒ `acceptsEffects = false`) does NOT commit. -/
theorem balanceMovement_rejects_sealed_dst (st : RecChainedState) (t : Turn) (a : AssetId)
    (hbad : acceptsEffects st.kernel t.dst = false) :
    execFullA st (.balanceA t a) = none := by
  show recCexecAsset st t a = none
  unfold recCexecAsset
  rw [if_neg (by intro h; rw [h] at hbad; cases hbad)]

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms recTransferBal_correct
#assert_axioms recCexecAsset_iff_spec
#assert_axioms execFullA_balanceA_iff_spec
#assert_axioms balanceMovement_debit
#assert_axioms balanceMovement_credit
#assert_axioms balanceMovement_other_untouched
#assert_axioms balanceMovement_rejects_unauthorized
#assert_axioms balanceMovement_rejects_overdraft
#assert_axioms balanceMovement_rejects_self
#assert_axioms balanceMovement_rejects_dead_src
#assert_axioms balanceMovement_rejects_sealed_dst

end Dregg2.Circuit.Spec.BalanceMovement
