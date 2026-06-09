/-
# Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow — the releaseEscrow (escrow-holding-RELEASE) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

This is the escrow-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `releaseEscrowA` (and its `slashObligationA` dispatch-alias). Universe A
(`Spec/escrowholdingrelease.lean`) carries the FULL-state soundness `execFullA_releaseEscrow_iff_spec ⇒
ReleaseEscrowSpec`: a committed release CREDITS the per-asset ledger `bal` at `(r.recipient, r.asset)`
by `+r.amount` (`recBalCreditCell … r.amount` — the parked value SETTLED to the recipient, the honest
contrast with refund/cancel which credit the CREATOR), marks the parked record resolved
(`markResolved … id`), advances the log, and FREEZES the other 15 kernel fields.

## What the EffectVM IR (a 14-column state block + GROUP-4 commitment) DOES support for releaseEscrow

The conserved `bal` move is a SINGLE-cell single-asset CREDIT (`recBalCreditCell … (+amount)`): on the
EffectVM row this is the RECIPIENT cell's `state.BALANCE_LO` limb moving UP by `amount`. This is EXACTLY
the transfer-row CREDIT leg (`direction = 0`, `signedMove = +amount`), so the IR carries it totally —
and the GROUP-4 commitment chain binds the whole after-state block into `state_commit` as for transfer.
(The credited CELL is the record's `recipient`, distinguishing release from refund/cancel — that is the
encoding choice at the connector, not a row gate; the row carries one bare credited limb.)

The ONE column difference from transfer: releaseEscrow's executor does NOT tick the cell's nonce
(`settleEscrowRawAsset` rewrites only `bal` and `escrows`), whereas the transfer EffectVM row ticks
`+1`. So the releaseEscrow descriptor FREEZES the nonce (`gNonceFreeze`), matching the executor.

## THE IR-EXTENSION FLAG (the escrows set-membership / resolve leg)

`ReleaseEscrowSpec` ALSO marks the parked record resolved (`escrows := markResolved … id`) — a
SET-MEMBERSHIP / list-digest mutation. The EffectVM 14-column state block has NO escrow-root column, and
the GROUP-4 hash-sites absorb NONE of the escrows list. So the IR as it stands CANNOT bind the escrows
resolve into `state_commit`.

  ⇒ **needs IR extension: an escrows-list-root column in the EffectVM state block (a 15th data column,
     or repurposing one named field as `ESCROW_ROOT`) absorbed by a new hash-site, so the
     `markResolved` update is bound into the published `state_commit`.** Universe A binds it via the
     `escrows` list equality; the EffectVM row has no counterpart column. This module proves what the
     IR DOES support (balance credit + the 14-column commitment) and reports the escrows resolve as
     out-of-IR — NOT papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.escrowholdingrelease
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   site0 site1 site2 site3 transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The releaseEscrow selector + the credit parameter. -/

/-- The escrow-holding-release selector column index. -/
def SEL_RELEASE_ESCROW : Nat := 7

/-- The release row is an escrow-release row: `s_release_escrow = 1`, `s_noop = 0`. -/
def IsReleaseEscrowRow (env : VmRowEnv) : Prop :=
  env.loc SEL_RELEASE_ESCROW = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The releaseEscrow per-row gate bodies (credit + full frame freeze, term-for-term). -/

/-- Balance-lo CREDIT body: `new_bal_lo − old_bal_lo − amount`. -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) (ePrm param.AMOUNT))

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted releaseEscrow descriptor. -/

/-- The escrow-holding-release AIR identity. -/
def releaseEscrowVmAirName : String := "dregg-effectvm-releaseescrow-v1"

/-- The escrow-release per-row gates: balance credit, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def releaseEscrowRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`releaseEscrowVmDescriptor`** — the releaseEscrow effect's concrete EffectVM circuit: the per-row
credit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED) and the 2 balance-limb range checks. -/
def releaseEscrowVmDescriptor : EffectVmDescriptor :=
  { name := releaseEscrowVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := releaseEscrowRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The releaseEscrow ROW INTENT (the independent faithfulness target). -/

/-- **`ReleaseEscrowRowIntent env`** — the intended escrow-release move: the new balance is the old PLUS
`amount` (the settle credit), the hi limb / nonce / whole frame fixed. This is the EffectVM-row
projection of `ReleaseEscrowSpec`'s `bal` credit + frame freeze on the recipient cell. -/
def ReleaseEscrowRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`releaseEscrowVm_faithful`.** On an escrow-release row, the emitted descriptor's per-row gates all
hold IFF `ReleaseEscrowRowIntent` holds. -/
theorem releaseEscrowVm_faithful (env : VmRowEnv) :
    (∀ c ∈ releaseEscrowRowGates, c.holdsVm env false false) ↔ ReleaseEscrowRowIntent env := by
  unfold releaseEscrowRowGates gFieldPassAll ReleaseEscrowRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linarith [hLo]
    · linarith [hHi]
    · linarith [hNon]
    · linarith [hCap]
    · linarith [hRes]
    · intro i hi
      have := hFld i hi
      simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
      linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a wrong-output release row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A release row whose post-state is NOT the intent move does NOT satisfy the
per-row gates. -/
theorem releaseEscrowVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ ReleaseEscrowRowIntent env) :
    ¬ (∀ c ∈ releaseEscrowRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((releaseEscrowVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A release row whose post-`bal_lo` is NOT the credit has no
satisfying gate set — the `gBalLoCredit` gate alone rejects it (UNSAT). -/
theorem releaseEscrowVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- The release parameters carried in the param block (only `amount` matters). -/
structure ReleaseParams where
  amount : ℤ

/-- `RowEncodesRelease env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition. -/
def RowEncodesRelease (env : VmRowEnv) (pre : CellState) (p : ReleaseParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = p.amount
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellReleaseSpec pre p post`** — the per-cell FULL-state release spec: the moved cell's `balLo`
rises by `amount`, the nonce is FROZEN, and the WHOLE frame is LITERALLY unchanged. This is the
EffectVM-row projection of `ReleaseEscrowSpec`'s `bal` credit + frame freeze on the recipient cell. -/
def CellReleaseSpec (pre : CellState) (p : ReleaseParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo + p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesRelease`, `ReleaseEscrowRowIntent` IS the structured
`CellReleaseSpec`. -/
theorem intent_to_cellReleaseSpec (env : VmRowEnv) (pre post : CellState) (p : ReleaseParams)
    (henc : RowEncodesRelease env pre p post) (hint : ReleaseEscrowRowIntent env) :
    CellReleaseSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.AMOUNT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding (REUSED). -/

/-- **`releaseEscrowDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under the
`RowEncodesRelease` decoding, forces the structured per-cell `CellReleaseSpec` AND publishes the
post-commit as `PI[NEW_COMMIT]`. -/
theorem releaseEscrowDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : ReleaseParams)
    (henc : RowEncodesRelease env pre p post)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptor env true true) :
    CellReleaseSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ releaseEscrowRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ releaseEscrowVmDescriptor.constraints := by
      unfold releaseEscrowVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold releaseEscrowRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (releaseEscrowVm_faithful env).mp hgates'
  refine ⟨intent_to_cellReleaseSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ releaseEscrowVmDescriptor.constraints := by
      unfold releaseEscrowVmDescriptor
      simp only [List.mem_append]
      exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §8 — The anti-ghost commitment tooth (REUSED from the transfer keystone, hash sites identical). -/

/-- **`releaseEscrowDescriptor_commit_binds_state`** — the keystone anti-ghost for releaseEscrow: two
descriptor-satisfying release rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell of the settled
post-state. -/
theorem releaseEscrowDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash releaseEscrowVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash releaseEscrowVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash releaseEscrowVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ releaseEscrowVmDescriptor.constraints := by
        unfold releaseEscrowVmDescriptor
        simp only [List.mem_append]
        exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by
    rw [hc e₁ hsat₁, hc e₂ hsat₂, hpub]
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §9 — CONNECTOR to universe-A: `CellReleaseSpec` IS `ReleaseEscrowSpec`'s per-cell bal image.

`execFullA_releaseEscrow_iff_spec ⇒ ReleaseEscrowSpec` carries the `bal` credit at `(r.recipient,
r.asset)` for the FOUND record `r`. We project the RECIPIENT cell of the kernel `bal` ledger into the
keystone `CellState` (the conserved `balLo` limb reads the per-asset entry `bal r.recipient r.asset`;
the EffectVM limbs with no universe-A analogue are `0`, FROZEN), and prove the recipient cell's
projection satisfies `CellReleaseSpec` EXACTLY (the credit + nonce-freeze + frame-freeze).

The DIVERGENCE pattern: the escrows-resolve is NOT in this per-cell projection (no escrow column in the
EffectVM block — the §IR-extension flag). And `ReleaseEscrowSpec`'s `bal` clause is a WHOLE-function
equality; the per-cell projection reads the `(r.recipient, r.asset)` entry of it (extracted via
`release_credits_recipient`). Note the credited cell is the record's RECIPIENT (distinguishing release
from refund/cancel, which credit the CREATOR). -/

open Dregg2.Exec (RecordKernelState RecChainedState CellId AssetId EscrowRecord)
open Dregg2.Circuit.Spec.EscrowHoldingRelease
  (ReleaseEscrowSpec releaseGuard release_credits_recipient execFullA_releaseEscrow_iff_spec)
open Dregg2.Exec.TurnExecutorFull (execFullA)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). -/
def cellProjRelease (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_release_credit`** — the recipient cell's projected `(r.recipient, r.asset)` ledger entry,
across a committed release (`execFullA … (.releaseEscrowA id actor) = some st'`), satisfies the
keystone's `CellReleaseSpec` EXACTLY for the FOUND record `r`: `balLo` rises by `r.amount`;
balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So `CellReleaseSpec` IS
`ReleaseEscrowSpec`'s per-cell `bal` image — NOT a fourth spec. The found record `r` (its
`recipient`/`asset`/`amount`) is the witness the executor's `releaseGuard` binds. -/
theorem unify_release_credit (st st' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execFullA st (.releaseEscrowA id actor) = some st') :
    ∃ r : EscrowRecord, releaseGuard st id actor r ∧
      CellReleaseSpec (cellProjRelease st.kernel.bal r.recipient r.asset) ⟨r.amount⟩
        (cellProjRelease st'.kernel.bal r.recipient r.asset) := by
  have hspec := (execFullA_releaseEscrow_iff_spec st id actor st').mp h
  obtain ⟨r, hg, hcredit⟩ := release_credits_recipient st id actor st' hspec
  refine ⟨r, hg, ?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal r.recipient r.asset = st.kernel.bal r.recipient r.asset + r.amount
  exact hcredit

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_release`** — a satisfying run of the runnable descriptor encoding
the recipient cell of a committed release agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre + r.amount) equals the executor's settle-credited
`bal r.recipient r.asset`, and the frozen frame agrees. The escrows-resolve is out-of-IR (§IR flag). -/
theorem descriptor_agrees_with_executor_release
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id : Nat) (actor : CellId) (r : EscrowRecord) (post : CellState)
    (hg : releaseGuard st id actor r)
    (hcredit : st'.kernel.bal r.recipient r.asset = st.kernel.bal r.recipient r.asset + r.amount)
    (henc : RowEncodesRelease env (cellProjRelease st.kernel.bal r.recipient r.asset) ⟨r.amount⟩ post)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptor env true true) :
    post.balLo = (cellProjRelease st'.kernel.bal r.recipient r.asset).balLo
    ∧ post.balHi = (cellProjRelease st'.kernel.bal r.recipient r.asset).balHi
    ∧ (∀ i, post.fields i = (cellProjRelease st'.kernel.bal r.recipient r.asset).fields i)
    ∧ post.capRoot = (cellProjRelease st'.kernel.bal r.recipient r.asset).capRoot
    ∧ post.reserved = (cellProjRelease st'.kernel.bal r.recipient r.asset).reserved := by
  obtain ⟨hcirc, _⟩ := releaseEscrowDescriptor_full_sound hash env
    (cellProjRelease st.kernel.bal r.recipient r.asset) post ⟨r.amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show post.balLo = st'.kernel.bal r.recipient r.asset
    rw [hcLo]; show st.kernel.bal r.recipient r.asset + r.amount = _; rw [hcredit]
  · rw [hcHi]; rfl
  · intro i; rw [hcF i]; rfl
  · rw [hcCap]; rfl
  · rw [hcRes]; rfl

/-! ## §11 — NON-VACUITY: a concrete release row realizes the intent; a forged one is rejected. -/

/-- A concrete release row: `bal_lo 100 → 105` (credit 5), nonce 5 → 5 (FROZEN), frame fixed at 0. -/
def goodReleaseRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_RELEASE_ESCROW then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 105
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.AMOUNT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodReleaseRow` REALIZES the escrow-release intent: bal_lo `100 →
105` (credit 5), nonce frozen `5 → 5`, frame fixed. -/
theorem goodReleaseRow_realizes_intent : ReleaseEscrowRowIntent goodReleaseRow := by
  unfold ReleaseEscrowRowIntent goodReleaseRow
  simp only [sbCol, saCol, prmCol, SEL_RELEASE_ESCROW, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 7) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 7) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED release row: `goodReleaseRow` with the post-`bal_lo` tampered to `999` (not the intended
`105`). -/
def badReleaseRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodReleaseRow.loc v
  nxt := goodReleaseRow.nxt
  pub := goodReleaseRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badReleaseRow`'s post-`bal_lo` is NOT the
credit, so the `gBalLoCredit` gate REJECTS it — a concrete UNSAT. -/
theorem badReleaseRow_rejected : ¬ (VmConstraint.gate gBalLoCredit).holdsVm badReleaseRow false false := by
  apply releaseEscrowVm_rejects_wrong_balance
  simp only [badReleaseRow, goodReleaseRow, sbCol, saCol, prmCol, SEL_RELEASE_ESCROW, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §A — STAGE-3 AMPLIFICATION: bind the `escrows` side-table ROOT into the descriptor.

Record-layer STAGE 3 (`Exec.SystemRoots`) gave each side-table its OWN kernel-owned root column in the
dedicated `system_roots` sub-block, committed by `systemRootsDigest` into ONE carrier
(`aux_off_sys.SYSTEM_ROOTS_DIGEST`). For releaseEscrow the relevant root is `state.systemRoot.ESCROW`
(the `escrows` holding-store list digest). BEFORE this stage the escrows resolve `markResolved … id` was
the §IR-EXTENSION flag — there was no column to bind it. NOW there is. This section AMPLIFIES the
descriptor to FULL: a per-row root-UPDATE gate binds the `escrows`-resolve step into the row, the
after-`SYSTEM_ROOTS_DIGEST` carrier is absorbed into `state_commit` by the GROUP-4 extension (site 3's
previously-spare `.zero` slot), and the anti-ghost tooth is re-proved over the now-bound root, CONNECTED
to `Exec.SystemRoots.systemRootsDigest_binds_pointwise` (equal commitment ⇒ equal digest ⇒ equal
`escrows` root). The §1–§10 soundness + universe-A connector are UNCHANGED (strictly additive). -/

open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise N_SYSTEM_ROOTS)

/-- The committed `system_roots` digest carrier of the AFTER state (`aux_off_sys.SYSTEM_ROOTS_DIGEST`). -/
def SYS_DIG_AFTER : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST

/-- The committed `system_roots` digest carrier of the BEFORE state (one aux past the after-carrier,
DISTINCT from every claimed aux slot, so it never aliases). -/
def SYS_DIG_BEFORE : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST + 1

/-- The `escrows`-accumulator STEP param: the field-element delta the `markResolved … id` resolve
contributes to the `escrows` side-table digest. The trace generator lays it at `param2`. -/
def ESCROW_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmEscrowStep : EmittedExpr := .var (prmCol ESCROW_ROOT_STEP_PARAM)

/-- The kernel index of the `escrows` side-table root (`Exec.SystemRoots.systemRoot.ESCROW = 0`). -/
def ESCROW_ROOT_INDEX : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.ESCROW, by decide⟩

/-! ## §B — the root-UPDATE gate + the digest-absorbing GROUP-4 extension site. -/

/-- Root-update gate body: `sa_digest − sb_digest − step` (so `sa_digest = sb_digest + step`). -/
def gEscrowRootUpdate : EmittedExpr :=
  eSub (eSub (.var SYS_DIG_AFTER) (.var SYS_DIG_BEFORE)) ePrmEscrowStep

/-- Site 3′: `state_commit = H4(inter1, inter2, inter3, sys_digest_after)` — the GROUP-4 extension that
absorbs the `system_roots` digest carrier (replacing transfer's spare `.zero`). -/
def siteEscrowRoot : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col SYS_DIG_AFTER ]
  , arity := 4 }

/-- The amplified GROUP-4 hash sites: transfer's three inner sites + the digest-absorbing site 3′. -/
def releaseEscrowRootHashSites : List VmHashSite :=
  [ EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1
  , EffectVmEmitTransfer.site2, siteEscrowRoot ]

/-- **`releaseEscrowRootHash_binds`** — under the amplified sites, the published `state_commit` is the
genuine 4-level digest of the after-state WITH the `system_roots` digest carrier in the 4th slot. -/
theorem releaseEscrowRootHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env releaseEscrowRootHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc SYS_DIG_AFTER ] := by
  unfold siteHoldsAll releaseEscrowRootHashSites at h
  simp only [siteHoldsAll.go, EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1,
    EffectVmEmitTransfer.site2, siteEscrowRoot, VmHashSite.resolvedInputs, HashInput.resolve,
    List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, _, _, h3, _⟩ := h
  rw [h3]; rfl

/-! ## §C — FAITHFULNESS of the root-update gate + ANTI-GHOST over the bound digest. -/

/-- **`ReleaseEscrowRootIntent env`** — the intended `escrows`-root move: the `system_roots` digest
ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
projection of the resolve `escrows := markResolved escrows id` onto its committed digest. -/
def ReleaseEscrowRootIntent (env : VmRowEnv) : Prop :=
  env.loc SYS_DIG_AFTER = env.loc SYS_DIG_BEFORE + env.loc (prmCol ESCROW_ROOT_STEP_PARAM)

/-- **`releaseEscrowRoot_gate_faithful`.** The root-update gate holds IFF the digest advances by the step. -/
theorem releaseEscrowRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gEscrowRootUpdate).holdsVm env false false ↔ ReleaseEscrowRootIntent env := by
  simp only [VmConstraint.holdsVm, gEscrowRootUpdate, ePrmEscrowStep, eSub, EmittedExpr.eval,
    ReleaseEscrowRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator is rejected. -/
theorem releaseEscrowRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc SYS_DIG_AFTER ≠ env.loc SYS_DIG_BEFORE + env.loc (prmCol ESCROW_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gEscrowRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((releaseEscrowRoot_gate_faithful env).mp h)

/-! ## §D — the AMPLIFIED descriptor + the side-table-root anti-ghost tooth (connected to `SystemRoots`). -/

/-- **`releaseEscrowVmDescriptorFull`** — the AMPLIFIED releaseEscrow circuit: the §2 per-row gates PLUS
the `escrows`-root-update gate, with the digest-absorbing GROUP-4 sites. Strictly additive. -/
def releaseEscrowVmDescriptorFull : EffectVmDescriptor :=
  { name := releaseEscrowVmAirName ++ "-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := (releaseEscrowRowGates ++ [.gate gEscrowRootUpdate])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := releaseEscrowRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The amplified descriptor STILL forces the §3 row intent (the credit + frame freeze). -/
theorem releaseEscrowFull_forces_intent (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ releaseEscrowVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    ReleaseEscrowRowIntent env := by
  apply (releaseEscrowVm_faithful env).mp
  intro c hc
  have hmem : c ∈ releaseEscrowVmDescriptorFull.constraints := by
    unfold releaseEscrowVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have := hgates c hmem
  unfold releaseEscrowRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- The amplified descriptor forces the `escrows`-ROOT update (the new content STAGE 3 buys). -/
theorem releaseEscrowFull_forces_root (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ releaseEscrowVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    ReleaseEscrowRootIntent env := by
  apply (releaseEscrowRoot_gate_faithful env).mp
  have hmem : (VmConstraint.gate gEscrowRootUpdate) ∈ releaseEscrowVmDescriptorFull.constraints := by
    unfold releaseEscrowVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-- **`releaseEscrowFull_commit_binds_sysdigest` — the digest is now bound into `state_commit`.** -/
theorem releaseEscrowFull_commit_binds_sysdigest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ releaseEscrowRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ releaseEscrowRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER := by
  rw [releaseEscrowRootHash_binds hash e₁ hs₁, releaseEscrowRootHash_binds hash e₂ hs₂] at hcommit
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  exact houter.2.2.2.1

/-- **`releaseEscrowFull_binds_escrow_root` — CONNECTED to `Exec.SystemRoots`.** Two amplified rows that
publish the same `state_commit` AND whose after-digest carrier IS the `systemRootsDigest` of their
sub-blocks have the SAME `escrows` side-table root. Tampering the `escrows` root (un-resolving the
record) provably MOVES `state_commit` ⇒ UNSAT. -/
theorem releaseEscrowFull_binds_escrow_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ releaseEscrowRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ releaseEscrowRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc SYS_DIG_AFTER = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc SYS_DIG_AFTER = systemRootsDigest hash sr₂) :
    sr₁ ESCROW_ROOT_INDEX = sr₂ ESCROW_ROOT_INDEX := by
  have hdig : systemRootsDigest hash sr₁ = systemRootsDigest hash sr₂ := by
    rw [← hd₁, ← hd₂]
    exact releaseEscrowFull_commit_binds_sysdigest hash hCR e₁ e₂ hs₁ hs₂ hcommit
  exact systemRootsDigest_binds_pointwise hash hCR sr₁ sr₂ hdig ESCROW_ROOT_INDEX

/-- **`releaseEscrowFull_sound` — the amplified full soundness.** A row satisfying the AMPLIFIED
descriptor, under `RowEncodesRelease`, forces the `CellReleaseSpec` credit/freeze AND the `escrows`-root
advance AND publishes the post-commit — the §7 universe-A connector lifted onto the root-bound descriptor. -/
theorem releaseEscrowFull_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : ReleaseParams)
    (henc : RowEncodesRelease env pre p post)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorFull env true true) :
    CellReleaseSpec pre p post
      ∧ ReleaseEscrowRootIntent env
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites, _⟩ := hsat
  have hintent := releaseEscrowFull_forces_intent env true true hcs
  have hroot := releaseEscrowFull_forces_root env true true hcs
  refine ⟨intent_to_cellReleaseSpec env pre post p henc hintent, hroot, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ releaseEscrowVmDescriptorFull.constraints := by
      unfold releaseEscrowVmDescriptorFull
      simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §E — RECONCILIATION onto the runtime trace-generator layout (the cutover discipline, `3aaf0772d`).

HONEST cutover status (the runtime hand-AIR + `generate_effect_vm_trace`, `Effect::ReleaseEscrow` arm):

  * **conserved leg (divergence, reported):** the runtime row is BALANCE-NEUTRAL (`trace.rs` writes only
    `param0 = escrow_id_hash` and TICKS the nonce; NO balance move). The §1 row gate here reads the
    universe-A IMAGE (CREDIT the recipient cell, nonce FROZEN), the ledger-entry projection of
    `ReleaseEscrowSpec`. The runtime moves the recipient's balance OUTSIDE this single escrow row (the
    settle is a side-table resolve that releases the parked value via a separate per-cell credit row);
    so on the runtime escrow row those columns diverge exactly as the NOTES family's did in `3aaf0772d`
    (the runtime row is neutral; universe-A's per-cell image moves the ledger). They reconcile only at
    `amount = 0`. Reported, not papered — the universe-A connector (§9–§10) stays the ledger image.

  * **escrows-root leg (NOW BINDABLE — this section):** the runtime writes the advanced `system_roots`
    digest carrier (aux 96) for the resolve; once the hand-AIR absorbs it at the commitment's 4th slot
    (currently `BabyBear::ZERO` in `cell_state.rs::compute_commitment`), `siteEscrowRoot` AGREES and
    `gEscrowRootUpdate` holds on the honest trace. Lean side FULL+proved; the runtime AIR change (absorb
    the digest at slot 4) is the one Rust-side step that graduates the cutover — out of this file's scope.

We pin the layout agreement as `#guard`s so a column drift breaks the build. -/

#guard SYS_DIG_AFTER == aux_off_sys.SYSTEM_ROOTS_DIGEST
#guard SYS_DIG_AFTER == 96
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        SYS_DIG_AFTER, SYS_DIG_BEFORE].dedup.length == 5
#guard ESCROW_ROOT_STEP_PARAM == 2
#guard ESCROW_ROOT_STEP_PARAM < NUM_PARAMS
#guard ESCROW_ROOT_INDEX.val == Dregg2.Exec.SystemRoots.systemRoot.ESCROW
#guard ESCROW_ROOT_INDEX.val == 0
#guard releaseEscrowVmDescriptorFull.constraints.length == 14 + 14 + 4 + 3
#guard releaseEscrowVmDescriptorFull.hashSites.length == 4

/-! ## §G — NON-VACUITY of the amplification: a concrete root-advancing row + a forged one. -/

/-- A concrete root-update row: `sys_digest 1000 → 1042` (advance by step `42` = the resolve's digest
contribution). -/
def goodEscrowRootRow : VmRowEnv where
  loc := fun v =>
    if v = SYS_DIG_BEFORE then 1000
    else if v = SYS_DIG_AFTER then 1042
    else if v = prmCol ESCROW_ROOT_STEP_PARAM then 42
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEscrowRootRow` REALIZES the `escrows`-root advance: `1042 = 1000 + 42`. -/
theorem goodEscrowRootRow_realizes : ReleaseEscrowRootIntent goodEscrowRootRow := by
  unfold ReleaseEscrowRootIntent goodEscrowRootRow
  simp only [SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, ESCROW_ROOT_STEP_PARAM,
    aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-- A FORGED root row: the after-digest is `9999` (NOT the advance `1042`) — an un-resolved `escrows` update. -/
def badEscrowRootRow : VmRowEnv where
  loc := fun v => if v = SYS_DIG_AFTER then 9999 else goodEscrowRootRow.loc v
  nxt := goodEscrowRootRow.nxt
  pub := goodEscrowRootRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEscrowRootRow` is REJECTED by `gEscrowRootUpdate`. -/
theorem badEscrowRootRow_rejected :
    ¬ (VmConstraint.gate gEscrowRootUpdate).holdsVm badEscrowRootRow false false := by
  apply releaseEscrowRoot_rejects_wrong_root
  simp only [badEscrowRootRow, goodEscrowRootRow, SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol,
    ESCROW_ROOT_STEP_PARAM, aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE,
    NUM_EFFECTS, STATE_SIZE]
  norm_num

/-! ## §12 — Axiom-hygiene pins. -/

#guard releaseEscrowVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard releaseEscrowVmDescriptor.hashSites.length == 4
#guard releaseEscrowVmDescriptor.traceWidth == 186

#assert_axioms releaseEscrowVm_faithful
#assert_axioms releaseEscrowVm_rejects_wrong_output
#assert_axioms releaseEscrowVm_rejects_wrong_balance
#assert_axioms intent_to_cellReleaseSpec
#assert_axioms releaseEscrowDescriptor_full_sound
#assert_axioms releaseEscrowDescriptor_commit_binds_state
#assert_axioms unify_release_credit
#assert_axioms descriptor_agrees_with_executor_release
#assert_axioms goodReleaseRow_realizes_intent
#assert_axioms badReleaseRow_rejected

-- STAGE-3 amplification (the bound `escrows` side-table root):
#assert_axioms releaseEscrowRootHash_binds
#assert_axioms releaseEscrowRoot_gate_faithful
#assert_axioms releaseEscrowRoot_rejects_wrong_root
#assert_axioms releaseEscrowFull_forces_intent
#assert_axioms releaseEscrowFull_forces_root
#assert_axioms releaseEscrowFull_commit_binds_sysdigest
#assert_axioms releaseEscrowFull_binds_escrow_root
#assert_axioms releaseEscrowFull_sound
#assert_axioms goodEscrowRootRow_realizes
#assert_axioms badEscrowRootRow_rejected

/-! ## §H — CLASS-A PROMOTION: the GENUINE in-row escrow-root RECOMPUTE (kills the opaque step).

§A–§G bound the escrows root by the ADDITIVE OPAQUE STEP `gEscrowRootUpdate`. This section PROMOTES
releaseEscrow to class A via the genuine in-row recompute from `EffectVmEmitEscrowRoot`: the released
record's leaf is recomputed `hash[id,creator,recipient,amount,asset,resolved]` (resolved = 1 on release;
amount = the SAME `param.AMOUNT` driving the recipient credit), then `new_root = hash[record_leaf,
old_root]` — FORCED, not a free step. The released amount IS the parked record's amount, bound into
`state_commit`. The §1–§10 credit + frame soundness are UNCHANGED. -/

open Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
  (escrowRecomputeSites escrowRootHolds escrowRootAdvance_forced escrowRoot_binds_record
   escrowRoot_amount_bound leafOf advanceOf)

/-- **`releaseEscrowVmDescriptorGenuine`** — the CLASS-A releaseEscrow circuit: §2 per-row gates (credit +
frame freeze), NO opaque root gate, genuine recompute sites prepended to the GROUP-4 commitment sites. -/
def releaseEscrowVmDescriptorGenuine : EffectVmDescriptor :=
  { name := releaseEscrowVmAirName ++ "-genuine-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := releaseEscrowRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := escrowRecomputeSites ++ releaseEscrowRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

theorem genuine_sites_split (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env (escrowRecomputeSites ++ releaseEscrowRootHashSites)) :
    escrowRootHolds hash env := by
  unfold escrowRootHolds escrowRecomputeSites
  unfold escrowRecomputeSites at h
  unfold siteHoldsAll at h ⊢
  simp only [List.cons_append, List.nil_append, siteHoldsAll.go,
    EffectVmEmitEscrowRoot.siteEscrowLeaf, EffectVmEmitEscrowRoot.siteEscrowRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h ⊢
  exact ⟨h.1, h.2.1, trivial⟩

/-- **`releaseEscrowGenuine_sound` — THE CLASS-A SOUNDNESS.** The genuine descriptor forces the per-cell
`CellReleaseSpec` (credit + frame freeze), the GENUINE escrow-root recompute (root FORCED), AND the commit. -/
theorem releaseEscrowGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : ReleaseParams)
    (henc : RowEncodesRelease env pre p post)
    (hsat : satisfiedVm hash releaseEscrowVmDescriptorGenuine env true true) :
    CellReleaseSpec pre p post
      ∧ env.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER
          = advanceOf hash
              (leafOf hash (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ID))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.CREATOR))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RECIPIENT))
                (env.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ASSET))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RESOLVED)))
              (env.loc EffectVmEmitEscrowRoot.SYS_DIG_BEFORE)
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites, _⟩ := hsat
  have hgates' : ∀ c ∈ releaseEscrowRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ releaseEscrowVmDescriptorGenuine.constraints := by
      unfold releaseEscrowVmDescriptorGenuine
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold releaseEscrowRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (releaseEscrowVm_faithful env).mp hgates'
  refine ⟨intent_to_cellReleaseSpec env pre post p henc hint, ?_, ?_⟩
  · exact escrowRootAdvance_forced hash env (genuine_sites_split hash env hsites)
  · have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
      intro c hc
      have hmem : c ∈ releaseEscrowVmDescriptorGenuine.constraints := by
        unfold releaseEscrowVmDescriptorGenuine
        simp only [List.mem_append]; exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    have hpin := (boundaryLast_pins env hlast).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
    rw [← hsaC]; exact hpin

/-- **`releaseEscrowGenuine_binds_record` — THE CLASS-A ANTI-GHOST.** Two genuine rows with the same
recomputed new root have the SAME released amount (and every record field) — a forged release moves the
root ⇒ moves `state_commit` ⇒ UNSAT. -/
theorem releaseEscrowGenuine_binds_record (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash releaseEscrowVmDescriptorGenuine e₁ true true)
    (hsat₂ : satisfiedVm hash releaseEscrowVmDescriptorGenuine e₂ true true)
    (hroot : e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER) :
    e₁.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) :=
  escrowRoot_amount_bound hash hCR e₁ e₂
    (genuine_sites_split hash e₁ hsat₁.2.1) (genuine_sites_split hash e₂ hsat₂.2.1) hroot

theorem releaseEscrowGenuine_recompute_nonvacuous :
    escrowRootHolds EffectVmEmitEscrowRoot.cN EffectVmEmitEscrowRoot.goodEscrowRow :=
  EffectVmEmitEscrowRoot.goodEscrowRow_recomputes

#guard releaseEscrowVmDescriptorGenuine.hashSites.length == 2 + 4
#guard releaseEscrowVmDescriptorGenuine.constraints.length == 13 + 14 + 4 + 3
#guard releaseEscrowVmDescriptorGenuine.traceWidth == 186

#assert_axioms genuine_sites_split
#assert_axioms releaseEscrowGenuine_sound
#assert_axioms releaseEscrowGenuine_binds_record

end Dregg2.Circuit.Emit.EffectVmEmitReleaseEscrow
