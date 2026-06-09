/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow — the createEscrow (escrow-holding-CREATE) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

This is the escrow-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `createEscrowA`. Universe A (`Spec/escrowholdingcreate.lean`) carries the FULL-state soundness
`execFullA_createEscrowA_iff_spec ⇒ EscrowHoldingCreateSpec`: a committed create DEBITS the per-asset
ledger `bal` at `(creator, asset)` by `amount` (`recBalCreditCell … (-amount)`), PREPENDS an unresolved
`EscrowRecord` onto `escrows`, advances the log, and FREEZES the other 15 kernel fields.

## What the EffectVM IR (a 14-column state block + GROUP-4 commitment) DOES support for createEscrow

The conserved `bal` move is a SINGLE-cell single-asset DEBIT (`recBalCreditCell … (-amount)`): on the
EffectVM row this is the creator cell's `state.BALANCE_LO` limb moving DOWN by `amount`. This is EXACTLY
the transfer-row DEBIT leg (`direction = 1`, `signedMove = −amount`), so the IR carries it totally —
and the GROUP-4 commitment chain binds the whole after-state block into `state_commit` as for transfer.

The ONE column difference from transfer: createEscrow's executor does NOT tick the cell's nonce
(`createEscrowRawAsset` rewrites only `bal` and `escrows`; the cell record's `nonce` survives), whereas
the transfer EffectVM row ticks `+1`. So the createEscrow descriptor FREEZES the nonce (`gNonceFreeze`),
matching the executor — the `CellTransferSpecFrozenNonce` shape the transfer connector already validated
as `recKExec`'s genuine per-cell image.

## THE IR-EXTENSION FLAG (the escrows set-membership / park leg)

`EscrowHoldingCreateSpec` ALSO prepends a `parkedRecord` onto `escrows` — a SET-MEMBERSHIP / list-digest
update. The EffectVM 14-column state block has NO escrow-root column, and the GROUP-4 hash-sites absorb
NONE of the escrows list. So the IR as it stands CANNOT bind the escrows prepend into `state_commit`.

  ⇒ **needs IR extension: an escrows-list-root column in the EffectVM state block (a 15th data column,
     or repurposing one named field as `ESCROW_ROOT`) absorbed by a new hash-site, so the prepended
     record is bound into the published `state_commit`.** Universe A binds it via the `escrows` list
     equality; the EffectVM row has no counterpart column. This module proves what the IR DOES support
     (balance debit + the 14-column commitment) and reports the escrows park as out-of-IR — NOT papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.escrowholdingcreate
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow

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

/-! ## §0 — The createEscrow selector + the debit parameter. -/

/-- The escrow-holding-create selector column index. -/
def SEL_CREATE_ESCROW : Nat := 5

/-- The create row is an escrow-create row: `s_create_escrow = 1`, `s_noop = 0`. -/
def IsCreateEscrowRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CREATE_ESCROW = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The createEscrow per-row gate bodies (debit + full frame freeze, term-for-term).

* `gBalLoDebit` — `new_bal_lo − old_bal_lo + amount = 0`, i.e. the limb DROPS by `amount` (the
  `recBalCreditCell … (-amount)` debit projected to the row — the value parked off-ledger).
* `gNonceFreeze` — `new_nonce − old_nonce = 0` (FROZEN). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + amount`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (ePrm param.AMOUNT)

/-- Nonce-FREEZE body: `new_nonce − old_nonce`. -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted createEscrow descriptor. -/

/-- The escrow-holding-create AIR identity. -/
def createEscrowVmAirName : String := "dregg-effectvm-createescrow-v1"

/-- The escrow-create per-row gates: balance debit, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def createEscrowRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`createEscrowVmDescriptor`** — the createEscrow effect's concrete EffectVM circuit: the per-row
debit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED) and the 2 balance-limb range checks. -/
def createEscrowVmDescriptor : EffectVmDescriptor :=
  { name := createEscrowVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := createEscrowRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The createEscrow ROW INTENT (the independent faithfulness target). -/

/-- **`CreateEscrowRowIntent env`** — the intended escrow-create move on the row `env.loc`: the new
balance is the old MINUS `amount` (the debit), the hi limb / nonce / whole frame fixed. This is the
EffectVM-row projection of `EscrowHoldingCreateSpec`'s `bal` debit + frame freeze on the creator cell. -/
def CreateEscrowRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`createEscrowVm_faithful`.** On an escrow-create row, the emitted descriptor's per-row gates all
hold IFF `CreateEscrowRowIntent` holds — the gates pin EXACTLY the debit + nonce-freeze + frame-freeze. -/
theorem createEscrowVm_faithful (env : VmRowEnv) :
    (∀ c ∈ createEscrowRowGates, c.holdsVm env false false) ↔ CreateEscrowRowIntent env := by
  unfold createEscrowRowGates gFieldPassAll CreateEscrowRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceFreeze, gCapPass, gResPass,
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
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
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

/-! ## §5 — ANTI-GHOST: a wrong-output create row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A create row whose post-state is NOT the intent move does NOT satisfy the
per-row gates. -/
theorem createEscrowVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ CreateEscrowRowIntent env) :
    ¬ (∀ c ∈ createEscrowRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((createEscrowVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A create row whose post-`bal_lo` is NOT the debit has no satisfying
gate set — the `gBalLoDebit` gate alone rejects it (UNSAT). -/
theorem createEscrowVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- The create parameters carried in the param block (only `amount` matters). -/
structure CreateParams where
  amount : ℤ

/-- `RowEncodesCreate env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition. -/
def RowEncodesCreate (env : VmRowEnv) (pre : CellState) (p : CreateParams) (post : CellState) : Prop :=
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

/-- **`CellCreateSpec pre p post`** — the per-cell FULL-state create spec: the moved cell's `balLo`
drops by `amount`, the nonce is FROZEN, and the WHOLE frame is LITERALLY unchanged. This is the
EffectVM-row projection of `EscrowHoldingCreateSpec`'s `bal` debit + frame freeze on the creator cell. -/
def CellCreateSpec (pre : CellState) (p : CreateParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesCreate`, `CreateEscrowRowIntent` IS the structured `CellCreateSpec`. -/
theorem intent_to_cellCreateSpec (env : VmRowEnv) (pre post : CellState) (p : CreateParams)
    (henc : RowEncodesCreate env pre p post) (hint : CreateEscrowRowIntent env) :
    CellCreateSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.AMOUNT) := by
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

/-- **`createEscrowDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under the
`RowEncodesCreate` decoding, forces the structured per-cell `CellCreateSpec` AND publishes the
post-commit as `PI[NEW_COMMIT]`. -/
theorem createEscrowDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : CreateParams)
    (henc : RowEncodesCreate env pre p post)
    (hsat : satisfiedVm hash createEscrowVmDescriptor env true true) :
    CellCreateSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ createEscrowRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createEscrowVmDescriptor.constraints := by
      unfold createEscrowVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold createEscrowRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (createEscrowVm_faithful env).mp hgates'
  refine ⟨intent_to_cellCreateSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ createEscrowVmDescriptor.constraints := by
      unfold createEscrowVmDescriptor
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

/-- **`createEscrowDescriptor_commit_binds_state`** — the keystone anti-ghost for createEscrow: two
descriptor-satisfying create rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell of the debited
post-state. -/
theorem createEscrowDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash createEscrowVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ createEscrowVmDescriptor.constraints := by
        unfold createEscrowVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellCreateSpec` IS `EscrowHoldingCreateSpec`'s per-cell bal image.

`execFullA_createEscrowA_iff_spec ⇒ EscrowHoldingCreateSpec` carries the `bal` debit at
`(creator, asset)`. We project ONE cell of the kernel `bal` ledger into the keystone `CellState` (the
conserved `balLo` limb reads the per-asset entry `bal creator asset`; the EffectVM limbs with no
universe-A analogue — balHi/fields/capRoot/reserved — are `0`, FROZEN), and prove the creator cell's
projection satisfies `CellCreateSpec` EXACTLY (the debit + nonce-freeze + frame-freeze).

The DIVERGENCE pattern: the escrows-park is NOT in this per-cell projection (no escrow column in the
EffectVM block — the §IR-extension flag). And `EscrowHoldingCreateSpec`'s `bal` clause is a
WHOLE-function equality; the per-cell projection reads the `(creator, asset)` entry of it (extracted via
`escrowCreate_debit`). -/

open Dregg2.Exec (RecordKernelState RecChainedState CellId AssetId)
open Dregg2.Circuit.Spec.EscrowHoldingCreate (EscrowHoldingCreateSpec escrowCreate_debit)
open Dregg2.Exec.TurnExecutorFull (execFullA)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). -/
def cellProjCreate (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_create_debit`** — the creator cell's projected `(creator, asset)` ledger entry, across a
committed create (`execFullA … (.createEscrowA …) = some st'`), satisfies the keystone's `CellCreateSpec`
EXACTLY: `balLo` drops by `amount`; balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So
`CellCreateSpec` IS `EscrowHoldingCreateSpec`'s per-cell `bal` image — NOT a fourth spec. -/
theorem unify_create_debit (st st' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA st (.createEscrowA id actor creator recipient asset amount) = some st') :
    CellCreateSpec (cellProjCreate st.kernel.bal creator asset) ⟨amount⟩
      (cellProjCreate st'.kernel.bal creator asset) := by
  have hdebit := escrowCreate_debit st id actor creator recipient asset amount st' h
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal creator asset = st.kernel.bal creator asset - amount
  exact hdebit

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_create`** — a satisfying run of the runnable descriptor encoding
the creator cell of a committed create agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre − amount) equals the executor's debited `bal creator asset`,
and the frozen frame agrees. The escrows-park is out-of-IR (§IR flag). -/
theorem descriptor_agrees_with_executor_create
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (post : CellState)
    (henc : RowEncodesCreate env (cellProjCreate st.kernel.bal creator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash createEscrowVmDescriptor env true true)
    (h : execFullA st (.createEscrowA id actor creator recipient asset amount) = some st') :
    post.balLo = (cellProjCreate st'.kernel.bal creator asset).balLo
    ∧ post.balHi = (cellProjCreate st'.kernel.bal creator asset).balHi
    ∧ (∀ i, post.fields i = (cellProjCreate st'.kernel.bal creator asset).fields i)
    ∧ post.capRoot = (cellProjCreate st'.kernel.bal creator asset).capRoot
    ∧ post.reserved = (cellProjCreate st'.kernel.bal creator asset).reserved := by
  obtain ⟨hcirc, _⟩ := createEscrowDescriptor_full_sound hash env
    (cellProjCreate st.kernel.bal creator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_create_debit st st' id actor creator recipient asset amount h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — NON-VACUITY: a concrete create row realizes the intent; a forged one is rejected. -/

/-- A concrete create row: `bal_lo 100 → 95` (debit 5), nonce 5 → 5 (FROZEN), frame fixed at 0. -/
def goodCreateRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_CREATE_ESCROW then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.AMOUNT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodCreateRow` REALIZES the escrow-create intent: bal_lo `100 →
95` (debit 5), nonce frozen `5 → 5`, frame fixed. -/
theorem goodCreateRow_realizes_intent : CreateEscrowRowIntent goodCreateRow := by
  unfold CreateEscrowRowIntent goodCreateRow
  simp only [sbCol, saCol, prmCol, SEL_CREATE_ESCROW, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 5) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 5) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED create row: `goodCreateRow` with the post-`bal_lo` tampered to `999` (not the intended
`95`). -/
def badCreateRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodCreateRow.loc v
  nxt := goodCreateRow.nxt
  pub := goodCreateRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badCreateRow`'s post-`bal_lo` is NOT the
debit, so the `gBalLoDebit` gate REJECTS it — a concrete UNSAT. -/
theorem badCreateRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badCreateRow false false := by
  apply createEscrowVm_rejects_wrong_balance
  simp only [badCreateRow, goodCreateRow, sbCol, saCol, prmCol, SEL_CREATE_ESCROW, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §A — STAGE-3 AMPLIFICATION: bind the `escrows` side-table ROOT into the descriptor.

Record-layer STAGE 3 (`Exec.SystemRoots`) gave each side-table its OWN kernel-owned root column in the
dedicated `system_roots` sub-block, committed by `systemRootsDigest` into ONE carrier
(`aux_off_sys.SYSTEM_ROOTS_DIGEST`). For createEscrow the relevant root is `state.systemRoot.ESCROW`
(the `escrows` holding-store list digest). BEFORE this stage the escrows prepend `parkedRecord ::
escrows` was the §IR-EXTENSION flag — there was no column to bind it. NOW there is. This section
AMPLIFIES the descriptor to FULL: a per-row root-UPDATE gate binds the `escrows`-list step into the row,
the after-`SYSTEM_ROOTS_DIGEST` carrier is absorbed into `state_commit` by the GROUP-4 extension (site
3's previously-spare `.zero` slot — `_IR-EXTENSION-DESIGN.md:158-162`), and the anti-ghost tooth is
re-proved over the now-bound root, CONNECTED to `Exec.SystemRoots.systemRootsDigest_binds_pointwise`
(equal commitment ⇒ equal digest ⇒ equal `escrows` root). The whole-cell soundness + universe-A
connector of §1–§10 are UNCHANGED (strictly additive). -/

open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise N_SYSTEM_ROOTS)

/-- The committed `system_roots` digest carrier of the AFTER state (the kernel side-table digest the
GROUP-4 extension absorbs into `state_commit`). This is the IR's `aux_off_sys.SYSTEM_ROOTS_DIGEST`. -/
def SYS_DIG_AFTER : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST

/-- The committed `system_roots` digest carrier of the BEFORE state (the pre-image of the accumulator
step). One aux column past the after-carrier, DISTINCT from every claimed aux slot (state-inters at
8/9/10, balance-bit block, the after-digest at 96), so it never aliases. The per-effect root-update
gate reads `sb`-digest here and writes `sa`-digest at `SYS_DIG_AFTER`. -/
def SYS_DIG_BEFORE : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST + 1

/-- The `escrows`-accumulator STEP param: the field-element delta the prepended `parkedRecord`
contributes to the `escrows` side-table digest (`systemRootsDigest` over the sub-block before vs after).
The trace generator lays it at `param2` (param0 = escrow_hash, param1 = amount; param2 = the digest step
the prover computed from the membership update `parkedRecord :: escrows`). -/
def ESCROW_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmEscrowStep : EmittedExpr := .var (prmCol ESCROW_ROOT_STEP_PARAM)

/-- The kernel index of the `escrows` side-table root in the `system_roots` sub-block
(`Exec.SystemRoots.systemRoot.ESCROW = 0`; mirrors the IR's `state.systemRoot.ESCROW`). The digest the
carrier commits includes THIS root, so binding the carrier binds the escrow root. -/
def ESCROW_ROOT_INDEX : Fin N_SYSTEM_ROOTS := ⟨Dregg2.Exec.SystemRoots.systemRoot.ESCROW, by decide⟩

/-! ## §B — the root-UPDATE gate + the digest-absorbing GROUP-4 extension site.

The per-row gate `gEscrowRootUpdate` pins `sa_digest = sb_digest + step`: the `escrows` side-table
digest ADVANCES by the accumulator step the prepended `parkedRecord` contributes (the runtime hand-AIR's
escrow-create arm computes exactly this digest delta and writes the new `systemRootsDigest` carrier). The
extended hash-site list `createEscrowRootHashSites` re-uses transfer's sites 0/1/2 and REPLACES site 3's
spare `.zero` 4th input with the after-digest carrier, so `state_commit` now absorbs the side-table
digest — the GROUP-4 extension. -/

/-- Root-update gate body: `sa_digest − sb_digest − step` (so `sa_digest = sb_digest + step`). Reads the
before/after `system_roots` digest carriers and the `param2` accumulator step. -/
def gEscrowRootUpdate : EmittedExpr :=
  eSub (eSub (.var SYS_DIG_AFTER) (.var SYS_DIG_BEFORE)) ePrmEscrowStep

/-- Site 3′: `state_commit = H4(inter1, inter2, inter3, sys_digest_after)` — the GROUP-4 extension that
absorbs the `system_roots` digest carrier into the published commitment (replacing transfer's spare
`.zero`). This is the column that makes the `escrows` root BINDABLE. -/
def siteEscrowRoot : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col SYS_DIG_AFTER ]
  , arity := 4 }

/-- The amplified GROUP-4 hash sites: transfer's three inner sites + the digest-absorbing site 3′. -/
def createEscrowRootHashSites : List VmHashSite :=
  [ EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1
  , EffectVmEmitTransfer.site2, siteEscrowRoot ]

/-- **`createEscrowRootHash_binds`** — under the amplified sites, the published `state_commit` is the
genuine 4-level digest of the after-state WITH the `system_roots` digest carrier in the 4th slot. The
site order is load-bearing (site 3′ reads sites 0/1/2 + the digest column). -/
theorem createEscrowRootHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env createEscrowRootHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc SYS_DIG_AFTER ] := by
  unfold siteHoldsAll createEscrowRootHashSites at h
  simp only [siteHoldsAll.go, EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1,
    EffectVmEmitTransfer.site2, siteEscrowRoot, VmHashSite.resolvedInputs, HashInput.resolve,
    List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, _, _, h3, _⟩ := h
  rw [h3]; rfl

/-! ## §C — FAITHFULNESS of the root-update gate + ANTI-GHOST over the bound digest. -/

/-- **`CreateEscrowRootIntent env`** — the intended `escrows`-root move on the row: the `system_roots`
digest ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
projection of the membership update `escrows := parkedRecord :: escrows` onto its committed digest. -/
def CreateEscrowRootIntent (env : VmRowEnv) : Prop :=
  env.loc SYS_DIG_AFTER = env.loc SYS_DIG_BEFORE + env.loc (prmCol ESCROW_ROOT_STEP_PARAM)

/-- **`createEscrowRoot_gate_faithful`.** The root-update gate holds IFF the digest advances by the
accumulator step — the gate pins EXACTLY the `escrows`-root update. -/
theorem createEscrowRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gEscrowRootUpdate).holdsVm env false false ↔ CreateEscrowRootIntent env := by
  simp only [VmConstraint.holdsVm, gEscrowRootUpdate, ePrmEscrowStep, eSub, EmittedExpr.eval,
    CreateEscrowRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator
(`sb_digest + step`) is rejected by `gEscrowRootUpdate` — a dropped/forged `escrows` update is UNSAT. -/
theorem createEscrowRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc SYS_DIG_AFTER ≠ env.loc SYS_DIG_BEFORE + env.loc (prmCol ESCROW_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gEscrowRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((createEscrowRoot_gate_faithful env).mp h)

/-! ## §D — the AMPLIFIED descriptor + the side-table-root anti-ghost tooth (connected to `SystemRoots`). -/

/-- **`createEscrowVmDescriptorFull`** — the AMPLIFIED createEscrow circuit: the §2 per-row gates PLUS
the `escrows`-root-update gate, with the digest-absorbing GROUP-4 sites. The runtime trace writes the
advanced `system_roots` digest and binds it into `state_commit`. Strictly additive over
`createEscrowVmDescriptor` (one extra gate, the spare site-3 slot filled). -/
def createEscrowVmDescriptorFull : EffectVmDescriptor :=
  { name := createEscrowVmAirName ++ "-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := (createEscrowRowGates ++ [.gate gEscrowRootUpdate])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := createEscrowRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The amplified descriptor STILL forces the §3 row intent (the debit + frame freeze): the per-row
gates are a sublist of its constraints, and `holdsVm` of a `.gate` ignores the boundary flags. -/
theorem createEscrowFull_forces_intent (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ createEscrowVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    CreateEscrowRowIntent env := by
  apply (createEscrowVm_faithful env).mp
  intro c hc
  have hmem : c ∈ createEscrowVmDescriptorFull.constraints := by
    unfold createEscrowVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have := hgates c hmem
  unfold createEscrowRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- The amplified descriptor forces the `escrows`-ROOT update (the new content STAGE 3 buys).
Generalised over the boundary flags (the root gate is a per-row `.gate`). -/
theorem createEscrowFull_forces_root (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ createEscrowVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    CreateEscrowRootIntent env := by
  apply (createEscrowRoot_gate_faithful env).mp
  have hmem : (VmConstraint.gate gEscrowRootUpdate) ∈ createEscrowVmDescriptorFull.constraints := by
    unfold createEscrowVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-- **`createEscrowFull_commit_binds_sysdigest` — the digest is now bound into `state_commit`.** Two
rows satisfying the amplified hash-sites that publish the SAME `state_commit` have the SAME absorbed
`system_roots` digest. Off `Poseidon2SpongeCR`: the outer sponge binds its 4-list, whose 4th slot is the
after-digest carrier. So a prover CANNOT keep `state_commit` while tampering the side-table digest — the
§IR-EXTENSION flag is CLOSED. -/
theorem createEscrowFull_commit_binds_sysdigest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ createEscrowRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ createEscrowRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER := by
  rw [createEscrowRootHash_binds hash e₁ hs₁, createEscrowRootHash_binds hash e₂ hs₂] at hcommit
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  exact houter.2.2.2.1

/-- **`createEscrowFull_binds_escrow_root` — CONNECTED to `Exec.SystemRoots`.** Two amplified rows that
publish the same `state_commit` AND whose after-digest carrier IS the `systemRootsDigest` of their
respective `system_roots` sub-blocks have the SAME `escrows` side-table root (and every other). The
chain: equal commitment ⇒ equal digest carrier (`createEscrowFull_commit_binds_sysdigest`) ⇒ equal
side-table roots pointwise (`Exec.SystemRoots.systemRootsDigest_binds_pointwise`). Tampering ONLY the
`escrows` root (dropping the parked record) provably MOVES `state_commit` ⇒ UNSAT. -/
theorem createEscrowFull_binds_escrow_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ createEscrowRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ createEscrowRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc SYS_DIG_AFTER = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc SYS_DIG_AFTER = systemRootsDigest hash sr₂) :
    sr₁ ESCROW_ROOT_INDEX = sr₂ ESCROW_ROOT_INDEX := by
  have hdig : systemRootsDigest hash sr₁ = systemRootsDigest hash sr₂ := by
    rw [← hd₁, ← hd₂]
    exact createEscrowFull_commit_binds_sysdigest hash hCR e₁ e₂ hs₁ hs₂ hcommit
  exact systemRootsDigest_binds_pointwise hash hCR sr₁ sr₂ hdig ESCROW_ROOT_INDEX

/-- **`createEscrowFull_sound` — the amplified full soundness.** A row satisfying the AMPLIFIED descriptor
(gates + root-update + amplified sites), under `RowEncodesCreate`, forces the structured `CellCreateSpec`
debit/freeze AND the `escrows`-root advance AND publishes the post-commit — the §7 universe-A connector
lifted onto the root-bound descriptor. -/
theorem createEscrowFull_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : CreateParams)
    (henc : RowEncodesCreate env pre p post)
    (hsat : satisfiedVm hash createEscrowVmDescriptorFull env true true) :
    CellCreateSpec pre p post
      ∧ CreateEscrowRootIntent env
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites, _⟩ := hsat
  have hintent := createEscrowFull_forces_intent env true true hcs
  have hroot := createEscrowFull_forces_root env true true hcs
  refine ⟨intent_to_cellCreateSpec env pre post p henc hintent, hroot, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ createEscrowVmDescriptorFull.constraints := by
      unfold createEscrowVmDescriptorFull
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

HONEST cutover status (the runtime hand-AIR + `generate_effect_vm_trace`, `Effect::CreateEscrow` arm):

  * **conserved leg (column-reconciled):** the runtime debits `bal_lo` by **param1** (`amount_lo`,
    `trace.rs` writes `param0 = escrow_hash, param1 = amount_lo`) and **TICKS** the nonce on every
    non-NoOp row. The §1 row gates here read the universe-A IMAGE (debit by `param.AMOUNT = param0`,
    nonce FROZEN), which is the ledger-entry projection, NOT the runtime row. So on the runtime trace
    those two columns diverge exactly as the notes/burn families' did before `3aaf0772d` reconciled
    them. The conserved-leg cutover therefore needs the SAME column move the burn keystone took
    (debit ← param1, nonce ← tick); we report it here rather than paper it, leaving the universe-A
    connector (§9–§10) intact as the ledger image.

  * **escrows-root leg (NOW BINDABLE — this section):** the runtime writes the advanced `system_roots`
    digest carrier (aux 96) and, once the hand-AIR absorbs it at the commitment's 4th slot (currently
    `BabyBear::ZERO` in `cell_state.rs::compute_commitment`), `siteEscrowRoot` AGREES with the hand-AIR
    and `gEscrowRootUpdate` holds on the honest trace. The Lean side is FULL+proved; the runtime AIR
    change (absorb the digest at slot 4) is the one Rust-side step that graduates the cutover — out of
    this file's scope, reported as the remaining gate.

We pin the layout agreement as `#guard`s so a column drift breaks the build. -/

-- The amplified descriptor reads the kernel digest carrier (aux 96), not a user field.
#guard SYS_DIG_AFTER == aux_off_sys.SYSTEM_ROOTS_DIGEST
#guard SYS_DIG_AFTER == 96
-- The before-carrier is DISTINCT from every claimed aux slot (state-inters + after-digest).
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        SYS_DIG_AFTER, SYS_DIG_BEFORE].dedup.length == 5
-- The accumulator-step param is param2 (param0 = escrow_hash, param1 = amount), in-range.
#guard ESCROW_ROOT_STEP_PARAM == 2
#guard ESCROW_ROOT_STEP_PARAM < NUM_PARAMS
-- The escrow root is index 0 of the `system_roots` sub-block.
#guard ESCROW_ROOT_INDEX.val == Dregg2.Exec.SystemRoots.systemRoot.ESCROW
#guard ESCROW_ROOT_INDEX.val == 0
-- The amplified descriptor has the extra root-update gate (14 row gates now) + the 4 amplified sites.
#guard createEscrowVmDescriptorFull.constraints.length == 14 + 14 + 4 + 3
#guard createEscrowVmDescriptorFull.hashSites.length == 4

/-! ## §G — NON-VACUITY of the amplification: a concrete root-advancing row + a forged one. -/

/-- A concrete root-update row: `sys_digest 1000 → 1042` (advance by step `42` = the prepended
`parkedRecord`'s digest contribution). -/
def goodEscrowRootRow : VmRowEnv where
  loc := fun v =>
    if v = SYS_DIG_BEFORE then 1000
    else if v = SYS_DIG_AFTER then 1042
    else if v = prmCol ESCROW_ROOT_STEP_PARAM then 42
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEscrowRootRow` REALIZES the `escrows`-root advance:
`1042 = 1000 + 42`. -/
theorem goodEscrowRootRow_realizes : CreateEscrowRootIntent goodEscrowRootRow := by
  unfold CreateEscrowRootIntent goodEscrowRootRow
  simp only [SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, ESCROW_ROOT_STEP_PARAM,
    aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-- A FORGED root row: the after-digest is `9999` (NOT the advance `1042`) — a dropped/forged `escrows`
update. -/
def badEscrowRootRow : VmRowEnv where
  loc := fun v => if v = SYS_DIG_AFTER then 9999 else goodEscrowRootRow.loc v
  nxt := goodEscrowRootRow.nxt
  pub := goodEscrowRootRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEscrowRootRow`'s after-digest is NOT the
advance, so `gEscrowRootUpdate` REJECTS it — the bound root has teeth. -/
theorem badEscrowRootRow_rejected :
    ¬ (VmConstraint.gate gEscrowRootUpdate).holdsVm badEscrowRootRow false false := by
  apply createEscrowRoot_rejects_wrong_root
  simp only [badEscrowRootRow, goodEscrowRootRow, SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol,
    ESCROW_ROOT_STEP_PARAM, aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE,
    NUM_EFFECTS, STATE_SIZE]
  norm_num

/-! ## §12 — Axiom-hygiene pins. -/

#guard createEscrowVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard createEscrowVmDescriptor.hashSites.length == 4
#guard createEscrowVmDescriptor.traceWidth == 186

#assert_axioms createEscrowVm_faithful
#assert_axioms createEscrowVm_rejects_wrong_output
#assert_axioms createEscrowVm_rejects_wrong_balance
#assert_axioms intent_to_cellCreateSpec
#assert_axioms createEscrowDescriptor_full_sound
#assert_axioms createEscrowDescriptor_commit_binds_state
#assert_axioms unify_create_debit
#assert_axioms descriptor_agrees_with_executor_create
#assert_axioms goodCreateRow_realizes_intent
#assert_axioms badCreateRow_rejected

-- STAGE-3 amplification (the bound `escrows` side-table root):
#assert_axioms createEscrowRootHash_binds
#assert_axioms createEscrowRoot_gate_faithful
#assert_axioms createEscrowRoot_rejects_wrong_root
#assert_axioms createEscrowFull_forces_intent
#assert_axioms createEscrowFull_forces_root
#assert_axioms createEscrowFull_commit_binds_sysdigest
#assert_axioms createEscrowFull_binds_escrow_root
#assert_axioms createEscrowFull_sound
#assert_axioms goodEscrowRootRow_realizes
#assert_axioms badEscrowRootRow_rejected

/-! ## §H — CLASS-A PROMOTION: the GENUINE in-row escrow-root RECOMPUTE (kills the opaque step).

§A–§G bound the escrows root by an ADDITIVE OPAQUE STEP (`gEscrowRootUpdate`: `sys_digest_after =
sys_digest_before + step_param`, `step_param` a FREE param). That is class C: a hostile prover picks ANY
step, so the root is *asserted*, not *recomputed* (the coverage ledger's createEscrow C-downgrade).

This section PROMOTES createEscrow to class A by REPLACING the opaque step with the genuine in-row
recompute from `EffectVmEmitEscrowRoot`: two hash-sites force

    record_leaf = hash[ id, creator, recipient, amount, asset, resolved ]      -- amount = param.AMOUNT
    sys_digest_after = hash[ record_leaf, sys_digest_before ]                    -- prepend-accumulator

so the new root is a DETERMINISTIC FUNCTION of (the bound record content, the old root) — FORCED, not
asserted. The `amount` input is the SAME `param.AMOUNT` column that drives the balance debit, so the
parked record's amount IS the debited amount (no skew). The new-root carrier is absorbed into
`state_commit` (the GROUP-4 site 3′, REUSED from §A), so under `Poseidon2SpongeCR` tampering ANY
parked-record field or the old root provably MOVES `state_commit` ⇒ UNSAT. The §1–§10 whole-cell
soundness + universe-A connector are UNCHANGED (strictly additive). -/

open Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
  (escrowRecomputeSites escrowRootHolds escrowRootAdvance_forced escrowRoot_binds_record
   escrowRoot_amount_bound leafOf advanceOf)

/-- **`createEscrowVmDescriptorGenuine`** — the CLASS-A createEscrow circuit: the §2 per-row gates (debit +
frame freeze) — NO opaque root gate — with the GROUP-4 commitment sites EXTENDED by the genuine recompute
sites (`escrowRecomputeSites`: leaf, then advance). The new-root carrier is forced by the bound record +
old root, then absorbed into `state_commit` via `siteEscrowRoot`. -/
def createEscrowVmDescriptorGenuine : EffectVmDescriptor :=
  { name := createEscrowVmAirName ++ "-genuine-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := createEscrowRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := escrowRecomputeSites ++ createEscrowRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The genuine descriptor's hash-site walk decomposes into the recompute sites (first) THEN the
commitment sites. We extract the recompute-holds predicate + the commitment-binds predicate from one
`siteHoldsAll` over the concatenation. -/
theorem genuine_sites_split (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env (escrowRecomputeSites ++ createEscrowRootHashSites)) :
    escrowRootHolds hash env := by
  -- the recompute sites (leaf, advance) read only `.col` inputs (no cross-site `digest k`), so their
  -- satisfaction is independent of the accumulator prefix — they hold as a standalone `siteHoldsAll`.
  unfold escrowRootHolds escrowRecomputeSites
  unfold escrowRecomputeSites at h
  unfold siteHoldsAll at h ⊢
  simp only [List.cons_append, List.nil_append, siteHoldsAll.go,
    EffectVmEmitEscrowRoot.siteEscrowLeaf, EffectVmEmitEscrowRoot.siteEscrowRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h ⊢
  exact ⟨h.1, h.2.1, trivial⟩

/-- **`createEscrowGenuine_root_forced`** — satisfying the genuine descriptor FORCES the new escrow root to
be the genuine recompute `hash[ hash[record], old_root ]` of the BOUND record content + old root. No free
step survives: the root is recomputed, not asserted. -/
theorem createEscrowGenuine_root_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hsat : satisfiedVm hash createEscrowVmDescriptorGenuine env true true) :
    env.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER
      = advanceOf hash
          (leafOf hash (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ID))
            (env.loc (prmCol EffectVmEmitEscrowRoot.ep.CREATOR))
            (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RECIPIENT))
            (env.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT))
            (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ASSET))
            (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RESOLVED)))
          (env.loc EffectVmEmitEscrowRoot.SYS_DIG_BEFORE) :=
  escrowRootAdvance_forced hash env (genuine_sites_split hash env hsat.2.1)

/-- **`createEscrowGenuine_sound` — THE CLASS-A SOUNDNESS.** Satisfying the genuine descriptor under
`RowEncodesCreate` forces (a) the structured per-cell `CellCreateSpec` (debit + frame freeze — §7's
content, the gates are unchanged), (b) the GENUINE escrow-root recompute (the new root IS
`hash[hash[record], old]`, FORCED), AND (c) publishes `post.commit = PI[NEW_COMMIT]`. This is the
whole-transition class-A statement: the moved balance + the genuinely-recomputed side-table root + the
published commitment, all from one descriptor. -/
theorem createEscrowGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : CreateParams)
    (henc : RowEncodesCreate env pre p post)
    (hsat : satisfiedVm hash createEscrowVmDescriptorGenuine env true true) :
    CellCreateSpec pre p post
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
  obtain ⟨hcs, hsites, hrng⟩ := hsat
  -- (a) the per-row gates force CellCreateSpec (gates identical to §7)
  have hgates' : ∀ c ∈ createEscrowRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createEscrowVmDescriptorGenuine.constraints := by
      unfold createEscrowVmDescriptorGenuine
      simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold createEscrowRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (createEscrowVm_faithful env).mp hgates'
  refine ⟨intent_to_cellCreateSpec env pre post p henc hint, ?_, ?_⟩
  · exact createEscrowGenuine_root_forced hash env ⟨hcs, hsites, hrng⟩
  · -- (c) the published commitment (boundaryLastPins, identical to §7)
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
      intro c hc
      have hmem : c ∈ createEscrowVmDescriptorGenuine.constraints := by
        unfold createEscrowVmDescriptorGenuine
        simp only [List.mem_append]; exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    have hpin := (boundaryLast_pins env hlast).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
    rw [← hsaC]; exact hpin

/-- **`createEscrowGenuine_binds_record` — THE CLASS-A ANTI-GHOST.** Two rows satisfying the genuine
descriptor whose recomputed new-root carriers are EQUAL share the OLD root AND every bound parked-record
field (id/creator/recipient/amount/asset/resolved). Since the new root is absorbed into `state_commit`,
two rows publishing the same commitment cannot differ in any parked-record field — a dropped/forged
escrow (skewed amount, swapped recipient, …) provably MOVES the root ⇒ MOVES `state_commit` ⇒ UNSAT. -/
theorem createEscrowGenuine_binds_record (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptorGenuine e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptorGenuine e₂ true true)
    (hroot : e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER) :
    e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_BEFORE = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_BEFORE
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.ep.ID) = e₂.loc (prmCol EffectVmEmitEscrowRoot.ep.ID)
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.ep.CREATOR) = e₂.loc (prmCol EffectVmEmitEscrowRoot.ep.CREATOR)
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.ep.RECIPIENT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.ep.RECIPIENT)
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT)
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.ep.ASSET) = e₂.loc (prmCol EffectVmEmitEscrowRoot.ep.ASSET)
    ∧ e₁.loc (prmCol EffectVmEmitEscrowRoot.ep.RESOLVED) = e₂.loc (prmCol EffectVmEmitEscrowRoot.ep.RESOLVED) :=
  escrowRoot_binds_record hash hCR e₁ e₂
    (genuine_sites_split hash e₁ hsat₁.2.1) (genuine_sites_split hash e₂ hsat₂.2.1) hroot

/-- **`createEscrowGenuine_amount_bound`** — the load-bearing corollary: two genuine rows with the same
new root have the SAME parked amount. Combined with the `gBalLoDebit` gate (post-`bal_lo` = pre − amount),
the parked record's amount IS the debited amount, bound by the commitment. The conservation leg and the
side-table content are now ONE bound transition. -/
theorem createEscrowGenuine_amount_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash createEscrowVmDescriptorGenuine e₁ true true)
    (hsat₂ : satisfiedVm hash createEscrowVmDescriptorGenuine e₂ true true)
    (hroot : e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER) :
    e₁.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) :=
  escrowRoot_amount_bound hash hCR e₁ e₂
    (genuine_sites_split hash e₁ hsat₁.2.1) (genuine_sites_split hash e₂ hsat₂.2.1) hroot

/-! ### §H NON-VACUITY: the genuine recompute is inhabited (shared `goodEscrowRow_recomputes`), and a
skewed amount is unforgeable (shared `tampered_amount_moves_root`). Both are PROVED in
`EffectVmEmitEscrowRoot` over a concrete injective sponge, so the genuine recompute fires on an honest
trace and a forged parked-amount yields a DIFFERENT root. We re-export the witness here for this file's
class-A claim. -/

/-- The genuine descriptor's recompute is INHABITED — the shared module's concrete witness
`goodEscrowRow_recomputes` satisfies exactly `createEscrowVmDescriptorGenuine.hashSites`' recompute prefix. -/
theorem createEscrowGenuine_recompute_nonvacuous :
    escrowRootHolds EffectVmEmitEscrowRoot.cN EffectVmEmitEscrowRoot.goodEscrowRow :=
  EffectVmEmitEscrowRoot.goodEscrowRow_recomputes

-- The two genuine recompute sites are present (leaf + advance) plus the 4 commitment sites = 6.
#guard createEscrowVmDescriptorGenuine.hashSites.length == 2 + 4
#guard createEscrowVmDescriptorGenuine.constraints.length == 13 + 14 + 4 + 3
#guard createEscrowVmDescriptorGenuine.traceWidth == 186

#assert_axioms genuine_sites_split
#assert_axioms createEscrowGenuine_root_forced
#assert_axioms createEscrowGenuine_sound
#assert_axioms createEscrowGenuine_binds_record
#assert_axioms createEscrowGenuine_amount_bound

end Dregg2.Circuit.Emit.EffectVmEmitCreateEscrow
