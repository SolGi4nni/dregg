/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow — the createCommittedEscrow (§8-hiding-portal-
gated committed-escrow CREATE) effect's concrete EffectVM circuit, EMITTED through the SAME
`EffectVmEmit` IR as transfer.

Universe A (`Inst/createCommittedEscrowA.lean`, `Spec/escrowcommitted.lean`) carries the FULL-state
soundness `createCommittedEscrowA_full_sound ⇒ CommittedEscrowCreateSpec`: a committed create

  * DEBITS the per-asset `bal` ledger at `(creator, asset)` by `amount`
    (`recBalCreditCell st.kernel.bal creator asset (-amount)`),
  * PREPENDS an unresolved bridge-tagged `EscrowRecord` (`parkedRecord …`) onto `escrows`,
  * advances the chained `log` by `escrowReceiptA actor ::`,
  * and FREEZES the other 15 kernel fields,

UNDER the §8 hiding-portal gate `hidingProof = true` ∧ the per-asset lock guard (`createGuard`).

## What the EffectVM IR (a 14-column state block + GROUP-4 commitment) DOES support

The conserved `bal` move is a SINGLE-cell single-asset DEBIT (`recBalCreditCell … (-amount)`): on the
EffectVM row this is the creator cell's `state.BALANCE_LO` limb moving DOWN by `amount`. This is
EXACTLY the bridgeLock / transfer-DEBIT leg (`signedMove = −amount`), so the IR carries it totally —
and the GROUP-4 commitment chain binds the whole after-state block (balance/nonce/fields/cap_root)
into `state_commit` exactly as for transfer.

The ONE column difference from the transfer row: the committed-escrow create does NOT tick the
creator cell's nonce (`createEscrowRawAsset` rewrites only `bal` and `escrows`; the cell record's
`nonce` field survives), whereas the transfer EffectVM row ticks `+1`. So this descriptor FREEZES the
nonce (`gNonceFreeze`), matching the executor — the freeze-nonce shape the transfer connector already
validated as `recKExec`'s genuine per-cell image.

## THE IR-EXTENSION FLAGS (the set-membership legs the per-row circuit CANNOT enforce)

`CommittedEscrowCreateSpec` ALSO (a) PREPENDS `parkedRecord` onto the `escrows` list — a SET-MEMBERSHIP
/ list-digest update — and (b) carries the §8 HIDING PORTAL `hidingProof = true` and the per-asset
lock guard (authority / availability / id-freshness). The EffectVM 14-column state block has NO
escrow-root column, and the GROUP-4 hash-sites absorb NONE of the escrows list. So the IR as it stands
CANNOT bind the escrows update into `state_commit`, NOR represent the boolean hiding portal as a
state-block gate.

  ⇒ **needs IR extension: (1) an escrows-list-root column in the EffectVM state block (a 15th data
     column, or repurposing one named field as `ESCROW_ROOT`) absorbed by a new hash-site, so the
     prepended unresolved record is bound into the published `state_commit`; (2) a hiding-portal /
     authority-gate selector input (a public boolean column `hidingProof` + an availability range gate
     `amount ≤ bal`).** Universe A binds the escrows update via the `escrowsComponent` list digest
     (`listLeafInjective LE` + `compressNInjective cN`) and the portal via `createCommittedEscrowGuard`;
     the EffectVM row has no counterpart columns. This module proves what the IR DOES support (the
     balance debit + the 14-column commitment) and reports the escrows/portal legs as out-of-IR — NOT
     papered.

The ID-FRESHNESS / no-double-spend of the escrow `id` is likewise a TURN/ACCUMULATOR property over the
`escrows` set, NOT a per-row arithmetic gate — stated honestly as out-of-row (`escrow_id_freshness_*`).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.escrowcommitted

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The committed-escrow-create selector + the debit parameter.

The EffectVM layout names only `sel.NOOP = 0` and `sel.TRANSFER = 1`; the committed-escrow-create
effect takes a fresh selector column (a LAYOUT CHOICE local to this descriptor — the running prover's
`columns.rs` assigns it; we keep the index explicit so the emitted gates are selector-specialized
exactly as the transfer template specializes on `s_transfer`). The create's balance move is a FIXED
DEBIT by `param.AMOUNT` (a lock always debits), so we emit the debit-specialized balance gate. -/

/-- The committed-escrow-create selector column index. -/
def SEL_ESCROW_CREATE : Nat := 3

/-- The create row is a committed-escrow-create row: `s_escrow_create = 1`, `s_noop = 0`. -/
def IsEscrowCreateRow (env : VmRowEnv) : Prop :=
  env.loc SEL_ESCROW_CREATE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (debit + full frame freeze + nonce freeze, term-for-term).

* `gBalLoDebit` — `new_bal_lo − old_bal_lo + amount = 0`, i.e. the limb DROPS by `amount` (the
  `recBalCreditCell … (-amount)` debit projected to the row).
* `gNonceFreeze` — `new_nonce − old_nonce = 0` (FROZEN; the create does NOT tick the nonce).
* `gBalHi`/`gCapPass`/`gResPass`/`gFieldPass i` — REUSED from the transfer template (bal_hi, cap_root,
  reserved, and the 8 fields all frozen — identical polynomials). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + amount`. Vanishes iff the limb drops by `amount`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (ePrm param.AMOUNT)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the create leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The committed-escrow-create AIR identity. -/
def escrowCreateVmAirName : String := "dregg-effectvm-createcommittedescrow-v1"

/-- The per-row gates: balance debit, bal_hi freeze, nonce freeze, cap/reserved freeze, 8 fields freeze. -/
def escrowCreateRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`escrowCreateVmDescriptor`** — the createCommittedEscrow effect's concrete EffectVM circuit: the
per-row debit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered
GROUP-4 hash sites (REUSED — the post-state commitment chain is the SAME 14-column binding) and the
2 balance-limb range checks. -/
def escrowCreateVmDescriptor : EffectVmDescriptor :=
  { name := escrowCreateVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := escrowCreateRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT (the independent faithfulness target).

`EscrowCreateRowIntent env`: on a create row, the new balance is the old balance MINUS `amount` (the
debit), the hi limb / nonce / whole frame (cap/reserved/8 fields) are FIXED. This is the EffectVM-row
projection of the conserved `bal` debit (`recBalCreditCell … (-amount)`) + nonce-freeze + frame-freeze
on the creator cell. -/

/-- **`EscrowCreateRowIntent env`** — the intended committed-escrow-create move on the row `env.loc`. -/
def EscrowCreateRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`escrowCreateVm_faithful`.** On a create row, the emitted descriptor's per-row gates all hold
IFF `EscrowCreateRowIntent` holds — the gates pin EXACTLY the debit + nonce-freeze + frame-freeze. -/
theorem escrowCreateVm_faithful (env : VmRowEnv) :
    (∀ c ∈ escrowCreateRowGates, c.holdsVm env false false) ↔ EscrowCreateRowIntent env := by
  unfold escrowCreateRowGates gFieldPassAll EscrowCreateRowIntent
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

/-- **Anti-ghost (general).** A create row whose post-state is NOT the intent move does NOT satisfy
the per-row gates. -/
theorem escrowCreateVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ EscrowCreateRowIntent env) :
    ¬ (∀ c ∈ escrowCreateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((escrowCreateVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A create row whose post-`bal_lo` is NOT the debit has no
satisfying gate set — the `gBalLoDebit` gate alone rejects it (UNSAT). -/
theorem escrowCreateVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`). -/

/-- The create parameters carried in the param block (only `amount` matters for the conserved leg). -/
structure EscrowParams where
  amount : ℤ

/-- `RowEncodesEscrow env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition (the create's `RowEncodes` analogue: no `direction` column). -/
def RowEncodesEscrow (env : VmRowEnv) (pre : CellState) (p : EscrowParams) (post : CellState) : Prop :=
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

/-- **`CellEscrowSpec pre p post`** — the per-cell FULL-state create spec: the moved cell's `balLo`
drops by `amount`, the nonce is FROZEN, and the WHOLE frame (balHi, the 8 fields, capRoot, reserved)
is LITERALLY unchanged. This is the EffectVM-row projection of `CommittedEscrowCreateSpec`'s `bal`
debit + frame freeze on the creator cell. -/
def CellEscrowSpec (pre : CellState) (p : EscrowParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesEscrow`, `EscrowCreateRowIntent` IS the structured `CellEscrowSpec`. -/
theorem intent_to_cellEscrowSpec (env : VmRowEnv) (pre post : CellState) (p : EscrowParams)
    (henc : RowEncodesEscrow env pre p post) (hint : EscrowCreateRowIntent env) :
    CellEscrowSpec pre p post := by
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

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding. -/

/-- **`escrowCreateDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor (gates +
transitions + boundaries + hash sites), under the `RowEncodesEscrow` decoding, forces the structured
per-cell `CellEscrowSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem escrowCreateDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : EscrowParams)
    (henc : RowEncodesEscrow env pre p post)
    (hsat : satisfiedVm hash escrowCreateVmDescriptor env true true) :
    CellEscrowSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ escrowCreateRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ escrowCreateVmDescriptor.constraints := by
      unfold escrowCreateVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold escrowCreateRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (escrowCreateVm_faithful env).mp hgates'
  refine ⟨intent_to_cellEscrowSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ escrowCreateVmDescriptor.constraints := by
      unfold escrowCreateVmDescriptor
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

/-- **`escrowCreateDescriptor_commit_binds_state`** — the keystone anti-ghost for the create: two
descriptor-satisfying create rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns (balance limbs, nonce, all 8 fields, cap_root). So a prover cannot keep `NEW_COMMIT` while
tampering any absorbed cell of the post-state. -/
theorem escrowCreateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash escrowCreateVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash escrowCreateVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash escrowCreateVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ escrowCreateVmDescriptor.constraints := by
        unfold escrowCreateVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellEscrowSpec` IS `CommittedEscrowCreateSpec`'s per-cell bal image.

`createCommittedEscrowA_full_sound ⇒ CommittedEscrowCreateSpec` carries the `bal` debit at
`(creator, asset)` (`recBalCreditCell st.kernel.bal creator asset (-amount)`). We project ONE cell of
the kernel `bal` ledger into the keystone `CellState` (the conserved `balLo` limb reads the per-asset
entry `bal creator asset`; the EffectVM limbs with no universe-A analogue — balHi/fields/capRoot/
reserved — are `0`, FROZEN), and prove the creator cell's projection satisfies `CellEscrowSpec` EXACTLY.

The DIVERGENCE pattern (reported, not papered):

  * The `escrows`-list prepend is NOT in this per-cell projection (no escrow column in the EffectVM
    block — the §IR-extension flag #1). The connector covers ONLY the conserved `bal` leg.
  * The §8 hiding portal / authority / availability / id-freshness guard is the §IR-extension flag #2
    (no portal column on the EffectVM row).
  * `CommittedEscrowCreateSpec`'s `bal` clause is a WHOLE-function equality
    `bal' = recBalCreditCell …`; the per-cell projection reads the `(creator, asset)` entry of it. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId recBalCreditCell)
open Dregg2.Circuit.Spec.EscrowCommitted
  (CommittedEscrowCreateSpec createCommittedEscrowKAsset_correct parkedRecord)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). The other EffectVM limbs have no universe-A analogue on the conserved ledger entry, so
they are `0` (frozen). -/
def cellProjEscrow (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_escrow_debit`** — the creator cell's projected `(creator, asset)` ledger entry, across a
committed `CommittedEscrowCreateSpec` post-state, satisfies the keystone's `CellEscrowSpec` EXACTLY:
`balLo` drops by `amount`; balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So
`CellEscrowSpec` IS `CommittedEscrowCreateSpec`'s per-cell `bal` image — NOT a fourth spec. -/
theorem unify_escrow_debit (st st' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (hspec : CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st') :
    CellEscrowSpec (cellProjEscrow st.kernel.bal creator asset) ⟨amount⟩
      (cellProjEscrow st'.kernel.bal creator asset) := by
  obtain ⟨_, hbal, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal creator asset = st.kernel.bal creator asset - amount
  rw [hbal]
  exact (createCommittedEscrowKAsset_correct st.kernel id creator recipient asset amount).1

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_escrow`** — a satisfying run of the runnable descriptor encoding
the creator cell of a committed create agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre − amount) equals the executor's debited `bal creator asset`,
and the frozen frame agrees. The escrows-list update + the §8 portal are out-of-IR (reported as the
§IR flags). -/
theorem descriptor_agrees_with_executor_escrow
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id : Nat) (actor creator recipient : CellId)
    (asset : AssetId) (amount : ℤ) (hidingProof : Bool) (post : CellState)
    (henc : RowEncodesEscrow env (cellProjEscrow st.kernel.bal creator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash escrowCreateVmDescriptor env true true)
    (hspec : CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st') :
    post.balLo = (cellProjEscrow st'.kernel.bal creator asset).balLo
    ∧ post.balHi = (cellProjEscrow st'.kernel.bal creator asset).balHi
    ∧ (∀ i, post.fields i = (cellProjEscrow st'.kernel.bal creator asset).fields i)
    ∧ post.capRoot = (cellProjEscrow st'.kernel.bal creator asset).capRoot
    ∧ post.reserved = (cellProjEscrow st'.kernel.bal creator asset).reserved := by
  obtain ⟨hcirc, _⟩ := escrowCreateDescriptor_full_sound hash env
    (cellProjEscrow st.kernel.bal creator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_escrow_debit st st' id actor creator recipient asset amount hidingProof hspec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — THE SET-MEMBERSHIP / ID-FRESHNESS leg the per-row circuit does NOT enforce (honest).

`CommittedEscrowCreateSpec` PREPENDS `parkedRecord id creator recipient asset amount` onto
`st.kernel.escrows`. This is a SET-INSERT into the holding-store, and the create guard requires
ID-FRESHNESS (`¬ ∃ r ∈ escrows, r.id = id`). NEITHER is a per-row arithmetic gate over the 14-column
EffectVM state block: there is no escrow-root column, the GROUP-4 hash-sites absorb none of the
`escrows` list, and the per-row gates constrain only the conserved `balLo` + frame. We state the leg
EXACTLY (it lives in universe A's `escrowsComponent` list digest, NOT in this descriptor) so the gap
is reported, not papered. -/

/-- **`escrow_prepend_is_out_of_row` — the honest finding.** A committed create's `escrows` store is
`parkedRecord :: st.escrows` (`CommittedEscrowCreateSpec`'s 3rd conjunct). This list-insert is a
universe-A property carried by the `escrowsComponent` list digest, NOT by any per-row gate or hash-site
of `escrowCreateVmDescriptor` — whose hash-sites (`transferHashSites`) absorb only the 13 balance/
nonce/field/cap state-block columns, none of `escrows`. So the runnable descriptor does NOT bind the
escrows update into `state_commit`: it is the §IR-extension flag #1, surfaced as a theorem. -/
theorem escrow_prepend_is_out_of_row (st st' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (hspec : CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st') :
    st'.kernel.escrows = parkedRecord id creator recipient asset amount :: st.kernel.escrows := by
  obtain ⟨_, _, hesc, _⟩ := hspec
  exact hesc

/-- **`escrow_id_freshness_is_out_of_row` — the no-collision leg, honestly out-of-row.** The create
guard demands the `id` is FRESH (`¬ ∃ r ∈ escrows, r.id = id`) — a uniqueness / no-double-park property
over the WHOLE `escrows` SET, not a per-row arithmetic fact. The `escrowCreateVmDescriptor` carries NO
escrow-set column, so this freshness is enforced ONLY at universe-A's guard / the turn-accumulator
layer, NEVER by the per-row circuit. We extract it from the spec's guard to name it precisely. -/
theorem escrow_id_freshness_is_out_of_row (st st' : RecChainedState) (id : Nat)
    (actor creator recipient : CellId) (asset : AssetId) (amount : ℤ) (hidingProof : Bool)
    (hspec : CommittedEscrowCreateSpec st id actor creator recipient asset amount hidingProof st') :
    ¬ (∃ r ∈ st.kernel.escrows, r.id = id) := by
  obtain ⟨⟨_, _, _, _, _, hfresh⟩, _⟩ := hspec
  exact hfresh

/-! ## §12 — NON-VACUITY: a concrete create row realizes the intent; a forged one is rejected. -/

/-- A concrete create row: `bal_lo 100 → 95` (debit 5), nonce 5 → 5 (FROZEN), frame fixed at 0. -/
def goodEscrowRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_ESCROW_CREATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.AMOUNT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEscrowRow` REALIZES the create intent: bal_lo `100 → 95`
(debit 5), nonce frozen `5 → 5`, frame fixed. -/
theorem goodEscrowRow_realizes_intent : EscrowCreateRowIntent goodEscrowRow := by
  unfold EscrowCreateRowIntent goodEscrowRow
  simp only [sbCol, saCol, prmCol, SEL_ESCROW_CREATE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 3) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 3) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED create row: `goodEscrowRow` with the post-`bal_lo` tampered to `999` (not the intended
`95`). -/
def badEscrowRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodEscrowRow.loc v
  nxt := goodEscrowRow.nxt
  pub := goodEscrowRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEscrowRow`'s post-`bal_lo` is NOT the
debit, so the `gBalLoDebit` gate REJECTS it — a concrete UNSAT. -/
theorem badEscrowRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badEscrowRow false false := by
  apply escrowCreateVm_rejects_wrong_balance
  simp only [badEscrowRow, goodEscrowRow, sbCol, saCol, prmCol, SEL_ESCROW_CREATE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard escrowCreateVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard escrowCreateVmDescriptor.hashSites.length == 4
#guard escrowCreateVmDescriptor.traceWidth == 186

#assert_axioms escrowCreateVm_faithful
#assert_axioms escrowCreateVm_rejects_wrong_output
#assert_axioms escrowCreateVm_rejects_wrong_balance
#assert_axioms intent_to_cellEscrowSpec
#assert_axioms escrowCreateDescriptor_full_sound
#assert_axioms escrowCreateDescriptor_commit_binds_state
#assert_axioms unify_escrow_debit
#assert_axioms descriptor_agrees_with_executor_escrow
#assert_axioms escrow_prepend_is_out_of_row
#assert_axioms escrow_id_freshness_is_out_of_row
#assert_axioms goodEscrowRow_realizes_intent
#assert_axioms badEscrowRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCreateCommittedEscrow
