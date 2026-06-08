/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteSpend — the noteSpend (note-NULLIFIER / anti-replay) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/noteSpendA.lean`, `Spec/notenullifier.lean`) carries the FULL-state soundness
`execFullA_noteSpend_iff_spec ⇒ NoteSpendSpec`: a committed spend PREPENDS the consumed nullifier `nf`
onto the `nullifiers` SET, advances the chained `log` by `escrowReceiptA actor ::`, and is otherwise
TOTALLY NEUTRAL — it is balance-neutral (`execFullA_noteSpend_bal_frame`) and FREEZES all 16 other
kernel fields. Its GUARD is the §8 spending proof (`spendProof = true`) ∧ the DOUBLE-SPEND gate
(`nf ∉ nullifiers`).

## RECONCILED ONTO THE RUNTIME (cutover): TRANSPARENT CREDIT + nonce TICK

This descriptor is RECONCILED onto the validated runtime hand-AIR + `generate_effect_vm_trace`, which
model a noteSpend as a TRANSPARENT CREDIT: the consumed shielded note's `value` (read from `param1`)
RETURNS to the transparent `bal_lo` pool (`new_bal_lo = old_bal_lo + value`), the runtime nonce TICKS by
one, and bal_hi / cap_root / reserved / the 8 fields are FROZEN; the post-state binds into `state_commit`
via the SAME GROUP-4 chain as transfer. So `noteSpendVmDescriptor` and the hand-AIR AGREE on the honest
trace (the cutover differential passes), and any wrong-credit / wrong-nonce / mutated-frame row is UNSAT.

## THE DEEPER DIVERGENCE (reported §10, NOT papered): runtime CREDIT vs universe-A balance-NEUTRAL

Universe-A's `NoteSpendSpec` models the spend as BALANCE-NEUTRAL nullifier accumulation (`bal' = bal`) —
a DIFFERENT shielding convention. The runtime credit and the universe-A neutral convention are
reconcilable ONLY for a zero-value note (`runtime_credit_vs_univA_neutral_divergence`): a genuine semantic
modeling gap, NOT a column index. We surface it as a theorem rather than unifying.

## THE IR-EXTENSION FLAG #1 — the nullifier-set insert (the LOAD-BEARING leg, out-of-IR)

The actual effect — `nullifiers := nf :: nullifiers` — is a SET-INSERT into the nullifier accumulator.
The EffectVM 14-column block has NO nullifier-root column, and the GROUP-4 hash-sites absorb none of
the `nullifiers` list. So the per-row circuit CANNOT bind, or even witness, the consumed nullifier `nf`
or its insertion.

  ⇒ **needs IR extension: a nullifiers-accumulator-root column in the EffectVM state block absorbed by
     a new hash-site, plus a param column carrying `nf` and the §8 `spendProof` boolean, so the
     membership update `nf :: nullifiers` is bound into the published `state_commit`.**

## THE no-DOUBLE-SPEND FINDING #2 (the prompt's keystone discipline) — a TURN/ACCUMULATOR property

The headline guarantee of `noteSpend` is NO DOUBLE-SPEND: `nf ∉ nullifiers` (the membership gate). This
is fundamentally NOT a per-row arithmetic fact — it is a NON-MEMBERSHIP / uniqueness assertion over the
WHOLE accumulated nullifier SET, an inter-row / turn-accumulator property. A SINGLE EffectVM row, even
extended with a nullifier-root column, can only bind the digest of the set; the FRESHNESS check
(`nf` is not already present, i.e. a Merkle NON-membership / sorted-insert witness) is a separate
gate-kind the IR lacks. Per the keystone's finding-#2 discipline we state EXACTLY what the per-row
circuit does vs does NOT enforce: it enforces the whole-cell FREEZE; it does NOT enforce uniqueness /
no-double-spend (that lives at universe-A's nullifier-set guard and the turn-accumulator layer).

  ⇒ **needs IR extension: a Merkle/sorted-set NON-MEMBERSHIP gate-kind (a freshness witness for `nf`),
     which the 4-arity Poseidon2 hash-site IR does NOT provide.** We surface this loudly as
     `noteSpend_no_double_spend_is_turn_property` rather than pretending the per-row gate covers it.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.notenullifier

namespace Dregg2.Circuit.Emit.EffectVmEmitNoteSpend

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The noteSpend selector. -/

/-- The note-nullifier-spend selector column index (`sel::NOTE_SPEND`). -/
def SEL_NOTE_SPEND : Nat := 4

/-- The spend row is a noteSpend row: `s_note_spend = 1`, `s_noop = 0`. -/
def IsNoteSpendRow (env : VmRowEnv) : Prop :=
  env.loc SEL_NOTE_SPEND = 1 ∧ env.loc sel.NOOP = 0

/-! ### NoteSpend value column (the running trace generator's convention).

`generate_effect_vm_trace`'s `Effect::NoteSpend` arm lays `param0 = nullifier`, `param1 = value_lo`
(the spent note value), and CREDITS the cell's transparent balance by that value
(`new_state.balance += value`); the hand-AIR's note-spend gate reads `prm(1)` (= `note_val_lo`) and
asserts `new_bal_lo = old_bal_lo + value`. The descriptor MUST match: a CREDIT into the transparent pool
from the consumed shielded note, read from `param1`. (See §9 divergence: universe-A's `NoteSpendSpec`
models the spend as balance-NEUTRAL nullifier accumulation — a DIFFERENT shielding convention.) -/
namespace param
/-- NoteSpend value lives at param column 1 (`columns.rs::param::NOTE_VALUE_LO`). -/
def NOTE_VALUE_LO : Nat := 1
end param

/-- NoteSpend value as an expression (param column 1). -/
def ePrmNoteValue : EmittedExpr := .var (prmCol param.NOTE_VALUE_LO)

/-! ## §1 — The per-row gate bodies (transparent CREDIT + nonce TICK + frame freeze). -/

/-- Balance-lo CREDIT body: `new_bal_lo − old_bal_lo − value` (so `new = old + value`), reading the note
value from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) ePrmNoteValue)

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a noteSpend row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce

/-! ## §2 — The emitted descriptor. -/

/-- The note-nullifier-spend AIR identity. -/
def noteSpendVmAirName : String := "dregg-effectvm-notespend-v1"

/-- The per-row gates: bal_lo CREDIT, bal_hi freeze, nonce TICK, cap/reserved freeze, 8 fields freeze. -/
def noteSpendRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`noteSpendVmDescriptor`** — the noteSpend effect's concrete EffectVM circuit: the per-row
WHOLE-block freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED — binding the frozen block) and the 2 balance-limb range checks. -/
def noteSpendVmDescriptor : EffectVmDescriptor :=
  { name := noteSpendVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := noteSpendRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT (the independent faithfulness target): the WHOLE state block frozen. -/

/-- **`NoteSpendRowIntent env`** — the intended noteSpend move on the row `env.loc`: the transparent
`bal_lo` is CREDITED by the `param1` value (the consumed shielded note returns value to the transparent
pool), the runtime nonce TICKS by one, and balHi/cap/reserved/8 fields are FROZEN. The nullifier-set
insert + no-double-spend gate are out-of-row (the §IR flags). -/
def NoteSpendRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.NOTE_VALUE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the credit/tick intent. -/

/-- **`noteSpendVm_faithful`.** On a noteSpend row, the emitted descriptor's per-row gates all hold
IFF `NoteSpendRowIntent` holds — the gates pin EXACTLY the transparent credit + nonce tick + frame freeze
the runtime hand-AIR enforces. -/
theorem noteSpendVm_faithful (env : VmRowEnv) (hrow : IsNoteSpendRow env) :
    (∀ c ∈ noteSpendRowGates, c.holdsVm env false false) ↔ NoteSpendRowIntent env := by
  obtain ⟨_hsNS, hsN⟩ := hrow
  unfold noteSpendRowGates gFieldPassAll NoteSpendRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      ePrmNoteValue, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
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
    · simp only [VmConstraint.holdsVm, gBalLoCredit, ePrmNoteValue, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a row whose post-`bal_lo` is NOT the credit on a noteSpend is rejected. -/

/-- **Anti-ghost (general).** A noteSpend row that does NOT realize the credit/tick intent does NOT
satisfy the per-row gates. -/
theorem noteSpendVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsNoteSpendRow env)
    (hwrong : ¬ NoteSpendRowIntent env) :
    ¬ (∀ c ∈ noteSpendRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((noteSpendVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A noteSpend row whose post-`bal_lo` is NOT the credit
`old + value` has no satisfying gate set — `gBalLoCredit` rejects it (UNSAT). -/
theorem noteSpendVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.NOTE_VALUE_LO)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, ePrmNoteValue, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesSpend env pre value post` ties the row's state-block columns + the `param1` value to a
`(pre, value, post)` cell transition. -/
def RowEncodesSpend (env : VmRowEnv) (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.NOTE_VALUE_LO) = value
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellSpendSpec pre value post`** — the per-cell FULL-state noteSpend spec (the RUNTIME image): the
transparent `balLo` is CREDITED by `value`, balHi/8-fields/cap/reserved frozen, nonce TICKED by one. This
is the EffectVM-row projection of the validated runtime hand-AIR's note-spend transition. See §9 for the
universe-A divergence (balance-NEUTRAL convention). -/
def CellSpendSpec (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesSpend`, `NoteSpendRowIntent` IS the structured `CellSpendSpec`. -/
theorem intent_to_cellSpendSpec (env : VmRowEnv) (pre post : CellState) (value : ℤ)
    (henc : RowEncodesSpend env pre value post) (hint : NoteSpendRowIntent env) :
    CellSpendSpec pre value post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpVal,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.NOTE_VALUE_LO) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpVal]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness + the commitment binding. -/

/-- **`noteSpendDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesSpend`, forces the structured per-cell FREEZE `CellSpendSpec` AND publishes the post-commit
as `PI[NEW_COMMIT]`. -/
theorem noteSpendDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteSpendRow env)
    (pre post : CellState) (value : ℤ)
    (henc : RowEncodesSpend env pre value post)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true) :
    CellSpendSpec pre value post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ noteSpendRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ noteSpendVmDescriptor.constraints := by
      unfold noteSpendVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold noteSpendRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (noteSpendVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellSpendSpec env pre post value henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ noteSpendVmDescriptor.constraints := by
      unfold noteSpendVmDescriptor
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

/-! ## §8 — The anti-ghost commitment tooth (REUSED; hash sites identical to transfer's). -/

/-- **`noteSpendDescriptor_commit_binds_state`** — two descriptor-satisfying noteSpend rows publishing
the SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT`
while tampering any absorbed cell of the (frozen) post-state. -/
theorem noteSpendDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash noteSpendVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash noteSpendVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash noteSpendVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ noteSpendVmDescriptor.constraints := by
        unfold noteSpendVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellSpendSpec` IS `NoteSpendSpec`'s per-cell frame image.

`execFullA_noteSpend_iff_spec ⇒ NoteSpendSpec` carries balance-neutrality (`bal' = bal`) and the
per-cell frame freeze (`cell' = cell`). We project ONE cell into the keystone `CellState` and prove the
projection of ANY cell satisfies `CellSpendSpec` EXACTLY (all FROZEN). The nullifier-set insert +
no-double-spend are the §IR-extension flags, reported below as out-of-row. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Circuit.Spec.NoteNullifier
  (NoteSpendSpec execFullA_noteSpend_iff_spec execFullA_noteSpend_bal_frame execFullA_noteSpend_fresh
   execFullA_noteSpend_nullifiers)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb; the other EffectVM limbs have no universe-A analogue, so `0`, frozen). -/
def cellProjSpend (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`univA_spend_is_balance_neutral` — the universe-A side of the divergence.** A committed
`NoteSpendSpec` FREEZES the per-asset ledger `bal` (`bal' = bal`, the 10th conjunct); the projected
entry's `balLo` is unchanged. So universe-A's noteSpend moves NO transparent value — the opposite of the
runtime credit. -/
theorem univA_spend_is_balance_neutral (st st' : RecChainedState) (nf : Nat) (actor c : CellId)
    (asset : AssetId) (spendProof : Bool) (hspec : NoteSpendSpec st nf actor spendProof st') :
    (cellProjSpend st'.kernel.bal c asset).balLo = (cellProjSpend st.kernel.bal c asset).balLo := by
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- NoteSpendSpec: guard ∧ nullifiers ∧ log ∧ accounts ∧ cell ∧ caps ∧ escrows ∧ revoked ∧
  --               commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE DEEPER DIVERGENCE (reported, NOT papered): runtime CREDIT vs universe-A balance-NEUTRAL.

The validated RUNTIME hand-AIR + `generate_effect_vm_trace` model a noteSpend as a TRANSPARENT CREDIT
(`new_bal_lo = old_bal_lo + value`): the consumed shielded note returns value to the transparent pool.
`noteSpendVmDescriptor` now faithfully describes that (so the cutover differential AGREES). Universe-A's
`NoteSpendSpec` instead is BALANCE-NEUTRAL (`bal' = bal`) — a DIFFERENT shielding convention. The two
agree only at `value = 0`. We surface this as a divergence theorem; the nullifier-set insert +
no-double-spend legs (§11) are universe-A properties unaffected by which balance convention is canonical. -/

/-- **`runtime_credit_vs_univA_neutral_divergence` — THE DEEPER DIVERGENCE, named precisely.** A
descriptor-satisfying noteSpend row (the RUNTIME image) CREDITS the cell's `balLo` by `value`
(`post.balLo = pre.balLo + value`, from `CellSpendSpec`), whereas the committed universe-A spec FREEZES
the projected entry's `balLo`. For these to AGREE on the post-balance we would need `pre.balLo + value =
pre.balLo`, i.e. `value = 0`. So the runtime credit and the universe-A balance-neutral convention are
reconcilable ONLY for a zero-value note — a genuine semantic modeling gap (a shielding convention
difference), NOT a column index. Reported, not forced. -/
theorem runtime_credit_vs_univA_neutral_divergence
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteSpendRow env)
    (st st' : RecChainedState) (nf : Nat) (actor c : CellId) (asset : AssetId) (spendProof : Bool)
    (post : CellState) (value : ℤ)
    (henc : RowEncodesSpend env (cellProjSpend st.kernel.bal c asset) value post)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true)
    (hspec : NoteSpendSpec st nf actor spendProof st')
    (hagree : post.balLo = (cellProjSpend st'.kernel.bal c asset).balLo) :
    value = 0 := by
  obtain ⟨hcirc, _⟩ :=
    noteSpendDescriptor_full_sound hash env hrow (cellProjSpend st.kernel.bal c asset) post value henc hsat
  have hcredit : post.balLo = (cellProjSpend st.kernel.bal c asset).balLo + value := hcirc.1
  have hneutral := univA_spend_is_balance_neutral st st' nf actor c asset spendProof hspec
  rw [hagree, hneutral] at hcredit
  linarith

/-! ## §11 — THE SET-INSERT + NO-DOUBLE-SPEND legs the per-row circuit does NOT enforce (honest).

`NoteSpendSpec` PREPENDS `nf` onto `st.kernel.nullifiers` under the freshness guard `nf ∉ nullifiers`.
NEITHER the insert NOR the freshness is a per-row gate of `noteSpendVmDescriptor`: there is no
nullifier-root column, the GROUP-4 hash-sites absorb none of `nullifiers`, and the per-row gates pin
only the frozen state block. We state both legs EXACTLY (per the keystone's finding-#2 discipline). -/

/-- **`noteSpend_nullifier_insert_is_out_of_row` — finding #1.** A committed noteSpend's `nullifiers`
store is `nf :: st.nullifiers` (`NoteSpendSpec`'s 2nd conjunct). This set-insert — the ACTUAL effect —
is a universe-A property carried by the nullifier list digest, NOT by any per-row gate or hash-site of
`noteSpendVmDescriptor`. So the runnable descriptor does NOT bind the nullifier update or `nf` into
`state_commit`: the §IR-extension flag #1, surfaced as a theorem. -/
theorem noteSpend_nullifier_insert_is_out_of_row (st st' : RecChainedState) (nf : Nat) (actor : CellId)
    (spendProof : Bool) (hspec : NoteSpendSpec st nf actor spendProof st') :
    st'.kernel.nullifiers = nf :: st.kernel.nullifiers :=
  hspec.2.1

/-- **`noteSpend_no_double_spend_is_turn_property` — finding #2 (THE keystone-discipline statement).**
The headline anti-replay guarantee — `nf` was NOT already spent (`nf ∉ st.nullifiers`) — is a
NON-MEMBERSHIP / uniqueness assertion over the WHOLE accumulated nullifier SET. It is fundamentally NOT
a per-row arithmetic fact: a single EffectVM row's 4-arity Poseidon2 hash-sites can bind a SET DIGEST
but NOT a freshness / Merkle-NON-membership witness. So `noteSpendVmDescriptor` (a per-row freeze AIR)
does NOT enforce no-double-spend; it is enforced ONLY at universe-A's nullifier-set guard and the
turn/accumulator layer. We extract the freshness from the spec's guard to NAME the boundary exactly
(NEEDS IR EXTENSION: a sorted-set / Merkle NON-membership gate-kind the hash-site IR lacks). -/
theorem noteSpend_no_double_spend_is_turn_property (st st' : RecChainedState) (nf : Nat)
    (actor : CellId) (spendProof : Bool) (hspec : NoteSpendSpec st nf actor spendProof st') :
    nf ∉ st.kernel.nullifiers :=
  hspec.1.2

/-- **`noteSpend_proof_gate_is_out_of_row` — the §8 spending-proof leg, out-of-row.** A committed
noteSpend carried `spendProof = true` — a §8 STARK spending-proof gate that the per-row freeze AIR does
NOT represent (no proof-verification column). Extracted from the spec's guard to name the boundary. -/
theorem noteSpend_proof_gate_is_out_of_row (st st' : RecChainedState) (nf : Nat) (actor : CellId)
    (spendProof : Bool) (hspec : NoteSpendSpec st nf actor spendProof st') :
    spendProof = true :=
  hspec.1.1

/-! ## §12 — NON-VACUITY: a concrete noteSpend row realizes the credit/tick intent; a wrong one rejected. -/

/-- A concrete noteSpend row: `bal_lo 100 → 130` (credit `value = 30` from `param1`), nonce 5 → 6 (TICK),
frame fixed at 0. -/
def goodSpendRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_NOTE_SPEND then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 130
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.NOTE_VALUE_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodSpendRow` is a genuine noteSpend row (`s_note_spend = 1`, `s_noop = 0`). -/
theorem goodSpendRow_isRow : IsNoteSpendRow goodSpendRow := by
  unfold IsNoteSpendRow goodSpendRow
  refine ⟨by norm_num [SEL_NOTE_SPEND], ?_⟩
  norm_num [sel.NOOP, SEL_NOTE_SPEND, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, param.NOTE_VALUE_LO]

/-- **NON-VACUITY (witness TRUE).** `goodSpendRow` REALIZES the noteSpend credit/tick intent:
`bal_lo 100 → 130 = 100 + 30`, nonce `5 → 6`, frame fixed. -/
theorem goodSpendRow_realizes_intent : NoteSpendRowIntent goodSpendRow := by
  unfold NoteSpendRowIntent goodSpendRow
  simp only [sbCol, saCol, prmCol, SEL_NOTE_SPEND, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.NOTE_VALUE_LO]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 4) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 4) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED noteSpend row: `goodSpendRow` with the post-`bal_lo` set to `999` (NOT the credit `130`). -/
def badSpendRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodSpendRow.loc v
  nxt := goodSpendRow.nxt
  pub := goodSpendRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSpendRow`'s post-`bal_lo` is NOT the credit
`130`, so `gBalLoCredit` REJECTS it — a concrete UNSAT (the credit has teeth). -/
theorem badSpendRow_rejected : ¬ (VmConstraint.gate gBalLoCredit).holdsVm badSpendRow false false := by
  apply noteSpendVm_rejects_balance_mint
  simp only [badSpendRow, goodSpendRow, sbCol, saCol, prmCol, SEL_NOTE_SPEND, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.NOTE_VALUE_LO]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard noteSpendVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard noteSpendVmDescriptor.hashSites.length == 4
#guard noteSpendVmDescriptor.traceWidth == 186

#assert_axioms noteSpendVm_faithful
#assert_axioms noteSpendVm_rejects_wrong_output
#assert_axioms noteSpendVm_rejects_balance_mint
#assert_axioms intent_to_cellSpendSpec
#assert_axioms noteSpendDescriptor_full_sound
#assert_axioms noteSpendDescriptor_commit_binds_state
#assert_axioms univA_spend_is_balance_neutral
#assert_axioms runtime_credit_vs_univA_neutral_divergence
#assert_axioms noteSpend_nullifier_insert_is_out_of_row
#assert_axioms noteSpend_no_double_spend_is_turn_property
#assert_axioms noteSpend_proof_gate_is_out_of_row
#assert_axioms goodSpendRow_isRow
#assert_axioms goodSpendRow_realizes_intent
#assert_axioms badSpendRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
