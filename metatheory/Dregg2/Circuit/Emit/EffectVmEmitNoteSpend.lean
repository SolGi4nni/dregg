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

## THE DEEPER DIVERGENCE (reported §10): runtime CREDIT vs universe-A balance-NEUTRAL

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

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.notenullifier
import Dregg2.Exec.SystemRoots
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

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
  , piCount := 42
  , constraints := noteSpendRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 4
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
    (hgatesat : satisfiedVm hash noteSpendVmDescriptor env true false)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true) :
    CellSpendSpec pre value post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ noteSpendRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ noteSpendVmDescriptor.constraints := by
      unfold noteSpendVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
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
      exact Or.inl (Or.inr hc)
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
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash noteSpendVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ noteSpendVmDescriptor.constraints := by
        unfold noteSpendVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
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
  -- NoteSpendSpec: guard ∧ nullifiers ∧ log ∧ accounts ∧ cell ∧ caps ∧ revoked ∧
  --               commitments ∧ bal ∧ … — `bal` is the 9th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE DEEPER DIVERGENCE (reported): runtime CREDIT vs universe-A balance-NEUTRAL.

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
    (hgatesat : satisfiedVm hash noteSpendVmDescriptor env true false)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true)
    (hspec : NoteSpendSpec st nf actor spendProof st')
    (hagree : post.balLo = (cellProjSpend st'.kernel.bal c asset).balLo) :
    value = 0 := by
  obtain ⟨hcirc, _⟩ :=
    noteSpendDescriptor_full_sound hash env hrow (cellProjSpend st.kernel.bal c asset) post value henc hgatesat hsat
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

/-! ## §A — STAGE-3 AMPLIFICATION: bind the `nullifiers` side-table ROOT into the descriptor.

Record-layer STAGE 3 (`Exec.SystemRoots`, `6aa29e996`) homed each side-table root in the dedicated
`system_roots` sub-block, committed by `systemRootsDigest` into ONE carrier
(`aux_off_sys.SYSTEM_ROOTS_DIGEST`). For `noteSpend` the relevant root is `state.systemRoot.NULLIFIER`
(the `nullifiers` accumulator). BEFORE this stage the nullifier-set insert `nf :: nullifiers` was the
§11 finding-#1 OUT-OF-IR flag — there was no column to bind it. NOW there is. This section AMPLIFIES the
descriptor to FULL: a per-row root-UPDATE gate binds the `nullifiers`-accumulator step into the row, the
after-`SYSTEM_ROOTS_DIGEST` carrier is absorbed into `state_commit` by the GROUP-4 extension, and the
anti-ghost tooth is re-proved over the now-bound root, CONNECTED to
`Exec.SystemRoots.cellCommitS_binds_systemRoots`. The whole-cell FREEZE + universe-A connectors of
§4–§11 are UNCHANGED (strictly additive).

HONESTY (finding #2 still stands): binding the nullifier-set DIGEST closes finding #1 (the insert is
bound into `state_commit`), but it does NOT by itself enforce NO-DOUBLE-SPEND. Freshness
(`nf ∉ nullifiers`) is a NON-MEMBERSHIP assertion the per-row digest gate cannot make: even with the
root bound, a sorted-set / Merkle non-membership gate-kind is still required (the IR lacks it). We keep
`noteSpend_no_double_spend_is_turn_property` and state the precise boundary in §D. -/

open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise N_SYSTEM_ROOTS rootList)

/-- The committed `system_roots` digest carrier of the AFTER state (the kernel side-table digest the
GROUP-4 extension absorbs into `state_commit`). This is the IR's `aux_off_sys.SYSTEM_ROOTS_DIGEST`. -/
def SYS_DIG_AFTER : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST

/-- The committed `system_roots` digest carrier of the BEFORE state (the pre-image of the accumulator
step). One aux column past the after-carrier, DISTINCT from every claimed aux slot, so it never aliases.
The per-effect root-update gate reads `sb`-digest here and writes `sa`-digest at `SYS_DIG_AFTER`. -/
def SYS_DIG_BEFORE : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST + 1

/-- The `nullifiers`-accumulator STEP param: the field-element delta the consumed `nf` contributes to
the `nullifiers` side-table digest. The trace generator lays it at `param2` (param0 = nullifier `nf`,
param1 = value; param2 = the digest step the prover computed from `nf :: nullifiers`). -/
def NULLIFIER_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmNullifierStep : EmittedExpr := .var (prmCol NULLIFIER_ROOT_STEP_PARAM)

/-! ## §B — the root-UPDATE gate + the digest-absorbing GROUP-4 extension site. -/

/-- Root-update gate body: `sa_digest − sb_digest − step` (so `sa_digest = sb_digest + step`). Reads
the before/after `system_roots` digest carriers and the `param2` accumulator step. -/
def gNullifierRootUpdate : EmittedExpr :=
  eSub (eSub (.var SYS_DIG_AFTER) (.var SYS_DIG_BEFORE)) ePrmNullifierStep

/-- Site 3′: `state_commit = H4(inter1, inter2, inter3, sys_digest_after)` — the GROUP-4 extension that
absorbs the `system_roots` digest carrier into the published commitment (replacing transfer's spare
`.zero`). This is the column that makes the `nullifiers` root BINDABLE. -/
def siteNullifierRoot : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col SYS_DIG_AFTER ]
  , arity := 4 }

/-- The amplified GROUP-4 hash sites: transfer's three inner sites + the digest-absorbing site 3′. -/
def noteSpendRootHashSites : List VmHashSite :=
  [ EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1
  , EffectVmEmitTransfer.site2, siteNullifierRoot ]

/-- **`noteSpendRootHash_binds`** — under the amplified sites, the published `state_commit` is the
genuine 4-level digest of the after-state WITH the `system_roots` digest carrier in the 4th slot. -/
theorem noteSpendRootHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env noteSpendRootHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc SYS_DIG_AFTER ] := by
  unfold siteHoldsAll noteSpendRootHashSites at h
  simp only [siteHoldsAll.go, EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1,
    EffectVmEmitTransfer.site2, siteNullifierRoot, VmHashSite.resolvedInputs, HashInput.resolve,
    List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, _, _, h3, _⟩ := h
  rw [h3]; rfl

/-! ## §C — FAITHFULNESS of the root-update gate + ANTI-GHOST over the bound digest. -/

/-- **`NoteSpendRootIntent env`** — the intended `nullifiers`-root move on the row: the `system_roots`
digest ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
projection of the membership update `nullifiers := nf :: nullifiers` onto its committed digest. -/
def NoteSpendRootIntent (env : VmRowEnv) : Prop :=
  env.loc SYS_DIG_AFTER = env.loc SYS_DIG_BEFORE + env.loc (prmCol NULLIFIER_ROOT_STEP_PARAM)

/-- **`noteSpendRoot_gate_faithful`.** The root-update gate holds IFF the digest advances by the
accumulator step — the gate pins EXACTLY the `nullifiers`-root update. -/
theorem noteSpendRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gNullifierRootUpdate).holdsVm env false false ↔ NoteSpendRootIntent env := by
  simp only [VmConstraint.holdsVm, gNullifierRootUpdate, ePrmNullifierStep, eSub, EmittedExpr.eval,
    NoteSpendRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator
(`sb_digest + step`) is rejected by `gNullifierRootUpdate` — a dropped/forged `nullifiers` update is
UNSAT (an attacker omitting `nf` to enable a later double-spend MOVES the digest, breaking the gate). -/
theorem noteSpendRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc SYS_DIG_AFTER ≠ env.loc SYS_DIG_BEFORE + env.loc (prmCol NULLIFIER_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gNullifierRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((noteSpendRoot_gate_faithful env).mp h)

/-! ## §D — the AMPLIFIED descriptor + the side-table-root anti-ghost tooth (connected to `SystemRoots`). -/

/-- **`noteSpendVmDescriptorFull`** — the AMPLIFIED noteSpend circuit: the §2 whole-cell freeze gates
PLUS the `nullifiers`-root-update gate, with the digest-absorbing GROUP-4 sites. Strictly additive over
`noteSpendVmDescriptor` (one extra gate, the spare site-3 slot filled). -/
def noteSpendVmDescriptorFull : EffectVmDescriptor :=
  { name := noteSpendVmAirName ++ "-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := (noteSpendRowGates ++ [.gate gNullifierRootUpdate])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := noteSpendRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The amplified descriptor still forces the §2 whole-cell FREEZE (generalised over the boundary flags;
the freeze gates are per-row `.gate`s whose `holdsVm` ignores `isFirst`/`isLast`). -/
theorem noteSpendFull_forces_freeze (env : VmRowEnv) (hrow : IsNoteSpendRow env) (b1 : Bool)
    (hgates : ∀ c ∈ noteSpendVmDescriptorFull.constraints, c.holdsVm env b1 false) :
    NoteSpendRowIntent env := by
  apply (noteSpendVm_faithful env hrow).mp
  intro c hc
  have hmem : c ∈ noteSpendVmDescriptorFull.constraints := by
    unfold noteSpendVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have := hgates c hmem
  unfold noteSpendRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- The amplified descriptor forces the `nullifiers`-ROOT update (the new content STAGE 3 buys). -/
theorem noteSpendFull_forces_root (env : VmRowEnv) (b1 : Bool)
    (hgates : ∀ c ∈ noteSpendVmDescriptorFull.constraints, c.holdsVm env b1 false) :
    NoteSpendRootIntent env := by
  apply (noteSpendRoot_gate_faithful env).mp
  have hmem : (VmConstraint.gate gNullifierRootUpdate) ∈ noteSpendVmDescriptorFull.constraints := by
    unfold noteSpendVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-- **`noteSpendFull_commit_binds_sysdigest` — the digest is now bound into `state_commit`.** Two rows
satisfying the amplified hash-sites that publish the SAME `state_commit` have the SAME absorbed
`system_roots` digest. So a prover CANNOT keep `state_commit` while tampering the side-table digest —
finding #1 (the nullifier insert out-of-IR) is CLOSED. -/
theorem noteSpendFull_commit_binds_sysdigest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ noteSpendRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ noteSpendRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER := by
  rw [noteSpendRootHash_binds hash e₁ hs₁, noteSpendRootHash_binds hash e₂ hs₂] at hcommit
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  exact houter.2.2.2.1

/-- **`noteSpendFull_binds_nullifiers_root` — CONNECTED to `Exec.SystemRoots`.** Two amplified rows
that publish the same `state_commit` AND whose after-digest carrier IS the `systemRootsDigest` of their
respective `system_roots` sub-blocks have the SAME `nullifiers` side-table root (and every other). The
chain: equal commitment ⇒ equal digest carrier ⇒ equal side-table roots pointwise. Tampering ONLY the
`nullifiers` root (omitting `nf`) provably MOVES `state_commit` ⇒ UNSAT. -/
theorem noteSpendFull_binds_nullifiers_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ noteSpendRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ noteSpendRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc SYS_DIG_AFTER = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc SYS_DIG_AFTER = systemRootsDigest hash sr₂)
    (i : Fin N_SYSTEM_ROOTS) :
    sr₁ i = sr₂ i := by
  have hdig : systemRootsDigest hash sr₁ = systemRootsDigest hash sr₂ := by
    rw [← hd₁, ← hd₂]
    exact noteSpendFull_commit_binds_sysdigest hash hCR e₁ e₂ hs₁ hs₂ hcommit
  exact systemRootsDigest_binds_pointwise hash hCR sr₁ sr₂ hdig i

/-! ## §E — CONNECTOR to universe-A `noteSpendDescriptor_full_sound` over the root-bound descriptor. -/

/-- **`noteSpendFull_sound` — the amplified full soundness.** A row satisfying the AMPLIFIED descriptor,
under `RowEncodesSpend`, forces the structured `CellSpendSpec` freeze AND the `nullifiers`-root advance
AND publishes the post-commit — §7 lifted onto the root-bound descriptor. -/
theorem noteSpendFull_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteSpendRow env)
    (pre post : CellState) (value : ℤ)
    (henc : RowEncodesSpend env pre value post)
    (hgatesat : satisfiedVm hash noteSpendVmDescriptorFull env true false)
    (hsat : satisfiedVm hash noteSpendVmDescriptorFull env true true) :
    CellSpendSpec pre value post
      ∧ NoteSpendRootIntent env
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hfreeze := noteSpendFull_forces_freeze env hrow true hcsT
  have hroot := noteSpendFull_forces_root env true hcsT
  refine ⟨intent_to_cellSpendSpec env pre post value henc hfreeze, hroot, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ noteSpendVmDescriptorFull.constraints := by
      unfold noteSpendVmDescriptorFull
      simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §F — the no-DOUBLE-SPEND boundary AFTER amplification (finding #2, NOT closed by the root).

The root binding closes finding #1: `nf :: nullifiers` is now committed (its digest is bound into
`state_commit`, anti-ghost-proved above). But it does NOT enforce FRESHNESS. Even with the digest bound,
the gate `gNullifierRootUpdate` only asserts the digest ADVANCED by `step`; it cannot witness that `nf`
was NOT already a member of the accumulated set. That is a NON-MEMBERSHIP / sorted-insert assertion the
4-arity Poseidon2 hash-site IR has no gate-kind for. We RESTATE the boundary precisely. -/

/-- **`noteSpend_freshness_still_needs_nonmembership` — finding #2 after amplification.** The universe-A
freshness guard (`nf ∉ st.nullifiers`) — the headline anti-replay property — is STILL a property of the
whole accumulated nullifier SET, NOT of the per-row digest-advance gate. The root binding commits the
post-set; it does not prove `nf` was absent from the pre-set. So `noteSpendVmDescriptorFull` enforces
the insert is COMMITTED but NOT that it is FRESH: a sorted-set / Merkle NON-membership gate-kind is
still required (the IR lacks it). We extract the guard from the spec to name the boundary exactly. -/
theorem noteSpend_freshness_still_needs_nonmembership (st st' : RecChainedState)
    (nf : Nat) (actor : CellId) (spendProof : Bool)
    (hspec : NoteSpendSpec st nf actor spendProof st') :
    nf ∉ st.kernel.nullifiers :=
  hspec.1.2

/-! ## §G — RECONCILIATION onto the runtime trace-generator layout (the cutover discipline, `3aaf0772d`). -/

-- The amplified descriptor reads the kernel digest carrier (aux 96), not a user field.
#guard SYS_DIG_AFTER == aux_off_sys.SYSTEM_ROOTS_DIGEST
#guard SYS_DIG_AFTER == 96
-- The before-carrier is DISTINCT from every claimed aux slot (state-inters + after-digest).
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        SYS_DIG_AFTER, SYS_DIG_BEFORE].dedup.length == 5
-- The accumulator-step param is param2 (param0 = nf, param1 = value), in-range of the 8 param cols.
#guard NULLIFIER_ROOT_STEP_PARAM == 2
#guard NULLIFIER_ROOT_STEP_PARAM < NUM_PARAMS
-- The amplified descriptor has the extra root-update gate (14 row gates now) + the 4 amplified sites.
#guard noteSpendVmDescriptorFull.constraints.length == 14 + 14 + 4 + 3
#guard noteSpendVmDescriptorFull.hashSites.length == 4

/-! ## §H — NON-VACUITY of the amplification: a concrete root-advancing row + a forged one. -/

/-- A concrete root-update row: `sys_digest 1000 → 1099` (advance by step `99` = the consumed `nf`'s
digest contribution). -/
def goodNullRow : VmRowEnv where
  loc := fun v =>
    if v = SYS_DIG_BEFORE then 1000
    else if v = SYS_DIG_AFTER then 1099
    else if v = prmCol NULLIFIER_ROOT_STEP_PARAM then 99
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodNullRow` REALIZES the `nullifiers`-root advance:
`1099 = 1000 + 99`. -/
theorem goodNullRow_realizes : NoteSpendRootIntent goodNullRow := by
  unfold NoteSpendRootIntent goodNullRow
  simp only [SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, NULLIFIER_ROOT_STEP_PARAM,
    aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-- A FORGED root row: the after-digest is `9999` (NOT the advance `1099`) — a dropped/forged
`nullifiers` update (an attacker omitting `nf` to enable a double-spend). -/
def badNullRow : VmRowEnv where
  loc := fun v => if v = SYS_DIG_AFTER then 9999 else goodNullRow.loc v
  nxt := goodNullRow.nxt
  pub := goodNullRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badNullRow`'s after-digest is NOT the
advance, so `gNullifierRootUpdate` REJECTS it — the bound root has teeth. -/
theorem badNullRow_rejected : ¬ (VmConstraint.gate gNullifierRootUpdate).holdsVm badNullRow false false := by
  apply noteSpendRoot_rejects_wrong_root
  simp only [badNullRow, goodNullRow, SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, NULLIFIER_ROOT_STEP_PARAM,
    aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-! ## §W — FULL-STATE ON THE RUNNABLE DESCRIPTOR (the magnesium breadth — the GENERIC crown).

§A–§G amplified the descriptor over the OLD raw `SYS_DIG_AFTER = aux 96` carrier with the bespoke
`noteSpendVmDescriptorFull`. THIS section lifts noteSpend to the GENERIC full-state-on-RUNNABLE crown
`EffectVmFullStateRunnable.runnable_full_sound` — the analog of `transferRunnableSpec` — over the
DEDICATED, non-aliasing `sysRootsDigestCol = 186` carrier and the shared `wideHashSites` (so the crypto /
anti-ghost is discharged ONCE in the generic theorem and the whole-17-field anti-ghost falls out of
`wide_rejects_state_tamper`/`wide_rejects_root_tamper`). The per-effect content is THIN: the wide
descriptor, the root-update gate over the dedicated carrier, the structured decode, and `decodeFull`
(reusing §4's `noteSpendVm_faithful` + the root-gate faithfulness). NO new crypto portal.

This binds the FULL post-state: the per-cell block (transparent CREDIT + nonce tick — the RUNTIME image,
fields 1–3 of the §0 census) AND all 8 side-table roots (fields 4–12 — the `nullifiers` root ADVANCES by
the accumulator step, every OTHER side-table root FROZEN). So a satisfying wide-descriptor witness pins
the 17-field post-state the noteSpend RUNTIME executor produces, and tamper of ANY field/root is UNSAT.

HONESTY (finding #2 + §10 still stand, UNAFFECTED): (a) binding the `nullifiers` DIGEST is NOT the
no-double-spend FRESHNESS gate (`nf ∉ nullifiers` is a non-membership assertion the digest-advance gate
cannot make — `noteSpend_freshness_still_needs_nonmembership`; the genuine non-membership circuit lives in
`Argus/Effects/NoteSpend.lean`, to be bound to this carrier by a sorted-tree opening). (b) the per-cell
clause is the RUNTIME credit `CellSpendSpec`; the universe-A balance-NEUTRAL convention diverges
(`runtime_credit_vs_univA_neutral_divergence`) — this wide descriptor binds the RUNTIME post-state it
actually enforces, the named divergence is orthogonal. -/

open EffectVmFullStateRunnable
  (wideHashSites baseAbsorbedCols RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Emit.EffectVmEmit (sysRootsDigestCol sysRootsDigestColBefore EFFECT_VM_WIDTH_SYSROOTS)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (RowEncodes CellState)

/-! ### §W.1 — the root-UPDATE gate over the DEDICATED carrier (`sysRootsDigestCol`/`…Before`).

Unlike §B's `gNullifierRootUpdate` (which reads the raw aux-96 `SYS_DIG_AFTER`, inside the balance-bit
block), this gate reads the dedicated, non-aliasing `sysRootsDigestCol = 186` / `sysRootsDigestColBefore
= 187` carriers the wide IR added — the exact column the `wideHashSites` absorb. -/

/-- Root-update gate body over the DEDICATED carrier: `sa_sysdig − sb_sysdig − step` (so
`sysRootsDigestCol = sysRootsDigestColBefore + step`), reading the dedicated `system_roots` carriers
(186/187) and the `param2` accumulator step. The wide analog of `gNullifierRootUpdate`. -/
def gNullifierRootUpdateWide : EmittedExpr :=
  eSub (eSub (.var sysRootsDigestCol) (.var sysRootsDigestColBefore)) ePrmNullifierStep

/-- **`NoteSpendRootIntentWide env`** — the dedicated-carrier root move: the `system_roots` digest at
`sysRootsDigestCol` ADVANCES by the `param2` step over `sysRootsDigestColBefore`. -/
def NoteSpendRootIntentWide (env : VmRowEnv) : Prop :=
  env.loc sysRootsDigestCol
    = env.loc sysRootsDigestColBefore + env.loc (prmCol NULLIFIER_ROOT_STEP_PARAM)

/-- **`gNullifierRootUpdateWide_faithful`.** The wide root-update gate holds IFF the dedicated-carrier
digest advances by the accumulator step. -/
theorem gNullifierRootUpdateWide_faithful (env : VmRowEnv) :
    (VmConstraint.gate gNullifierRootUpdateWide).holdsVm env false false ↔ NoteSpendRootIntentWide env := by
  simp only [VmConstraint.holdsVm, gNullifierRootUpdateWide, ePrmNullifierStep, eSub, EmittedExpr.eval,
    NoteSpendRootIntentWide]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### §W.2 — the WIDE descriptor (dedicated carrier + `wideHashSites`). -/

/-- **`noteSpendVmDescriptorWide`** — noteSpend's WIDE runnable descriptor: the §2 whole-cell credit/freeze
gates PLUS the dedicated-carrier `nullifiers`-root-update gate ++ transition continuity ++ the 7 boundary
PI pins ++ the selector-binding gate, with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and `hashSites :=
wideHashSites`. The `system_roots`-absorbing analog of `transferVmDescriptorWide`. -/
def noteSpendVmDescriptorWide : EffectVmDescriptor :=
  { name := noteSpendVmAirName ++ "-sysroots"
  , traceWidth := EFFECT_VM_WIDTH_SYSROOTS
  , piCount := 42
  , constraints := (noteSpendRowGates ++ [.gate gNullifierRootUpdateWide])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_NOTE_SPEND
  , hashSites := wideHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The wide descriptor's hash-sites ARE the shared `wideHashSites`. -/
theorem noteSpendWide_usesWideSites : noteSpendVmDescriptorWide.hashSites = wideHashSites := rfl

/-- **`noteSpendWide_forces_credit`** — the wide descriptor still forces the §2 whole-cell credit/freeze
intent (`NoteSpendRowIntent`); the gates are a sublist of the wide constraints, all per-row `.gate`s. -/
theorem noteSpendWide_forces_credit (env : VmRowEnv) (hrow : IsNoteSpendRow env) (b1 : Bool)
    (hgates : ∀ c ∈ noteSpendVmDescriptorWide.constraints, c.holdsVm env b1 false) :
    NoteSpendRowIntent env := by
  apply (noteSpendVm_faithful env hrow).mp
  intro c hc
  have hmem : c ∈ noteSpendVmDescriptorWide.constraints := by
    unfold noteSpendVmDescriptorWide
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))
  have := hgates c hmem
  unfold noteSpendRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`noteSpendWide_forces_root`** — the wide descriptor forces the dedicated-carrier `nullifiers`-root
advance. -/
theorem noteSpendWide_forces_root (env : VmRowEnv) (b1 : Bool)
    (hgates : ∀ c ∈ noteSpendVmDescriptorWide.constraints, c.holdsVm env b1 false) :
    NoteSpendRootIntentWide env := by
  apply (gNullifierRootUpdateWide_faithful env).mp
  have hmem : (VmConstraint.gate gNullifierRootUpdateWide) ∈ noteSpendVmDescriptorWide.constraints := by
    unfold noteSpendVmDescriptorWide
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp)))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-! ### §W.3 — the DECLARATIVE full 17-field post-state clause + the structured decode. -/

/-- **`NoteSpendFullClause hash value preRoots postRoots step`** — the full declarative 17-field post-state
for a noteSpend over `(pre, post, pr)`: the per-cell RUNTIME `CellSpendSpec` (transparent CREDIT by `value`
+ nonce tick — fields 1–3), the decoded roots `pr = postRoots`, the `nullifiers`-root committed-digest
advance (`systemRootsDigest postRoots = systemRootsDigest preRoots + step` — field 5), and every
NON-`NULLIFIER` side-table root FROZEN (fields 4,6–12). 13–17 ride the per-cell value's restLimbs (the
named factoring). -/
def NoteSpendFullClause (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (pre post : CellState) (pr : SysRoots) : Prop :=
  CellSpendSpec pre value post
  ∧ pr = postRoots
  ∧ Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
      = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots + step
  ∧ (∀ i : Fin N_SYSTEM_ROOTS, i.val ≠ Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER → postRoots i = preRoots i)

/-- **`NoteSpendDecode hash value preRoots postRoots step env pre post pr`** — the structured row decode:
the cell block + param value is `RowEncodesSpend`, the decoded roots are `postRoots`, the dedicated
carriers ARE the `systemRootsDigest` of `postRoots`/`preRoots`, the `param2` step is `step`, AND the
off-row witness data (the `nullifiers`-root digest advance + non-`NULLIFIER` freeze) hold. -/
def NoteSpendDecode (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (pr : SysRoots) : Prop :=
  RowEncodesSpend env pre value post
  ∧ pr = postRoots
  ∧ env.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
  ∧ env.loc sysRootsDigestColBefore = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots
  ∧ env.loc (prmCol NULLIFIER_ROOT_STEP_PARAM) = step
  ∧ (∀ i : Fin N_SYSTEM_ROOTS, i.val ≠ Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER → postRoots i = preRoots i)

/-! ### §W.4 — THE INSTANCE + the crown `noteSpend_runnable_full_sound`. -/

/-- **`noteSpendRunnableSpec hash value preRoots postRoots step`** — noteSpend's `RunnableFullStateSpec`.
`decodeAfter` is `NoteSpendDecode`; `fullClause` is `NoteSpendFullClause`; `decodeFull` projects the wide
descriptor's credit/freeze gates to `CellSpendSpec` (via `noteSpendWide_forces_credit` +
`intent_to_cellSpendSpec`) and the dedicated-carrier root gate to the digest advance. THIN; NON-VACUOUS
(§W.5). -/
def noteSpendRunnableSpec (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ) :
    RunnableFullStateSpec CellState where
  descriptor    := noteSpendVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsNoteSpendRow
  decodeAfter   := NoteSpendDecode hash value preRoots postRoots step
  fullClause    := NoteSpendFullClause hash value preRoots postRoots step
  decodeFull    := by
    intro env pre post pr hrow hdec hgates
    obtain ⟨henc, hpr, hdigA, hdigB, hstep, hfreezeRoots⟩ := hdec
    have hcredit := noteSpendWide_forces_credit env hrow true hgates
    have hcell := intent_to_cellSpendSpec env pre post value henc hcredit
    have hrootW := noteSpendWide_forces_root env true hgates
    have hadvance : Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
        = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots + step := by
      have := hrootW
      unfold NoteSpendRootIntentWide at this
      rw [hdigA, hdigB, hstep] at this
      exact this
    exact ⟨hcell, hpr, hadvance, hfreezeRoots⟩

/-- **`noteSpend_runnable_full_sound` — THE CROWN (full-state on the RUNNABLE descriptor).** A row
satisfying noteSpend's WIDE runnable descriptor (`satisfiedVm noteSpendVmDescriptorWide`, first/last
active), under the structured decode `NoteSpendDecode`, pins the FULL 17-field declarative post-state
`NoteSpendFullClause`: the per-cell transparent credit + nonce tick (the RUNTIME image), the `nullifiers`-
root committed-digest advance by the accumulator step, and every OTHER side-table root frozen. This is the
generic `runnable_full_sound` instantiated at `noteSpendRunnableSpec`. (The no-double-spend FRESHNESS leg
is NOT a per-row digest fact — see `noteSpend_freshness_still_needs_nonmembership` + the genuine
non-membership circuit in `Argus/Effects/NoteSpend.lean`.) -/
theorem noteSpend_runnable_full_sound (hash : List ℤ → ℤ)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (pr : SysRoots)
    (hrow : IsNoteSpendRow env)
    (hdec : NoteSpendDecode hash value preRoots postRoots step env pre post pr)
    (hgatesat : satisfiedVm hash noteSpendVmDescriptorWide env true false) :
    NoteSpendFullClause hash value preRoots postRoots step pre post pr :=
  runnable_full_sound (noteSpendRunnableSpec hash value preRoots postRoots step) hash env pre post pr
    hrow hdec hgatesat

/-- **`noteSpend_runnable_rejects_root_tamper` — the side-table anti-ghost (free from the generic crown).**
Two wide rows publishing the SAME `NEW_COMMIT` (with `systemRootsDigest` carriers) but whose `system_roots`
sub-blocks DIFFER at some index (a dropped/omitted `nullifiers` update — an attacker omitting `nf` to
enable a later double-spend, OR any other side-table root tampered) cannot BOTH satisfy — UNSAT. The
whole-17-field anti-ghost tooth, from `wide_rejects_root_tamper`. -/
theorem noteSpend_runnable_rejects_root_tamper (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash noteSpendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash noteSpendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (noteSpendRunnableSpec hash value preRoots postRoots step) hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`noteSpend_runnable_rejects_state_tamper` — the per-cell-block anti-ghost (free).** Two wide rows
publishing the same `NEW_COMMIT` but whose absorbed state-block columns (balance/nonce/fields/cap) DIFFER
cannot both satisfy — a forged credit / tampered field / forged cap-root that still claims the published
commitment is UNSAT. From `wide_rejects_state_tamper`. -/
theorem noteSpend_runnable_rejects_state_tamper (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash noteSpendVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash noteSpendVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂)
    (htamper : baseAbsorbedCols e₁ ≠ baseAbsorbedCols e₂) : False :=
  wide_rejects_state_tamper (noteSpendRunnableSpec hash value preRoots postRoots step) hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### §W.5 — NON-VACUITY of the wide instance: the full clause is INHABITED + REFUTABLE. -/

/-- A concrete frozen reference sub-block (every side-table empty before the spend). -/
def wPreRootsS : SysRoots := Dregg2.Exec.SystemRoots.emptySystemRoots

/-- A concrete post sub-block: the `nullifiers` (NULLIFIER) root advanced to `9`, every other root still
empty (the genuine "only the touched root moved" shape). -/
def wPostRootsS : SysRoots := fun i =>
  if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.NULLIFIER, by decide⟩ : Fin N_SYSTEM_ROOTS) then 9 else 0

/-- The honest cell pre/post for the witness: transparent credit `100 → 130` (value `30`), nonce `5 → 6`,
frame frozen. -/
def wPreS : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }
def wPostS : CellState :=
  { balLo := 130, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`noteSpend_fullClause_inhabited` — NON-VACUITY (witness TRUE).** The full clause is inhabited by a
real spend: transparent credit `100 → 130` + nonce tick, the `nullifiers` root digest advanced by the
genuine step, every other root frozen. So `NoteSpendFullClause` is a MEANINGFUL 17-field predicate a real
noteSpend satisfies, not `True`. -/
theorem noteSpend_fullClause_inhabited (hash : List ℤ → ℤ) :
    NoteSpendFullClause hash 30 wPreRootsS wPostRootsS
      (Dregg2.Exec.SystemRoots.systemRootsDigest hash wPostRootsS
        - Dregg2.Exec.SystemRoots.systemRootsDigest hash wPreRootsS)
      wPreS wPostS wPostRootsS := by
  refine ⟨?_, rfl, by ring, ?_⟩
  · -- CellSpendSpec wPreS 30 wPostS: balLo = 100 + 30 = 130, balHi frozen, nonce+1, frame frozen.
    refine ⟨by norm_num [wPreS, wPostS], rfl, by norm_num [wPreS, wPostS], ?_, rfl, rfl⟩
    intro i; rfl
  · -- every NON-NULLIFIER root is frozen at 0.
    intro i hi
    simp only [wPostRootsS, wPreRootsS, Dregg2.Exec.SystemRoots.emptySystemRoots]
    rw [if_neg]
    intro hcontra
    exact hi (by rw [hcontra])

/-- **`noteSpend_fullClause_refutable` — NON-VACUITY (witness FALSE).** A post-state whose `balLo` is a
forged `999` (NOT the credit `130`) FAILS `CellSpendSpec`, so `NoteSpendFullClause` is REFUTABLE — the
clause rejects a forged transparent credit, pinning non-vacuity from both sides. -/
theorem noteSpend_fullClause_refutable (hash : List ℤ → ℤ) :
    ¬ NoteSpendFullClause hash 30 wPreRootsS wPostRootsS
        (Dregg2.Exec.SystemRoots.systemRootsDigest hash wPostRootsS
          - Dregg2.Exec.SystemRoots.systemRootsDigest hash wPreRootsS)
        wPreS { wPostS with balLo := 999 } wPostRootsS := by
  rintro ⟨⟨hbal, _⟩, _⟩
  -- hbal : (999) = wPreS.balLo + 30 = 130
  simp only [wPreS] at hbal
  norm_num at hbal

/-! ### §W.6 — RECONCILIATION pins (the wide descriptor's shape). -/

-- The wide descriptor carries the widened trace width + the dedicated carrier (NOT the old aux-96).
#guard noteSpendVmDescriptorWide.traceWidth == 190
#guard noteSpendVmDescriptorWide.hashSites.length == 4
-- 13 credit/freeze gates + 1 wide-root gate + 14 transitions + 4 boundaryFirst + 3 boundaryLast + 1 selector.
#guard noteSpendVmDescriptorWide.constraints.length == 13 + 1 + 14 + 4 + 3 + 1
-- The wide root gate reads the DEDICATED carriers (187/188), never the old aux-96 (96).
#guard sysRootsDigestCol == 188
#guard sysRootsDigestColBefore == 189
#guard decide (sysRootsDigestCol ≠ SYS_DIG_AFTER)

#assert_axioms gNullifierRootUpdateWide_faithful
#assert_axioms noteSpendWide_forces_credit
#assert_axioms noteSpendWide_forces_root
#assert_axioms noteSpend_runnable_full_sound
#assert_axioms noteSpend_runnable_rejects_root_tamper
#assert_axioms noteSpend_runnable_rejects_state_tamper
#assert_axioms noteSpend_fullClause_inhabited
#assert_axioms noteSpend_fullClause_refutable

/-! ## §13 — Axiom-hygiene pins. -/

#guard noteSpendVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard noteSpendVmDescriptor.hashSites.length == 4
#guard noteSpendVmDescriptor.traceWidth == 188

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

-- STAGE-3 amplification (the bound `nullifiers` side-table root):
#assert_axioms noteSpendRootHash_binds
#assert_axioms noteSpendRoot_gate_faithful
#assert_axioms noteSpendRoot_rejects_wrong_root
#assert_axioms noteSpendFull_forces_freeze
#assert_axioms noteSpendFull_forces_root
#assert_axioms noteSpendFull_commit_binds_sysdigest
#assert_axioms noteSpendFull_binds_nullifiers_root
#assert_axioms noteSpendFull_sound
#assert_axioms noteSpend_freshness_still_needs_nonmembership
#assert_axioms goodNullRow_realizes
#assert_axioms badNullRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
