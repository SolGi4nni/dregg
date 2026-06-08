/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteCreate — the noteCreate (note-COMMITMENT publish) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/noteCreateA.lean`, `Spec/notecommitment.lean`) carries the FULL-state soundness
`execNoteCreateA_iff_spec ⇒ NoteCreateASpec`: a committed publish PREPENDS a fresh commitment `cm`
onto the `commitments` SET, advances the chained `log` by `escrowReceiptA actor ::`, and is otherwise
TOTALLY NEUTRAL — it is balance-neutral (`noteCreateA_bal_neutral`) and FREEZES all 16 other kernel
fields. `noteCreate` is the APPEND-ONLY dual of `noteSpend`: NO guard at all (always commits).

## RECONCILED ONTO THE RUNTIME (cutover): TRANSPARENT DEBIT + nonce TICK

This descriptor is RECONCILED onto the validated runtime hand-AIR + `generate_effect_vm_trace`, which
model a noteCreate as a TRANSPARENT DEBIT: the published `value` (read from `param1`, the trace
convention) LEAVES the transparent `bal_lo` pool (`new_bal_lo = old_bal_lo − value`), the runtime nonce
TICKS by one (the per-cell sequence counter, as on every non-NoOp row), and bal_hi / cap_root / reserved
/ the 8 fields are FROZEN; the post-state binds into `state_commit` via the SAME GROUP-4 chain as
transfer. So `noteCreateVmDescriptor` and the hand-AIR AGREE on the honest trace (the cutover
differential passes), and any wrong-debit / wrong-nonce / mutated-frame row is UNSAT.

## THE DEEPER DIVERGENCE (reported §9, NOT papered): runtime DEBIT vs universe-A balance-NEUTRAL

Universe-A's `NoteCreateASpec` models the publish as BALANCE-NEUTRAL commitment accumulation
(`noteCreateA_bal_neutral : bal' = bal`) — a DIFFERENT shielding convention (value hidden in the
commitment, never moved on the transparent ledger). The runtime debit and the universe-A neutral
convention are reconcilable ONLY for a zero-value note (`runtime_debit_vs_univA_neutral_divergence`):
a genuine semantic modeling gap, NOT a column index. We surface it as a theorem rather than unifying.

## THE IR-EXTENSION FLAG (the commitment-set insert — the LOAD-BEARING leg, out-of-IR)

The actual effect — `commitments := cm :: commitments` — is a SET-INSERT into the commitment
accumulator. The EffectVM 14-column block has NO commitment-root column, and the GROUP-4 hash-sites
absorb none of the `commitments` list. So the per-row circuit CANNOT bind, or even witness, the
published commitment `cm` or its insertion.

  ⇒ **needs IR extension: a commitments-accumulator-root column in the EffectVM state block (a 15th
     data column, or a repurposed named field `COMMIT_ROOT`) absorbed by a new hash-site, plus a param
     column carrying the published `cm`, so the membership update `cm :: commitments` is bound into the
     published `state_commit`.** Universe A binds it via the `commitmentsComponent` list digest; the
     EffectVM row has no counterpart column. This module proves what the IR DOES support (the whole
     state-block FREEZE + the 14-column commitment) and reports the commitment-set insert as out-of-IR
     — NOT papered. The append-only "no double-check" / freshness is likewise a TURN/ACCUMULATOR
     property over the `commitments` SET, stated honestly out-of-row.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.notecommitment

namespace Dregg2.Circuit.Emit.EffectVmEmitNoteCreate

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

/-! ## §0 — The noteCreate selector. -/

/-- The note-commitment-publish selector column index (`sel::NOTE_CREATE`). -/
def SEL_NOTE_CREATE : Nat := 5

/-- The publish row is a noteCreate row: `s_note_create = 1`, `s_noop = 0`. -/
def IsNoteCreateRow (env : VmRowEnv) : Prop :=
  env.loc SEL_NOTE_CREATE = 1 ∧ env.loc sel.NOOP = 0

/-! ### NoteCreate value column (the running trace generator's convention).

`generate_effect_vm_trace`'s `Effect::NoteCreate` arm lays `param0 = commitment`, `param1 = value_lo`
(the note value), and DEBITS the cell's transparent balance by that value (`new_state.balance -= value`);
the hand-AIR's note-create gate reads `prm(1)` (= `nc_val_lo`) and asserts `new_bal_lo = old_bal_lo −
value`. The descriptor MUST match the runtime: a transparent DEBIT into the shielded note, read from
`param1`. (See the §9 divergence finding: universe-A's `NoteCreateASpec` models the publish as
balance-NEUTRAL commitment accumulation, a DIFFERENT shielding convention than the runtime's transparent
debit — reported, not papered.) -/
namespace param
/-- NoteCreate value lives at param column 1 (`columns.rs::param::NOTE_VALUE_LO`). -/
def NOTE_VALUE_LO : Nat := 1
end param

/-- NoteCreate value as an expression (param column 1). -/
def ePrmNoteValue : EmittedExpr := .var (prmCol param.NOTE_VALUE_LO)

/-! ## §1 — The per-row gate bodies (transparent DEBIT + nonce TICK + frame freeze).

A noteCreate DEBITS the transparent `bal_lo` by `value` (the value leaves the transparent pool into the
shielded note), TICKS the runtime nonce (as every non-NoOp EffectVM row does), and FREEZES the rest of
the block. bal_hi / cap_root / reserved / the 8 fields freeze bodies are REUSED from the transfer
template (identical polynomials). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + value` (so `new = old − value`), reading the note
value from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmNoteValue

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a noteCreate row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce

/-! ## §2 — The emitted descriptor. -/

/-- The note-commitment-publish AIR identity. -/
def noteCreateVmAirName : String := "dregg-effectvm-notecreate-v1"

/-- The per-row gates: bal_lo DEBIT, bal_hi freeze, nonce TICK, cap/reserved freeze, 8 fields freeze. -/
def noteCreateRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`noteCreateVmDescriptor`** — the noteCreate effect's concrete EffectVM circuit: the per-row
WHOLE-block freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED — the post-state commitment chain binds the frozen block) and the 2 balance-limb
range checks. -/
def noteCreateVmDescriptor : EffectVmDescriptor :=
  { name := noteCreateVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := noteCreateRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT (the independent faithfulness target): the WHOLE state block frozen. -/

/-- **`NoteCreateRowIntent env`** — the intended noteCreate move on the row `env.loc`: the transparent
`bal_lo` is DEBITED by the `param1` value (the value leaves the transparent pool into the shielded note),
the runtime nonce TICKS by one, and balHi/cap/reserved/8 fields are FROZEN. The actual commitment-set
insert is out-of-row (the §IR flag). -/
def NoteCreateRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.NOTE_VALUE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the debit/tick intent. -/

/-- **`noteCreateVm_faithful`.** On a noteCreate row, the emitted descriptor's per-row gates all hold
IFF `NoteCreateRowIntent` holds — the gates pin EXACTLY the transparent debit + nonce tick + frame freeze
that the runtime hand-AIR enforces. -/
theorem noteCreateVm_faithful (env : VmRowEnv) (hrow : IsNoteCreateRow env) :
    (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) ↔ NoteCreateRowIntent env := by
  obtain ⟨_hsNC, hsN⟩ := hrow
  unfold noteCreateRowGates gFieldPassAll NoteCreateRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
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
    · simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmNoteValue, eSA, eSB, eSub, EmittedExpr.eval]
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

/-! ## §5 — ANTI-GHOST: a row whose post-`bal_lo` is NOT the debit on a noteCreate is rejected. -/

/-- **Anti-ghost (general).** A noteCreate row that does NOT realize the debit/tick intent does NOT
satisfy the per-row gates. -/
theorem noteCreateVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (hwrong : ¬ NoteCreateRowIntent env) :
    ¬ (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((noteCreateVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A noteCreate row whose post-`bal_lo` is NOT the debit
`old − value` has no satisfying gate set — `gBalLoDebit` alone rejects it (UNSAT). -/
theorem noteCreateVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.NOTE_VALUE_LO)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmNoteValue, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesNote env pre value post` ties the row's state-block columns + the `param1` value to a
`(pre, value, post)` cell transition. -/
def RowEncodesNote (env : VmRowEnv) (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
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

/-- **`CellNoteSpec pre value post`** — the per-cell FULL-state noteCreate spec (the RUNTIME image): the
transparent `balLo` is DEBITED by `value`, balHi/8-fields/cap/reserved frozen, nonce TICKED by one. This
is the EffectVM-row projection of the validated runtime hand-AIR's note-create transition (a transparent
debit into the shielded note). See §9 for the universe-A divergence (balance-NEUTRAL convention). -/
def CellNoteSpec (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo - value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesNote`, `NoteCreateRowIntent` IS the structured `CellNoteSpec`. -/
theorem intent_to_cellNoteSpec (env : VmRowEnv) (pre post : CellState) (value : ℤ)
    (henc : RowEncodesNote env pre value post) (hint : NoteCreateRowIntent env) :
    CellNoteSpec pre value post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpVal,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.NOTE_VALUE_LO) := by
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

/-- **`noteCreateDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesNote`, forces the structured per-cell FREEZE `CellNoteSpec` AND publishes the post-commit
as `PI[NEW_COMMIT]`. -/
theorem noteCreateDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (pre post : CellState) (value : ℤ)
    (henc : RowEncodesNote env pre value post)
    (hsat : satisfiedVm hash noteCreateVmDescriptor env true true) :
    CellNoteSpec pre value post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ noteCreateRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ noteCreateVmDescriptor.constraints := by
      unfold noteCreateVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold noteCreateRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (noteCreateVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellNoteSpec env pre post value henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ noteCreateVmDescriptor.constraints := by
      unfold noteCreateVmDescriptor
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

/-- **`noteCreateDescriptor_commit_binds_state`** — two descriptor-satisfying noteCreate rows publishing
the SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT`
while tampering any absorbed cell of the (frozen) post-state. -/
theorem noteCreateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash noteCreateVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash noteCreateVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash noteCreateVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ noteCreateVmDescriptor.constraints := by
        unfold noteCreateVmDescriptor
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

/-! ## §9 — THE DEEPER DIVERGENCE (reported, NOT papered): runtime DEBIT vs universe-A balance-NEUTRAL.

The validated RUNTIME hand-AIR + `generate_effect_vm_trace` model a noteCreate as a TRANSPARENT DEBIT:
the published `value` LEAVES the transparent `bal_lo` pool (`new_bal_lo = old_bal_lo − value`). This is
what `noteCreateVmDescriptor` now faithfully describes (so the cutover differential AGREES with the
hand-AIR). Universe-A's `NoteCreateASpec`, by contrast, models the publish as BALANCE-NEUTRAL commitment
accumulation (`noteCreateA_bal_neutral : bal' = bal`) — a DIFFERENT shielding convention (the value is
hidden in the commitment, never moved on the transparent ledger). These two are NOT the same per-cell
transition: they agree only at `value = 0`. We surface this as `runtime_debit_vs_univA_neutral_divergence`
rather than pretending the descriptor unifies with `NoteCreateASpec`. The commitment-set insert (§11) and
its no-double-check leg are universe-A properties unaffected by which balance convention is canonical. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Circuit.Spec.NoteCommitment
  (NoteCreateASpec execNoteCreateA_iff_spec noteCreateA_bal_neutral)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). The other EffectVM limbs have no universe-A analogue on the ledger entry, so they are
`0` (frozen). -/
def cellProjNote (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`univA_note_is_balance_neutral` — the universe-A side of the divergence.** A committed
`NoteCreateASpec` FREEZES the per-asset ledger `bal` (`bal' = bal`); the projected entry's `balLo` is
unchanged. So universe-A's noteCreate moves NO transparent value — the opposite of the runtime debit. -/
theorem univA_note_is_balance_neutral (st st' : RecChainedState) (cm : Nat) (actor c : CellId)
    (asset : AssetId) (hspec : NoteCreateASpec st cm actor st') :
    (cellProjNote st'.kernel.bal c asset).balLo = (cellProjNote st.kernel.bal c asset).balLo := by
  show st'.kernel.bal c asset = st.kernel.bal c asset
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-- **`runtime_debit_vs_univA_neutral_divergence` — THE DEEPER DIVERGENCE, named precisely.** A
descriptor-satisfying noteCreate row (the RUNTIME image) DEBITS the cell's `balLo` by `value`
(`post.balLo = pre.balLo − value`, from `CellNoteSpec`), whereas the committed universe-A spec FREEZES
the projected entry's `balLo`. For these to AGREE on the post-balance we would need
`pre.balLo − value = pre.balLo`, i.e. `value = 0`. So the runtime debit and the universe-A balance-neutral
convention are reconcilable ONLY for a zero-value note — a genuine SEMANTIC modeling gap (a shielding
convention difference), NOT a column index. Reported, not forced. -/
theorem runtime_debit_vs_univA_neutral_divergence
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (st st' : RecChainedState) (cm : Nat) (actor c : CellId) (asset : AssetId)
    (post : CellState) (value : ℤ)
    (henc : RowEncodesNote env (cellProjNote st.kernel.bal c asset) value post)
    (hsat : satisfiedVm hash noteCreateVmDescriptor env true true)
    (hspec : NoteCreateASpec st cm actor st')
    (hagree : post.balLo = (cellProjNote st'.kernel.bal c asset).balLo) :
    value = 0 := by
  obtain ⟨hcirc, _⟩ :=
    noteCreateDescriptor_full_sound hash env hrow (cellProjNote st.kernel.bal c asset) post value henc hsat
  have hdebit : post.balLo = (cellProjNote st.kernel.bal c asset).balLo - value := hcirc.1
  have hneutral := univA_note_is_balance_neutral st st' cm actor c asset hspec
  -- post.balLo = pre.balLo - value  AND  post.balLo = pre'.balLo = pre.balLo  ⟹  value = 0
  rw [hagree, hneutral] at hdebit
  linarith

/-! ## §11 — THE COMMITMENT-SET INSERT leg the per-row circuit does NOT enforce (honest, LOAD-BEARING).

`NoteCreateASpec` PREPENDS `cm` onto `st.kernel.commitments` — the ACTUAL effect. This is a SET-INSERT
into the commitment accumulator, and it is the LOAD-BEARING content of the effect (the per-cell FREEZE
above is "nothing happened to any cell"). NEITHER the insert NOR the published `cm` is a per-row gate
or hash-site of `noteCreateVmDescriptor`: there is no commitment-root column, the GROUP-4 hash-sites
absorb none of `commitments`. We state the leg EXACTLY so the gap is reported, not papered. -/

/-- **`note_insert_is_out_of_row` — the honest finding (LOAD-BEARING leg out-of-IR).** A committed
noteCreate's `commitments` store is `cm :: st.commitments` (`NoteCreateASpec`'s 2nd conjunct). This
set-insert — the ACTUAL effect — is a universe-A property carried by the `commitmentsComponent` list
digest, NOT by any per-row gate or hash-site of `noteCreateVmDescriptor`, whose hash-sites absorb only
the 13 frozen balance/nonce/field/cap state-block columns, none of `commitments`. So the runnable
descriptor does NOT bind the commitment update or the published `cm` into `state_commit`: it is the
§IR-extension flag, surfaced as a theorem. -/
theorem note_insert_is_out_of_row (st st' : RecChainedState) (cm : Nat) (actor : CellId)
    (hspec : NoteCreateASpec st cm actor st') :
    st'.kernel.commitments = cm :: st.kernel.commitments :=
  hspec.2.1

/-- **`note_append_only_is_out_of_row` — the no-double-check / freshness leg, honestly out-of-row.**
`noteCreate` is APPEND-ONLY with NO guard: every prior commitment survives. This grow-only / membership
property is over the WHOLE `commitments` SET, NOT a per-row arithmetic fact — enforced ONLY at
universe-A's accumulator / the turn layer, NEVER by the per-row circuit. We extract it from the spec to
name it precisely: any `x` already committed remains committed in the post-state. -/
theorem note_append_only_is_out_of_row (st st' : RecChainedState) (cm : Nat) (actor : CellId)
    (hspec : NoteCreateASpec st cm actor st') (x : Nat) (hx : x ∈ st.kernel.commitments) :
    x ∈ st'.kernel.commitments := by
  rw [note_insert_is_out_of_row st st' cm actor hspec]
  exact List.mem_cons_of_mem _ hx

/-! ## §12 — NON-VACUITY: a concrete noteCreate row realizes the debit/tick intent; a wrong one rejected. -/

/-- A concrete noteCreate row: `bal_lo 100 → 70` (debit `value = 30` from `param1`), nonce 5 → 6 (TICK),
frame fixed at 0. -/
def goodNoteRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_NOTE_CREATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 70
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.NOTE_VALUE_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `goodNoteRow` is a genuine noteCreate row (`s_note_create = 1`, `s_noop = 0`). -/
theorem goodNoteRow_isRow : IsNoteCreateRow goodNoteRow := by
  unfold IsNoteCreateRow goodNoteRow
  refine ⟨by norm_num [SEL_NOTE_CREATE], ?_⟩
  norm_num [sel.NOOP, SEL_NOTE_CREATE, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, param.NOTE_VALUE_LO]

/-- **NON-VACUITY (witness TRUE).** `goodNoteRow` REALIZES the noteCreate debit/tick intent:
`bal_lo 100 → 70 = 100 − 30`, nonce `5 → 6`, frame fixed. -/
theorem goodNoteRow_realizes_intent : NoteCreateRowIntent goodNoteRow := by
  unfold NoteCreateRowIntent goodNoteRow
  simp only [sbCol, saCol, prmCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.NOTE_VALUE_LO]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 5) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 5) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED noteCreate row: `goodNoteRow` with the post-`bal_lo` set to `999` (NOT the debit `70`). -/
def badNoteRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodNoteRow.loc v
  nxt := goodNoteRow.nxt
  pub := goodNoteRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badNoteRow`'s post-`bal_lo` is NOT the debit
`70`, so the `gBalLoDebit` gate REJECTS it — a concrete UNSAT (the debit has teeth). -/
theorem badNoteRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badNoteRow false false := by
  apply noteCreateVm_rejects_balance_mint
  simp only [badNoteRow, goodNoteRow, sbCol, saCol, prmCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.NOTE_VALUE_LO]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard noteCreateVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard noteCreateVmDescriptor.hashSites.length == 4
#guard noteCreateVmDescriptor.traceWidth == 186

#assert_axioms noteCreateVm_faithful
#assert_axioms noteCreateVm_rejects_wrong_output
#assert_axioms noteCreateVm_rejects_balance_mint
#assert_axioms intent_to_cellNoteSpec
#assert_axioms noteCreateDescriptor_full_sound
#assert_axioms noteCreateDescriptor_commit_binds_state
#assert_axioms univA_note_is_balance_neutral
#assert_axioms runtime_debit_vs_univA_neutral_divergence
#assert_axioms note_insert_is_out_of_row
#assert_axioms note_append_only_is_out_of_row
#assert_axioms goodNoteRow_isRow
#assert_axioms goodNoteRow_realizes_intent
#assert_axioms badNoteRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
