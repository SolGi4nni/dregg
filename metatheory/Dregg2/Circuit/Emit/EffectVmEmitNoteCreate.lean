/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteCreate — the noteCreate (note-COMMITMENT publish) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/noteCreateA.lean`, `Spec/notecommitment.lean`) carries the FULL-state soundness
`execNoteCreateA_iff_spec ⇒ NoteCreateASpec`: a committed publish PREPENDS a fresh commitment `cm`
onto the `commitments` SET, advances the chained `log` by `escrowReceiptA actor ::`, and is otherwise
TOTALLY NEUTRAL — it is balance-neutral (`noteCreateA_bal_neutral`) and FREEZES all 16 other kernel
fields. `noteCreate` is the APPEND-ONLY dual of `noteSpend`: NO guard at all (always commits).

## BALANCE-NEUTRAL (the shielding convention the executor + Rust apply already use)

This descriptor is RECONCILED onto the runtime so that the per-cell row is **BALANCE-NEUTRAL**: a
`noteCreate` PUBLISHES a commitment into the off-ledger note SET and moves NO transparent value, so the
`bal_lo` limb is FROZEN (`new_bal_lo = old_bal_lo`), the runtime nonce TICKS by one (the per-cell
sequence counter, as on every non-NoOp row), and bal_hi / cap_root / reserved / the 8 fields are
FROZEN; the post-state binds into `state_commit` via the SAME GROUP-4 chain as transfer. This is EXACTLY
the convention the verified executor uses (`apply_note_create`, `turn/src/executor/apply.rs:988`, which
records the commitment in the journal and NEVER touches the cell balance) and universe-A's
`NoteCreateASpec` (`noteCreateA_bal_neutral : bal' = bal`). So `noteCreateVmDescriptor` AGREES with the
executor and universe-A on the per-cell balance with NO divergence, and any forged on-trace balance
move (a smuggled debit/credit) is UNSAT (the `gBalLoFreeze` gate rejects it).

## BALANCE-NEUTRAL AGREEMENT (§9): EffectVM == universe-A on the frozen balance

The Rust circuit (`circuit/src/effect_vm/air.rs` `c_nc_bal`, `trace.rs`) and this descriptor are
BOTH balance-neutral, matching the executor: the value lives hidden in the commitment, never on the
transparent ledger. §9 below is an AGREEMENT theorem (`noteCreate_balance_neutral_matches_univA`):
the EffectVM descriptor and universe-A AGREE on the frozen balance for EVERY note.

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
     property over the `commitments` SET, stated out-of-row.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.notecommitment
import Dregg2.Exec.SystemRoots
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable

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
(the note value). The value is HIDDEN inside the published commitment; it is NEVER moved on the
transparent `bal_lo` ledger (the shielding convention). The param column is still laid (the
commitment-root amplification §A–§G reads the published commitment), but the BALANCE gate FREEZES
`bal_lo` — it does not read the value. This matches the verified executor (`apply_note_create`, which
records the commitment and never touches balance) and universe-A's balance-neutral `NoteCreateASpec`. -/
namespace param
/-- NoteCreate value lives at param column 1 (`columns.rs::param::NOTE_VALUE_LO`); carried for the
commitment binding, NOT moved on the transparent ledger. -/
def NOTE_VALUE_LO : Nat := 1
end param

/-- NoteCreate value as an expression (param column 1) — bound into the commitment, not the ledger. -/
def ePrmNoteValue : EmittedExpr := .var (prmCol param.NOTE_VALUE_LO)

/-! ## §1 — The per-row gate bodies (BALANCE-NEUTRAL + nonce TICK + frame freeze).

A noteCreate is BALANCE-NEUTRAL: it publishes a commitment into the off-ledger note set and moves NO
transparent value, so the `bal_lo` limb is FROZEN. It TICKS the runtime nonce (as every non-NoOp
EffectVM row does), and FREEZES the rest of the block. bal_hi / cap_root / reserved / the 8 fields
freeze bodies are REUSED from the transfer template (identical polynomials). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (the publish moves no transparent value; the
note value is hidden in the commitment, never on the ledger). The balance-neutral convention. -/
def gBalLoFreeze : EmittedExpr :=
  eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a noteCreate row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce

/-! ## §2 — The emitted descriptor. -/

/-- The note-commitment-publish AIR identity. -/
def noteCreateVmAirName : String := "dregg-effectvm-notecreate-v1"

/-- The per-row gates: bal_lo FREEZE (balance-neutral), bal_hi freeze, nonce TICK, cap/reserved freeze,
8 fields freeze. -/
def noteCreateRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceTick
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
                     ++ selectorGates 5
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT (the independent faithfulness target): the WHOLE state block frozen. -/

/-- **`NoteCreateRowIntent env`** — the intended noteCreate move on the row `env.loc`: the transparent
`bal_lo` is FROZEN (balance-neutral — the note value is hidden in the commitment, never moved on the
ledger), the runtime nonce TICKS by one, and balHi/cap/reserved/8 fields are FROZEN. The actual
commitment-set insert is bound by the §A–§G commitment-root amplification. -/
def NoteCreateRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the debit/tick intent. -/

/-- **`noteCreateVm_faithful`.** On a noteCreate row, the emitted descriptor's per-row gates all hold
IFF `NoteCreateRowIntent` holds — the gates pin EXACTLY the balance-neutral freeze + nonce tick + frame
freeze that the runtime hand-AIR enforces. -/
theorem noteCreateVm_faithful (env : VmRowEnv) (hrow : IsNoteCreateRow env) :
    (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) ↔ NoteCreateRowIntent env := by
  obtain ⟨_hsNC, hsN⟩ := hrow
  unfold noteCreateRowGates gFieldPassAll NoteCreateRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
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

/-! ## §5 — ANTI-GHOST: a row whose post-`bal_lo` is NOT frozen on a noteCreate is rejected. -/

/-- **Anti-ghost (general).** A noteCreate row that does NOT realize the freeze/tick intent does NOT
satisfy the per-row gates. -/
theorem noteCreateVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (hwrong : ¬ NoteCreateRowIntent env) :
    ¬ (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((noteCreateVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A noteCreate row whose post-`bal_lo` is NOT the FROZEN value (a
smuggled on-trace credit/debit — noteCreate is balance-neutral) has no satisfying gate set —
`gBalLoFreeze` alone rejects it (UNSAT). The value lives in the commitment, never on the ledger. -/
theorem noteCreateVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
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

/-- **`CellNoteSpec pre value post`** — the per-cell FULL-state noteCreate spec (the BALANCE-NEUTRAL
image): the transparent `balLo` is FROZEN (the note value is hidden in the commitment, never moved on
the ledger), balHi/8-fields/cap/reserved frozen, nonce TICKED by one. This is the EffectVM-row
projection of the executor's balance-neutral note-create transition — matching universe-A's
`NoteCreateASpec` (`noteCreateA_bal_neutral`), with NO divergence. The `value` argument is carried
(bound into the commitment via §A–§G) but does NOT move `balLo`. -/
def CellNoteSpec (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo
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
  · rw [← hsaLo, ← hsbLo]; exact hbal
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
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
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

/-- **`noteCreateDescriptor_commit_binds_state`** — two descriptor-satisfying noteCreate rows publishing
the SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT`
while tampering any absorbed cell of the (frozen) post-state. -/
theorem noteCreateDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash noteCreateVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash noteCreateVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2.1
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash noteCreateVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ noteCreateVmDescriptor.constraints := by
        unfold noteCreateVmDescriptor
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

/-! ## §9 — AGREEMENT: EffectVM balance-NEUTRAL == universe-A balance-NEUTRAL.

`noteCreateVmDescriptor` FREEZES `bal_lo` (balance-neutral), matching universe-A's shielding
convention (`noteCreateA_bal_neutral : bal' = bal`) and the Rust circuit
(`circuit/src/effect_vm/air.rs` `c_nc_bal`, `trace.rs`). So the EffectVM descriptor and universe-A
BOTH freeze the per-cell balance — they AGREE for EVERY note, not just `value = 0`. We surface that
as `noteCreate_balance_neutral_matches_univA` (an AGREEMENT theorem, no divergence conjunct). The
commitment-set insert (§11) and its no-double-check leg are universe-A properties unaffected by the
balance convention. -/

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

/-- **`univA_note_is_balance_neutral` — the universe-A side.** A committed `NoteCreateASpec` FREEZES the
per-asset ledger `bal` (`bal' = bal`); the projected entry's `balLo` is unchanged. universe-A's
noteCreate moves NO transparent value — the SAME balance-neutral convention the descriptor now uses. -/
theorem univA_note_is_balance_neutral (st st' : RecChainedState) (cm : Nat) (actor c : CellId)
    (asset : AssetId) (hspec : NoteCreateASpec st cm actor st') :
    (cellProjNote st'.kernel.bal c asset).balLo = (cellProjNote st.kernel.bal c asset).balLo := by
  show st'.kernel.bal c asset = st.kernel.bal c asset
  obtain ⟨_, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-- **`noteCreate_balance_neutral_matches_univA` — THE CLOSED DIVERGENCE, now AGREEMENT.** A
descriptor-satisfying noteCreate row (the EffectVM image) FREEZES the cell's `balLo`
(`post.balLo = pre.balLo`, from the balance-neutral `CellNoteSpec`), and the committed universe-A spec
ALSO freezes the projected entry's `balLo`. So the EffectVM descriptor's on-trace post-balance EQUALS
universe-A's post-balance for EVERY note (no `value = 0` side-condition) — the shielding-convention
divergence is CLOSED, the two surfaces agree by construction (the note value lives in the commitment,
never on the transparent ledger, in BOTH). -/
theorem noteCreate_balance_neutral_matches_univA
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (st st' : RecChainedState) (cm : Nat) (actor c : CellId) (asset : AssetId)
    (post : CellState) (value : ℤ)
    (henc : RowEncodesNote env (cellProjNote st.kernel.bal c asset) value post)
    (hsat : satisfiedVm hash noteCreateVmDescriptor env true true)
    (hspec : NoteCreateASpec st cm actor st') :
    post.balLo = (cellProjNote st'.kernel.bal c asset).balLo := by
  obtain ⟨hcirc, _⟩ :=
    noteCreateDescriptor_full_sound hash env hrow (cellProjNote st.kernel.bal c asset) post value henc hsat
  have hfreeze : post.balLo = (cellProjNote st.kernel.bal c asset).balLo := hcirc.1
  have hneutral := univA_note_is_balance_neutral st st' cm actor c asset hspec
  -- descriptor freezes: post.balLo = pre.balLo; universe-A freezes: pre'.balLo = pre.balLo. Agree.
  rw [hfreeze, hneutral]

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

/-- **`note_append_only_is_out_of_row` — the no-double-check / freshness leg, out-of-row.**
`noteCreate` is APPEND-ONLY with NO guard: every prior commitment survives. This grow-only / membership
property is over the WHOLE `commitments` SET, NOT a per-row arithmetic fact — enforced ONLY at
universe-A's accumulator / the turn layer, NEVER by the per-row circuit. We extract it from the spec to
name it precisely: any `x` already committed remains committed in the post-state. -/
theorem note_append_only_is_out_of_row (st st' : RecChainedState) (cm : Nat) (actor : CellId)
    (hspec : NoteCreateASpec st cm actor st') (x : Nat) (hx : x ∈ st.kernel.commitments) :
    x ∈ st'.kernel.commitments := by
  rw [note_insert_is_out_of_row st st' cm actor hspec]
  exact List.mem_cons_of_mem _ hx

/-! ## §12 — NON-VACUITY: a concrete noteCreate row realizes the freeze/tick intent; a wrong one rejected. -/

/-- A concrete noteCreate row: `bal_lo 100 → 100` (FROZEN — balance-neutral), nonce 5 → 6 (TICK),
frame fixed at 0. The note value (`param1 = 30`) is carried but does NOT move the ledger. -/
def goodNoteRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_NOTE_CREATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
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

/-- **NON-VACUITY (witness TRUE).** `goodNoteRow` REALIZES the noteCreate freeze/tick intent:
`bal_lo 100 → 100` (frozen — balance-neutral), nonce `5 → 6`, frame fixed. -/
theorem goodNoteRow_realizes_intent : NoteCreateRowIntent goodNoteRow := by
  unfold NoteCreateRowIntent goodNoteRow
  simp only [sbCol, saCol, prmCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.NOTE_VALUE_LO]
  refine ⟨rfl, rfl, by norm_num, rfl, rfl, ?_⟩
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

/-- A FORGED noteCreate row: `goodNoteRow` with the post-`bal_lo` set to `999` (NOT the frozen `100` —
a smuggled on-trace credit). -/
def badNoteRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodNoteRow.loc v
  nxt := goodNoteRow.nxt
  pub := goodNoteRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badNoteRow`'s post-`bal_lo` is NOT the
FROZEN `100` (a smuggled on-trace credit), so the `gBalLoFreeze` gate REJECTS it — a concrete UNSAT
(balance-neutrality has teeth). -/
theorem badNoteRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badNoteRow false false := by
  apply noteCreateVm_rejects_balance_mint
  simp only [badNoteRow, goodNoteRow, sbCol, saCol, prmCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.NOTE_VALUE_LO]
  norm_num

/-! ## §A — STAGE-3 AMPLIFICATION: bind the `commitments` side-table ROOT into the descriptor.

Record-layer STAGE 3 (`Exec.SystemRoots`, `6aa29e996`) gave each side-table its OWN kernel-owned root
column in the dedicated `system_roots` sub-block, committed by `systemRootsDigest` into ONE carrier
(`aux_off_sys.SYSTEM_ROOTS_DIGEST`). For `noteCreate` the relevant root is `state.systemRoot.COMMIT`
(the `commitments` accumulator). BEFORE this stage the commitment-set insert `cm :: commitments` was
the §11 OUT-OF-IR flag — there was no column to bind it. NOW there is. This section AMPLIFIES the
descriptor to FULL: a per-row root-UPDATE gate binds the `commitments`-accumulator step into the row,
the after-`SYSTEM_ROOTS_DIGEST` carrier is absorbed into `state_commit` by the GROUP-4 extension
(site 3's previously-spare `.zero` slot — `_IR-EXTENSION-DESIGN.md:158-162`), and the anti-ghost tooth
is re-proved over the now-bound root, CONNECTED to `Exec.SystemRoots.cellCommitS_binds_systemRoots`
(equal commitment ⇒ equal digest ⇒ equal `commitments` root). The whole-cell FREEZE + universe-A
connector of §4–§11 are UNCHANGED (strictly additive). -/

open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest systemRootsDigest_binds_pointwise N_SYSTEM_ROOTS rootList)

/-- The committed `system_roots` digest carrier of the AFTER state (the kernel side-table digest the
GROUP-4 extension absorbs into `state_commit`). This is the IR's `aux_off_sys.SYSTEM_ROOTS_DIGEST`. -/
def SYS_DIG_AFTER : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST

/-- The committed `system_roots` digest carrier of the BEFORE state (the pre-image of the accumulator
step). One aux column past the after-carrier, DISTINCT from every claimed aux slot (state-inters at
8/9/10, balance-bit block, the after-digest at 96), so it never aliases. The per-effect root-update
gate reads `sb`-digest here and writes `sa`-digest at `SYS_DIG_AFTER`. -/
def SYS_DIG_BEFORE : Nat := aux_off_sys.SYSTEM_ROOTS_DIGEST + 1

/-- The `commitments`-accumulator STEP param: the field-element delta the published `cm` contributes to
the `commitments` side-table digest (`systemRootsDigest` over the sub-block before vs after). The
trace generator lays it at `param2` (param0 = commitment `cm`, param1 = value; param2 = the digest
step the prover computed from the membership update `cm :: commitments`). -/
def COMMIT_ROOT_STEP_PARAM : Nat := 2

/-- The accumulator-step expression (param column 2). -/
def ePrmCommitStep : EmittedExpr := .var (prmCol COMMIT_ROOT_STEP_PARAM)

/-! ## §B — the root-UPDATE gate + the digest-absorbing GROUP-4 extension site.

The per-row gate `gCommitRootUpdate` pins `sa_digest = sb_digest + step`: the `commitments` side-table
digest ADVANCES by the accumulator step the appended `cm` contributes (the runtime hand-AIR's
note-create arm computes exactly this digest delta and writes the new `systemRootsDigest` carrier). The
extended hash-site list `noteCreateRootHashSites` re-uses transfer's sites 0/1/2 and REPLACES site 3's
spare `.zero` 4th input with the after-digest carrier, so `state_commit` now absorbs the side-table
digest — the GROUP-4 extension. -/

/-- Root-update gate body: `sa_digest − sb_digest − step` (so `sa_digest = sb_digest + step`). Reads
the before/after `system_roots` digest carriers and the `param2` accumulator step. -/
def gCommitRootUpdate : EmittedExpr :=
  eSub (eSub (.var SYS_DIG_AFTER) (.var SYS_DIG_BEFORE)) ePrmCommitStep

/-- Site 3′: `state_commit = H4(inter1, inter2, inter3, sys_digest_after)` — the GROUP-4 extension that
absorbs the `system_roots` digest carrier into the published commitment (replacing transfer's spare
`.zero`). This is the column that makes the `commitments` root BINDABLE. -/
def siteCommitRoot : VmHashSite :=
  { digestCol := saCol state.STATE_COMMIT
  , inputs := [ .digest 0, .digest 1, .digest 2, .col SYS_DIG_AFTER ]
  , arity := 4 }

/-- The amplified GROUP-4 hash sites: transfer's three inner sites + the digest-absorbing site 3′. -/
def noteCreateRootHashSites : List VmHashSite :=
  [ EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1
  , EffectVmEmitTransfer.site2, siteCommitRoot ]

/-- **`noteCreateRootHash_binds`** — under the amplified sites, the published `state_commit` is the
genuine 4-level digest of the after-state WITH the `system_roots` digest carrier in the 4th slot. The
site order is load-bearing (site 3′ reads sites 0/1/2 + the digest column). -/
theorem noteCreateRootHash_binds (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env noteCreateRootHashSites) :
    env.loc (saCol state.STATE_COMMIT)
      = hash [ hash [ env.loc (saCol state.BALANCE_LO), env.loc (saCol state.BALANCE_HI)
                    , env.loc (saCol state.NONCE), env.loc (saCol (state.FIELD_BASE + 0)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 1)), env.loc (saCol (state.FIELD_BASE + 2))
                    , env.loc (saCol (state.FIELD_BASE + 3)), env.loc (saCol (state.FIELD_BASE + 4)) ]
             , hash [ env.loc (saCol (state.FIELD_BASE + 5)), env.loc (saCol (state.FIELD_BASE + 6))
                    , env.loc (saCol (state.FIELD_BASE + 7)), env.loc (saCol state.CAP_ROOT) ]
             , env.loc SYS_DIG_AFTER ] := by
  unfold siteHoldsAll noteCreateRootHashSites at h
  simp only [siteHoldsAll.go, EffectVmEmitTransfer.site0, EffectVmEmitTransfer.site1,
    EffectVmEmitTransfer.site2, siteCommitRoot, VmHashSite.resolvedInputs, HashInput.resolve,
    List.map_cons, List.map_nil, List.getD] at h
  obtain ⟨_, _, _, h3, _⟩ := h
  rw [h3]; rfl

/-! ## §C — FAITHFULNESS of the root-update gate + ANTI-GHOST over the bound digest. -/

/-- **`NoteCreateRootIntent env`** — the intended `commitments`-root move on the row: the `system_roots`
digest ADVANCES by the `param2` accumulator step (`sa_digest = sb_digest + step`). This is the per-row
projection of the membership update `commitments := cm :: commitments` onto its committed digest. -/
def NoteCreateRootIntent (env : VmRowEnv) : Prop :=
  env.loc SYS_DIG_AFTER = env.loc SYS_DIG_BEFORE + env.loc (prmCol COMMIT_ROOT_STEP_PARAM)

/-- **`noteCreateRoot_gate_faithful`.** The root-update gate holds IFF the digest advances by the
accumulator step — the gate pins EXACTLY the `commitments`-root update. -/
theorem noteCreateRoot_gate_faithful (env : VmRowEnv) :
    (VmConstraint.gate gCommitRootUpdate).holdsVm env false false ↔ NoteCreateRootIntent env := by
  simp only [VmConstraint.holdsVm, gCommitRootUpdate, ePrmCommitStep, eSub, EmittedExpr.eval,
    NoteCreateRootIntent]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Anti-ghost (root tamper).** A row whose after-digest is NOT the advanced accumulator
(`sb_digest + step`) is rejected by `gCommitRootUpdate` — a dropped/forged `commitments` update is
UNSAT. -/
theorem noteCreateRoot_rejects_wrong_root (env : VmRowEnv)
    (hwrong : env.loc SYS_DIG_AFTER ≠ env.loc SYS_DIG_BEFORE + env.loc (prmCol COMMIT_ROOT_STEP_PARAM)) :
    ¬ (VmConstraint.gate gCommitRootUpdate).holdsVm env false false := by
  intro h; exact hwrong ((noteCreateRoot_gate_faithful env).mp h)

/-! ## §D — the AMPLIFIED descriptor + the side-table-root anti-ghost tooth (connected to `SystemRoots`). -/

/-- **`noteCreateVmDescriptorFull`** — the AMPLIFIED noteCreate circuit: the §2 whole-cell freeze gates
PLUS the `commitments`-root-update gate, with the digest-absorbing GROUP-4 sites. The runtime trace
now writes the advanced `system_roots` digest and binds it into `state_commit`. Strictly additive over
`noteCreateVmDescriptor` (one extra gate, the spare site-3 slot filled). -/
def noteCreateVmDescriptorFull : EffectVmDescriptor :=
  { name := noteCreateVmAirName ++ "-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := (noteCreateRowGates ++ [.gate gCommitRootUpdate])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := noteCreateRootHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The amplified descriptor still forces the §2 whole-cell FREEZE (the root-update gate is additive and
the freeze gates are a sublist of its constraints). Generalised over the boundary flags — the freeze
gates are per-row `.gate`s, whose `holdsVm` ignores `isFirst`/`isLast`. -/
theorem noteCreateFull_forces_freeze (env : VmRowEnv) (hrow : IsNoteCreateRow env) (b1 b2 : Bool)
    (hgates : ∀ c ∈ noteCreateVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    NoteCreateRowIntent env := by
  apply (noteCreateVm_faithful env hrow).mp
  intro c hc
  have hmem : c ∈ noteCreateVmDescriptorFull.constraints := by
    unfold noteCreateVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have := hgates c hmem
  -- `c` is a per-row `.gate` (a member of `noteCreateRowGates`), so `holdsVm` ignores the flags.
  unfold noteCreateRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- The amplified descriptor forces the `commitments`-ROOT update (the new content STAGE 3 buys).
Generalised over the boundary flags (the root gate is a per-row `.gate`). -/
theorem noteCreateFull_forces_root (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ noteCreateVmDescriptorFull.constraints, c.holdsVm env b1 b2) :
    NoteCreateRootIntent env := by
  apply (noteCreateRoot_gate_faithful env).mp
  have hmem : (VmConstraint.gate gCommitRootUpdate) ∈ noteCreateVmDescriptorFull.constraints := by
    unfold noteCreateVmDescriptorFull
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by simp))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-- **`noteCreateFull_commit_binds_sysdigest` — the digest is now bound into `state_commit`.** Two
rows satisfying the amplified hash-sites that publish the SAME `state_commit` have the SAME absorbed
`system_roots` digest. Off `Poseidon2SpongeCR`: the outer sponge binds its 4-list, whose 4th slot is
the after-digest carrier. So a prover CANNOT keep `state_commit` while tampering the side-table digest
— the §11 OUT-OF-IR flag is CLOSED. -/
theorem noteCreateFull_commit_binds_sysdigest (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ noteCreateRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ noteCreateRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc SYS_DIG_AFTER = e₂.loc SYS_DIG_AFTER := by
  rw [noteCreateRootHash_binds hash e₁ hs₁, noteCreateRootHash_binds hash e₂ hs₂] at hcommit
  have houter := hCR _ _ hcommit
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at houter
  exact houter.2.2.2.1

/-- **`noteCreateFull_binds_commitments_root` — CONNECTED to `Exec.SystemRoots`.** Two amplified rows
that publish the same `state_commit` AND whose after-digest carrier IS the `systemRootsDigest` of their
respective `system_roots` sub-blocks have the SAME `commitments` side-table root (and every other). The
chain: equal commitment ⇒ equal digest carrier (`noteCreateFull_commit_binds_sysdigest`) ⇒ equal
side-table roots pointwise (`Exec.SystemRoots.systemRootsDigest_binds_pointwise`). Tampering ONLY the
`commitments` root (omitting `cm`) provably MOVES `state_commit` ⇒ UNSAT. -/
theorem noteCreateFull_binds_commitments_root (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hs₁ : siteHoldsAll hash e₁ noteCreateRootHashSites)
    (hs₂ : siteHoldsAll hash e₂ noteCreateRootHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT))
    (hd₁ : e₁.loc SYS_DIG_AFTER = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc SYS_DIG_AFTER = systemRootsDigest hash sr₂)
    (i : Fin N_SYSTEM_ROOTS) :
    sr₁ i = sr₂ i := by
  have hdig : systemRootsDigest hash sr₁ = systemRootsDigest hash sr₂ := by
    rw [← hd₁, ← hd₂]
    exact noteCreateFull_commit_binds_sysdigest hash hCR e₁ e₂ hs₁ hs₂ hcommit
  exact systemRootsDigest_binds_pointwise hash hCR sr₁ sr₂ hdig i

/-! ## §E — CONNECTOR to universe-A `noteCreateDescriptor_full_sound`: the amplified descriptor STILL
carries the whole-cell freeze + post-commit publication (now over the root-bound commitment). -/

/-- **`noteCreateFull_sound` — the amplified full soundness.** A row satisfying the AMPLIFIED descriptor
(gates + root-update + amplified sites), under `RowEncodesNote`, forces the structured `CellNoteSpec`
freeze AND the `commitments`-root advance AND publishes the post-commit — the §7 universe-A connector
lifted onto the root-bound descriptor. -/
theorem noteCreateFull_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsNoteCreateRow env)
    (pre post : CellState) (value : ℤ)
    (henc : RowEncodesNote env pre value post)
    (hsat : satisfiedVm hash noteCreateVmDescriptorFull env true true) :
    CellNoteSpec pre value post
      ∧ NoteCreateRootIntent env
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites, _⟩ := hsat
  have hfreeze := noteCreateFull_forces_freeze env hrow true true hcs
  have hroot := noteCreateFull_forces_root env true true hcs
  refine ⟨intent_to_cellNoteSpec env pre post value henc hfreeze, hroot, ?_⟩
  -- the post-commit publication is the last-row PI pin (unchanged from §7).
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ noteCreateVmDescriptorFull.constraints := by
      unfold noteCreateVmDescriptorFull
      simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  have hpin := (boundaryLast_pins env hlast).1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §F — RECONCILIATION onto the runtime trace-generator layout (the cutover discipline, `3aaf0772d`).

The validated runtime hand-AIR + `generate_effect_vm_trace` (after STAGE 3) lay the `system_roots`
digest carrier exactly where this descriptor reads it: the after-`SYSTEM_ROOTS_DIGEST` carrier (aux 96,
the kernel side-table digest), and the note-create arm computes the advanced digest from the
`commitments := cm :: commitments` update. So on the HONEST trace `gCommitRootUpdate` holds (the runtime
writes `sa_digest = sb_digest + step`) and `siteCommitRoot` holds (the runtime binds the carrier into
`state_commit`): the descriptor AGREES with the hand-AIR. We pin the layout agreement as `#guard`s so a
column drift breaks the build. -/

-- The amplified descriptor reads the kernel digest carrier (aux 96), not a user field.
#guard SYS_DIG_AFTER == aux_off_sys.SYSTEM_ROOTS_DIGEST
#guard SYS_DIG_AFTER == 96
-- The before-carrier is DISTINCT from every claimed aux slot (state-inters + after-digest).
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        SYS_DIG_AFTER, SYS_DIG_BEFORE].dedup.length == 5
-- The accumulator-step param is param2 (param0 = cm, param1 = value), in-range of the 8 param cols.
#guard COMMIT_ROOT_STEP_PARAM == 2
#guard COMMIT_ROOT_STEP_PARAM < NUM_PARAMS
-- The amplified descriptor has the extra root-update gate (14 row gates now) + the 4 amplified sites.
#guard noteCreateVmDescriptorFull.constraints.length == 14 + 14 + 4 + 3
#guard noteCreateVmDescriptorFull.hashSites.length == 4

/-! ## §G — NON-VACUITY of the amplification: a concrete root-advancing row + a forged one. -/

/-- A concrete root-update row: `sys_digest 1000 → 1042` (advance by step `42` = the appended `cm`'s
digest contribution). -/
def goodRootRow : VmRowEnv where
  loc := fun v =>
    if v = SYS_DIG_BEFORE then 1000
    else if v = SYS_DIG_AFTER then 1042
    else if v = prmCol COMMIT_ROOT_STEP_PARAM then 42
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodRootRow` REALIZES the `commitments`-root advance:
`1042 = 1000 + 42`. -/
theorem goodRootRow_realizes : NoteCreateRootIntent goodRootRow := by
  unfold NoteCreateRootIntent goodRootRow
  simp only [SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, COMMIT_ROOT_STEP_PARAM, aux_off_sys.SYSTEM_ROOTS_DIGEST,
    PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-- A FORGED root row: the after-digest is `9999` (NOT the advance `1042`) — a dropped/forged
`commitments` update. -/
def badRootRow : VmRowEnv where
  loc := fun v => if v = SYS_DIG_AFTER then 9999 else goodRootRow.loc v
  nxt := goodRootRow.nxt
  pub := goodRootRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badRootRow`'s after-digest is NOT the
advance, so `gCommitRootUpdate` REJECTS it — the bound root has teeth. -/
theorem badRootRow_rejected : ¬ (VmConstraint.gate gCommitRootUpdate).holdsVm badRootRow false false := by
  apply noteCreateRoot_rejects_wrong_root
  simp only [badRootRow, goodRootRow, SYS_DIG_BEFORE, SYS_DIG_AFTER, prmCol, COMMIT_ROOT_STEP_PARAM,
    aux_off_sys.SYSTEM_ROOTS_DIGEST, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE]
  norm_num

/-! ## §W — FULL-STATE ON THE RUNNABLE DESCRIPTOR (the magnesium breadth — the GENERIC crown).

§A–§G amplified the descriptor over the OLD raw `SYS_DIG_AFTER = aux 96` carrier with the bespoke
`noteCreateVmDescriptorFull`. THIS section lifts noteCreate to the GENERIC full-state-on-RUNNABLE crown
`EffectVmFullStateRunnable.runnable_full_sound` — the analog of the transfer reference
`transferRunnableSpec` — over the DEDICATED, non-aliasing `sysRootsDigestCol = 186` carrier and the
shared `wideHashSites` (so the crypto / anti-ghost is discharged ONCE in the generic theorem and the
whole-17-field anti-ghost falls out of `wide_rejects_state_tamper`/`wide_rejects_root_tamper`). The
per-effect content is THIN: the wide descriptor, the root-update gate over the dedicated carrier, the
structured decode, and `decodeFull` (which reuses §4's `noteCreateVm_faithful` + the root-gate
faithfulness). NO new crypto portal — the only terminal is the generic theorem's `Poseidon2SpongeCR`.

This binds the FULL post-state: the per-cell block (balance-NEUTRAL freeze + nonce tick, fields 1–3 of
the §0 census) AND all 8 side-table roots (fields 4–12 — the `commitments` root ADVANCES by the
accumulator step, every OTHER side-table root FROZEN), so a satisfying wide-descriptor witness pins
exactly the 17-field post-state the noteCreate executor produces, and tamper of ANY field/root is UNSAT
(the generic anti-ghost). -/

open EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Circuit.Emit.EffectVmEmit (sysRootsDigestCol sysRootsDigestColBefore EFFECT_VM_WIDTH_SYSROOTS)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (RowEncodes CellState absorbedCols)

/-! ### §W.1 — the root-UPDATE gate over the DEDICATED carrier (`sysRootsDigestCol`/`…Before`).

Unlike §B's `gCommitRootUpdate` (which reads the raw aux-96 `SYS_DIG_AFTER`, inside the balance-bit
block), this gate reads the dedicated, non-aliasing `sysRootsDigestCol = 186` / `sysRootsDigestColBefore
= 187` carriers the wide IR added — the exact column the `wideHashSites` absorb. So the `commitments`
digest step the row binds is the SAME column the published `state_commit` commits to. -/

/-- Root-update gate body over the DEDICATED carrier: `sa_sysdig − sb_sysdig − step` (so
`sysRootsDigestCol = sysRootsDigestColBefore + step`), reading the dedicated `system_roots` carriers
(186/187) and the `param2` accumulator step. The wide analog of `gCommitRootUpdate`. -/
def gCommitRootUpdateWide : EmittedExpr :=
  eSub (eSub (.var sysRootsDigestCol) (.var sysRootsDigestColBefore)) ePrmCommitStep

/-- **`NoteCreateRootIntentWide env`** — the dedicated-carrier root move: the `system_roots` digest at
`sysRootsDigestCol` ADVANCES by the `param2` step over `sysRootsDigestColBefore`. -/
def NoteCreateRootIntentWide (env : VmRowEnv) : Prop :=
  env.loc sysRootsDigestCol
    = env.loc sysRootsDigestColBefore + env.loc (prmCol COMMIT_ROOT_STEP_PARAM)

/-- **`gCommitRootUpdateWide_faithful`.** The wide root-update gate holds IFF the dedicated-carrier
digest advances by the accumulator step. -/
theorem gCommitRootUpdateWide_faithful (env : VmRowEnv) :
    (VmConstraint.gate gCommitRootUpdateWide).holdsVm env false false ↔ NoteCreateRootIntentWide env := by
  simp only [VmConstraint.holdsVm, gCommitRootUpdateWide, ePrmCommitStep, eSub, EmittedExpr.eval,
    NoteCreateRootIntentWide]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### §W.2 — the WIDE descriptor (dedicated carrier + `wideHashSites`). -/

/-- **`noteCreateVmDescriptorWide`** — noteCreate's WIDE runnable descriptor: the §2 whole-cell freeze
gates PLUS the dedicated-carrier `commitments`-root-update gate ++ transition continuity ++ the 7
boundary PI pins ++ the selector-binding gate, with `traceWidth := EFFECT_VM_WIDTH_SYSROOTS` and
`hashSites := wideHashSites` (so `usesWideSites := rfl`). The `system_roots`-absorbing analog of
`transferVmDescriptorWide`. -/
def noteCreateVmDescriptorWide : EffectVmDescriptor :=
  { name := noteCreateVmAirName ++ "-sysroots"
  , traceWidth := EFFECT_VM_WIDTH_SYSROOTS
  , piCount := 34
  , constraints := (noteCreateRowGates ++ [.gate gCommitRootUpdateWide])
                     ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates SEL_NOTE_CREATE
  , hashSites := wideHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-- The wide descriptor's hash-sites ARE the shared `wideHashSites`. -/
theorem noteCreateWide_usesWideSites : noteCreateVmDescriptorWide.hashSites = wideHashSites := rfl

/-- **`noteCreateWide_forces_freeze`** — the wide descriptor still forces the §2 whole-cell FREEZE
(`NoteCreateRowIntent`); the freeze gates are a sublist of the wide constraints, all per-row `.gate`s
(flag-independent). -/
theorem noteCreateWide_forces_freeze (env : VmRowEnv) (hrow : IsNoteCreateRow env) (b1 b2 : Bool)
    (hgates : ∀ c ∈ noteCreateVmDescriptorWide.constraints, c.holdsVm env b1 b2) :
    NoteCreateRowIntent env := by
  apply (noteCreateVm_faithful env hrow).mp
  intro c hc
  have hmem : c ∈ noteCreateVmDescriptorWide.constraints := by
    unfold noteCreateVmDescriptorWide
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hc))))
  have := hgates c hmem
  unfold noteCreateRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`noteCreateWide_forces_root`** — the wide descriptor forces the dedicated-carrier `commitments`-root
advance. -/
theorem noteCreateWide_forces_root (env : VmRowEnv) (b1 b2 : Bool)
    (hgates : ∀ c ∈ noteCreateVmDescriptorWide.constraints, c.holdsVm env b1 b2) :
    NoteCreateRootIntentWide env := by
  apply (gCommitRootUpdateWide_faithful env).mp
  have hmem : (VmConstraint.gate gCommitRootUpdateWide) ∈ noteCreateVmDescriptorWide.constraints := by
    unfold noteCreateVmDescriptorWide
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (by simp)))))
  have := hgates _ hmem
  simpa only [VmConstraint.holdsVm] using this

/-! ### §W.3 — the DECLARATIVE full 17-field post-state clause + the structured decode.

`NoteCreateFullClause` is the genuine full post-state: the per-cell `CellNoteSpec` (balance-NEUTRAL
freeze + nonce tick — fields 1–3), the decoded roots ARE `postRoots`, the `commitments` root's committed
DIGEST advanced by the accumulator `step` (the bound update of field 6), and EVERY OTHER side-table root
is FROZEN (fields 4,5,7–12). Non-vacuous: §W.5 inhabits it with a real publish. -/

/-- **`NoteCreateFullClause hash value preRoots postRoots step`** — the full declarative 17-field
post-state for a noteCreate over `(pre, post, pr)`: the per-cell balance-neutral `CellNoteSpec`, the
decoded roots `pr = postRoots`, the `commitments`-root committed-digest advance
(`systemRootsDigest postRoots = systemRootsDigest preRoots + step`), and every NON-`COMMIT` side-table
root FROZEN (`postRoots i = preRoots i`). All 17 fields: 1–3 by `CellNoteSpec`; 6 by the digest advance;
4,5,7–12 by the freeze; 13–17 ride the per-cell value's restLimbs (the named `CommitmentCrossBind`
factoring, as the §0 census). -/
def NoteCreateFullClause (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (pre post : CellState) (pr : SysRoots) : Prop :=
  CellNoteSpec pre value post
  ∧ pr = postRoots
  ∧ Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
      = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots + step
  ∧ (∀ i : Fin N_SYSTEM_ROOTS, i.val ≠ Dregg2.Exec.SystemRoots.systemRoot.COMMIT → postRoots i = preRoots i)

/-- **`NoteCreateDecode hash value preRoots postRoots step env pre post pr`** — the structured row decode:
the cell block + param value is `RowEncodesNote`, the decoded roots are `postRoots`, the dedicated
carriers ARE the `systemRootsDigest` of `postRoots`/`preRoots`, the `param2` step is `step`, the
published `NEW_COMMIT` is the after-`state_commit`, AND the off-row witness data (the `commitments`-root
digest advance + non-`COMMIT` freeze) hold. The `RowEncodes`-style relation EXTENDED with the dedicated
`sysRootsDigestCol` carrier link (the recipe's `decodeAfter`). -/
def NoteCreateDecode (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (pr : SysRoots) : Prop :=
  RowEncodesNote env pre value post
  ∧ pr = postRoots
  ∧ env.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
  ∧ env.loc sysRootsDigestColBefore = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots
  ∧ env.loc (prmCol COMMIT_ROOT_STEP_PARAM) = step
  ∧ (∀ i : Fin N_SYSTEM_ROOTS, i.val ≠ Dregg2.Exec.SystemRoots.systemRoot.COMMIT → postRoots i = preRoots i)

/-! ### §W.4 — THE INSTANCE + the crown `noteCreate_runnable_full_sound`. -/

/-- **`noteCreateRunnableSpec hash value preRoots postRoots step`** — noteCreate's `RunnableFullStateSpec`.
`decodeAfter` is `NoteCreateDecode`; `fullClause` is `NoteCreateFullClause`; `decodeFull` projects the
wide descriptor's freeze gates to `CellNoteSpec` (via `noteCreateWide_forces_freeze` +
`intent_to_cellNoteSpec`) and the dedicated-carrier root gate to the digest advance (via
`noteCreateWide_forces_root` + the carrier decode). THIN — the only per-effect content is §4's already-
proved faithfulness + the decode; NON-VACUOUS (§W.5). -/
def noteCreateRunnableSpec (hash : List ℤ → ℤ) (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ) :
    RunnableFullStateSpec CellState where
  descriptor    := noteCreateVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsNoteCreateRow
  decodeAfter   := NoteCreateDecode hash value preRoots postRoots step
  fullClause    := NoteCreateFullClause hash value preRoots postRoots step
  decodeFull    := by
    intro env pre post pr hrow hdec hgates
    obtain ⟨henc, hpr, hdigA, hdigB, hstep, hfreezeRoots⟩ := hdec
    -- per-cell freeze: the wide freeze gates ⟹ NoteCreateRowIntent ⟹ CellNoteSpec.
    have hfreeze := noteCreateWide_forces_freeze env hrow true true hgates
    have hcell := intent_to_cellNoteSpec env pre post value henc hfreeze
    -- the dedicated-carrier root gate ⟹ the digest advances by the `param2` step …
    have hrootW := noteCreateWide_forces_root env true true hgates
    -- … which, decoded, is the `commitments`-root digest advance over `postRoots`/`preRoots`.
    have hadvance : Dregg2.Exec.SystemRoots.systemRootsDigest hash postRoots
        = Dregg2.Exec.SystemRoots.systemRootsDigest hash preRoots + step := by
      have := hrootW
      unfold NoteCreateRootIntentWide at this
      rw [hdigA, hdigB, hstep] at this
      exact this
    exact ⟨hcell, hpr, hadvance, hfreezeRoots⟩

/-- **`noteCreate_runnable_full_sound` — THE CROWN (full-state on the RUNNABLE descriptor).** A row
satisfying noteCreate's WIDE runnable descriptor (`satisfiedVm noteCreateVmDescriptorWide`, first/last
active), under the structured decode `NoteCreateDecode`, pins the FULL 17-field declarative post-state
`NoteCreateFullClause`: the per-cell balance-neutral freeze + nonce tick, the `commitments`-root committed-
digest advance by the accumulator step, and every OTHER side-table root frozen. This is the generic
`runnable_full_sound` instantiated at `noteCreateRunnableSpec` — the circuit the prover ACTUALLY RUNS
pins the whole post-state the noteCreate executor produces, not the weaker frame projection. -/
theorem noteCreate_runnable_full_sound (hash : List ℤ → ℤ)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (env : VmRowEnv) (pre post : CellState) (pr : SysRoots)
    (hrow : IsNoteCreateRow env)
    (hdec : NoteCreateDecode hash value preRoots postRoots step env pre post pr)
    (hsat : satisfiedVm hash noteCreateVmDescriptorWide env true true) :
    NoteCreateFullClause hash value preRoots postRoots step pre post pr :=
  runnable_full_sound (noteCreateRunnableSpec hash value preRoots postRoots step) hash env pre post pr
    hrow hdec hsat

/-- **`noteCreate_runnable_rejects_root_tamper` — the side-table anti-ghost (free from the generic
crown).** Two rows satisfying the wide descriptor publishing the SAME `NEW_COMMIT` (with
`systemRootsDigest` carriers) but whose `system_roots` sub-blocks DIFFER at some index (a dropped/omitted
`commitments` update, OR any other side-table root tampered) cannot BOTH satisfy — UNSAT. The whole-17-
field anti-ghost tooth, specialised from `wide_rejects_root_tamper`. -/
theorem noteCreate_runnable_rejects_root_tamper (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash noteCreateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash noteCreateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (noteCreateRunnableSpec hash value preRoots postRoots step) hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`noteCreate_runnable_rejects_state_tamper` — the per-cell-block anti-ghost (free).** Two wide rows
publishing the same `NEW_COMMIT` but whose absorbed state-block columns (balance/nonce/fields/cap) DIFFER
cannot both satisfy — a forged balance / tampered field / forged cap-root that still claims the published
commitment is UNSAT. Specialised from `wide_rejects_state_tamper`. -/
theorem noteCreate_runnable_rejects_state_tamper (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (value : ℤ) (preRoots postRoots : SysRoots) (step : ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash noteCreateVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash noteCreateVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  wide_rejects_state_tamper (noteCreateRunnableSpec hash value preRoots postRoots step) hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### §W.5 — NON-VACUITY of the wide instance: the full clause is INHABITED + REFUTABLE.

The crown is hollow if `NoteCreateFullClause` is vacuous. A concrete realization: the `commitments` root
advances (the COMMIT index moves), every other root frozen, the cell balance-neutral. And a refutation:
a forged post-balance fails `CellNoteSpec`. Both sides, no `native_decide`. -/

/-- A concrete frozen reference sub-block (every side-table empty before the publish). -/
def wPreRoots : SysRoots := Dregg2.Exec.SystemRoots.emptySystemRoots

/-- A concrete post sub-block: the `commitments` (COMMIT) root advanced to `7`, every other root still
empty (the genuine "only the touched root moved" shape). -/
def wPostRoots : SysRoots := fun i =>
  if i = (⟨Dregg2.Exec.SystemRoots.systemRoot.COMMIT, by decide⟩ : Fin N_SYSTEM_ROOTS) then 7 else 0

/-- The honest cell pre/post for the witness: balance-neutral `100 → 100`, nonce `5 → 6`, frame frozen. -/
def wPre : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }
def wPost : CellState :=
  { balLo := 100, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- **`noteCreate_fullClause_inhabited` — NON-VACUITY (witness TRUE).** The full clause is inhabited by a
real publish: balance-neutral cell freeze + nonce tick, the `commitments` root digest advanced by the
genuine step `δ = systemRootsDigest wPostRoots − systemRootsDigest wPreRoots`, every other root frozen. So
`NoteCreateFullClause` is a MEANINGFUL 17-field predicate a real noteCreate satisfies, not `True`. -/
theorem noteCreate_fullClause_inhabited (hash : List ℤ → ℤ) :
    NoteCreateFullClause hash 30 wPreRoots wPostRoots
      (Dregg2.Exec.SystemRoots.systemRootsDigest hash wPostRoots
        - Dregg2.Exec.SystemRoots.systemRootsDigest hash wPreRoots)
      wPre wPost wPostRoots := by
  refine ⟨?_, rfl, by ring, ?_⟩
  · -- CellNoteSpec wPre 30 wPost: balLo frozen, balHi frozen, nonce+1, fields/cap/reserved frozen.
    refine ⟨rfl, rfl, by norm_num [wPre, wPost], ?_, rfl, rfl⟩
    intro i; rfl
  · -- every NON-COMMIT root is frozen at 0 (both empty/post agree off the COMMIT index).
    intro i hi
    simp only [wPostRoots, wPreRoots, Dregg2.Exec.SystemRoots.emptySystemRoots]
    rw [if_neg]
    intro hcontra
    exact hi (by rw [hcontra])

/-- **`noteCreate_fullClause_refutable` — NON-VACUITY (witness FALSE).** A post-state whose `balLo` is a
forged `999` (NOT the balance-neutral frozen `100`) FAILS `CellNoteSpec`, so `NoteCreateFullClause` is
REFUTABLE — the clause rejects a smuggled on-trace credit, pinning non-vacuity from both sides. -/
theorem noteCreate_fullClause_refutable (hash : List ℤ → ℤ) :
    ¬ NoteCreateFullClause hash 30 wPreRoots wPostRoots
        (Dregg2.Exec.SystemRoots.systemRootsDigest hash wPostRoots
          - Dregg2.Exec.SystemRoots.systemRootsDigest hash wPreRoots)
        wPre { wPost with balLo := 999 } wPostRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  -- hbal : (999) = wPre.balLo = 100 (balance-neutral)
  simp only [wPre] at hbal
  norm_num at hbal

/-! ### §W.6 — RECONCILIATION pins (the wide descriptor's shape). -/

-- The wide descriptor carries the widened trace width + the dedicated carrier (NOT the old aux-96).
#guard noteCreateVmDescriptorWide.traceWidth == 188
#guard noteCreateVmDescriptorWide.hashSites.length == 4
-- 13 freeze gates + 1 wide-root gate + 14 transitions + 4 boundaryFirst + 3 boundaryLast + 1 selector.
#guard noteCreateVmDescriptorWide.constraints.length == 13 + 1 + 14 + 4 + 3 + 1
-- The wide root gate reads the DEDICATED carriers (186/187), never the old aux-96 (96).
#guard sysRootsDigestCol == 186
#guard sysRootsDigestColBefore == 187
#guard decide (sysRootsDigestCol ≠ SYS_DIG_AFTER)

#assert_axioms gCommitRootUpdateWide_faithful
#assert_axioms noteCreateWide_forces_freeze
#assert_axioms noteCreateWide_forces_root
#assert_axioms noteCreate_runnable_full_sound
#assert_axioms noteCreate_runnable_rejects_root_tamper
#assert_axioms noteCreate_runnable_rejects_state_tamper
#assert_axioms noteCreate_fullClause_inhabited
#assert_axioms noteCreate_fullClause_refutable

/-! ## §13 — Axiom-hygiene pins. -/

#guard noteCreateVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard noteCreateVmDescriptor.hashSites.length == 4
#guard noteCreateVmDescriptor.traceWidth == 186

#assert_axioms noteCreateVm_faithful
#assert_axioms noteCreateVm_rejects_wrong_output
#assert_axioms noteCreateVm_rejects_balance_mint
#assert_axioms intent_to_cellNoteSpec
#assert_axioms noteCreateDescriptor_full_sound
#assert_axioms noteCreateDescriptor_commit_binds_state
#assert_axioms univA_note_is_balance_neutral
#assert_axioms noteCreate_balance_neutral_matches_univA
#assert_axioms note_insert_is_out_of_row
#assert_axioms note_append_only_is_out_of_row
#assert_axioms goodNoteRow_isRow
#assert_axioms goodNoteRow_realizes_intent
#assert_axioms badNoteRow_rejected

-- STAGE-3 amplification (the bound `commitments` side-table root):
#assert_axioms noteCreateRootHash_binds
#assert_axioms noteCreateRoot_gate_faithful
#assert_axioms noteCreateRoot_rejects_wrong_root
#assert_axioms noteCreateFull_forces_freeze
#assert_axioms noteCreateFull_forces_root
#assert_axioms noteCreateFull_commit_binds_sysdigest
#assert_axioms noteCreateFull_binds_commitments_root
#assert_axioms noteCreateFull_sound
#assert_axioms goodRootRow_realizes
#assert_axioms badRootRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
