/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteCreate — the noteCreate (note-COMMITMENT publish) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/noteCreateA.lean`, `Spec/notecommitment.lean`) carries the FULL-state soundness
`execNoteCreateA_iff_spec ⇒ NoteCreateASpec`: a committed publish PREPENDS a fresh commitment `cm`
onto the `commitments` SET, advances the chained `log` by `escrowReceiptA actor ::`, and is otherwise
TOTALLY NEUTRAL — it is balance-neutral (`noteCreateA_bal_neutral`) and FREEZES all 16 other kernel
fields. `noteCreate` is the APPEND-ONLY dual of `noteSpend`: NO guard at all (always commits).

## THE KEY STRUCTURAL FACT (and the honest IR boundary)

A noteCreate touches NEITHER the per-asset `bal` ledger NOR any per-cell state-block column. The ONLY
state it mutates is the `commitments` SET — a set the EffectVM 14-column state block has NO column for,
and the GROUP-4 hash-sites absorb NONE of. So, projected onto ONE EffectVM cell's state block, a
noteCreate is a PURE FREEZE: every state-block column (balance limbs, nonce, the 8 fields, cap_root,
reserved) is UNCHANGED (`state_after = state_before`), and the published `state_commit` is therefore
the genuine digest of the FROZEN after-state (= the before-state).

What the IR DOES support is exactly this FREEZE + the commitment binding of the frozen block: the
descriptor pins `state_after = state_before` per column and binds the (unchanged) after-state into
`state_commit` via the SAME GROUP-4 chain as transfer. This is the conservation / balance-neutrality
tooth — genuine and load-bearing (a row claiming a noteCreate but mutating any cell is UNSAT).

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
  (eSB eSA eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The noteCreate selector. -/

/-- The note-commitment-publish selector column index. -/
def SEL_NOTE_CREATE : Nat := 4

/-- The publish row is a noteCreate row: `s_note_create = 1`, `s_noop = 0`. -/
def IsNoteCreateRow (env : VmRowEnv) : Prop :=
  env.loc SEL_NOTE_CREATE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (WHOLE state-block FREEZE).

A noteCreate moves nothing on the conserved cell: every state-block column is frozen. We emit the
balance-lo FREEZE (`gBalLoFreeze`) and nonce FREEZE (`gNonceFreeze`) bodies; bal_hi / cap_root /
reserved / the 8 fields freeze bodies are REUSED from the transfer template (identical polynomials). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — the publish moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the publish leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The note-commitment-publish AIR identity. -/
def noteCreateVmAirName : String := "dregg-effectvm-notecreate-v1"

/-- The per-row gates: bal_lo freeze, bal_hi freeze, nonce freeze, cap/reserved freeze, 8 fields freeze
— the WHOLE state block frozen. -/
def noteCreateRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
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

/-- **`NoteCreateRowIntent env`** — the intended noteCreate move on the row `env.loc`: every
state-block column is UNCHANGED (`state_after = state_before`). The actual commitment-set insert is
out-of-row (the §IR flag). -/
def NoteCreateRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the freeze intent. -/

/-- **`noteCreateVm_faithful`.** On a noteCreate row, the emitted descriptor's per-row gates all hold
IFF `NoteCreateRowIntent` holds — the gates pin EXACTLY the whole-block freeze. -/
theorem noteCreateVm_faithful (env : VmRowEnv) :
    (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) ↔ NoteCreateRowIntent env := by
  unfold noteCreateRowGates gFieldPassAll NoteCreateRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a row that MUTATES any state-block cell on a noteCreate is rejected. -/

/-- **Anti-ghost (general).** A noteCreate row whose state block is NOT frozen (any column moved) does
NOT satisfy the per-row gates — the conservation tooth. -/
theorem noteCreateVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ NoteCreateRowIntent env) :
    ¬ (∀ c ∈ noteCreateRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((noteCreateVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A noteCreate row whose post-`bal_lo` is NOT the pre-`bal_lo`
(value forged out of thin air on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze`
alone rejects it (UNSAT). -/
theorem noteCreateVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesNote env pre post` ties the row's state-block columns to a `(pre, post)` cell transition
(no params — a noteCreate carries the commitment off-block). -/
def RowEncodesNote (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellNoteSpec pre post`** — the per-cell FULL-state noteCreate spec: the WHOLE cell state is
FROZEN (`post = pre` on every data column). This is the EffectVM-row projection of `NoteCreateASpec`'s
balance-neutrality + per-cell frame freeze (the commitment-set insert is off-block — the §IR flag). -/
def CellNoteSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesNote`, `NoteCreateRowIntent` IS the structured `CellNoteSpec`. -/
theorem intent_to_cellNoteSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesNote env pre post) (hint : NoteCreateRowIntent env) :
    CellNoteSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
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
theorem noteCreateDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesNote env pre post)
    (hsat : satisfiedVm hash noteCreateVmDescriptor env true true) :
    CellNoteSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
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
  have hint := (noteCreateVm_faithful env).mp hgates'
  refine ⟨intent_to_cellNoteSpec env pre post henc hint, ?_⟩
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
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

/-! ## §9 — CONNECTOR to universe-A: `CellNoteSpec` IS `NoteCreateASpec`'s per-cell frame image.

`execNoteCreateA_iff_spec ⇒ NoteCreateASpec` carries balance-neutrality (`bal' = bal`) and the per-cell
frame freeze (`cell' = cell`). We project ONE cell into the keystone `CellState` (the conserved `balLo`
limb reads the per-asset entry `bal c asset`; the other EffectVM limbs are `0`, FROZEN) and prove the
projection of ANY cell satisfies `CellNoteSpec` EXACTLY (all FROZEN). The commitment-set insert is the
§IR-extension flag, reported below as out-of-row. -/

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

/-- **`unify_note_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`NoteCreateASpec` post-state, satisfies the keystone's `CellNoteSpec` EXACTLY: `balLo` is FROZEN
(`bal' = bal`, balance-neutral); balHi/nonce/fields/capRoot/reserved frozen (`0 = 0`). So `CellNoteSpec`
IS `NoteCreateASpec`'s per-cell frame image — NOT a fourth spec. -/
theorem unify_note_freeze (st st' : RecChainedState) (cm : Nat) (actor c : CellId) (asset : AssetId)
    (hspec : NoteCreateASpec st cm actor st') :
    CellNoteSpec (cellProjNote st.kernel.bal c asset) (cellProjNote st'.kernel.bal c asset) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_note`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed noteCreate agrees with the executor's per-cell post-state: the descriptor's
pinned post-state (frozen) equals the executor's frozen cell on every state-block column. The
commitment-set insert is out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_note
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (cm : Nat) (actor c : CellId) (asset : AssetId) (pre post : CellState)
    (hpre : pre = cellProjNote st.kernel.bal c asset)
    (henc : RowEncodesNote env pre post)
    (hsat : satisfiedVm hash noteCreateVmDescriptor env true true)
    (hspec : NoteCreateASpec st cm actor st') :
    post.balLo = (cellProjNote st'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjNote st'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjNote st'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjNote st'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjNote st'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := noteCreateDescriptor_full_sound hash env pre post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ := unify_note_freeze st st' cm actor c asset hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

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

/-! ## §12 — NON-VACUITY: a concrete frozen noteCreate row realizes the intent; a minting one rejected. -/

/-- A concrete noteCreate row: every state-block column frozen (bal_lo 100 → 100, nonce 5 → 5, frame
fixed at 0). -/
def goodNoteRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_NOTE_CREATE then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodNoteRow` REALIZES the noteCreate freeze intent: every
state-block column unchanged (`100 → 100`, `5 → 5`, frame fixed). -/
theorem goodNoteRow_realizes_intent : NoteCreateRowIntent goodNoteRow := by
  unfold NoteCreateRowIntent goodNoteRow
  simp only [sbCol, saCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 4) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have f1 : (54 + (3 + i) = 4) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED noteCreate row: `goodNoteRow` with the post-`bal_lo` minted to `999` (a balance-neutral
effect cannot move value). -/
def badNoteRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodNoteRow.loc v
  nxt := goodNoteRow.nxt
  pub := goodNoteRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badNoteRow`'s post-`bal_lo` is NOT frozen
(forged mint), so the `gBalLoFreeze` gate REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badNoteRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badNoteRow false false := by
  apply noteCreateVm_rejects_balance_mint
  simp only [badNoteRow, goodNoteRow, sbCol, saCol, SEL_NOTE_CREATE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
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
#assert_axioms unify_note_freeze
#assert_axioms descriptor_agrees_with_executor_note
#assert_axioms note_insert_is_out_of_row
#assert_axioms note_append_only_is_out_of_row
#assert_axioms goodNoteRow_realizes_intent
#assert_axioms badNoteRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
