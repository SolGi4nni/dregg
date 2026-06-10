/-
# Dregg2.Circuit.Emit.EffectVmEmitSetField — the developer-facing `setFieldA` field-write effect's
  EffectVM-row circuit, EMITTED, promoted to **class A** (the transfer bar, per cell).

## Why setField reaches class A on the RUNNABLE row (unlike the cap/cell families)

`setFieldA` writes ONE per-cell field slot. The EffectVM row carries the cell's eight developer
field columns `fields[0..7]` (`state.FIELD_BASE + i`), and those columns ARE among the 13 the
deployed row's `state_commit` absorbs (the keystone's GROUP-4 sites hash `fields[0..7]` into the
published commitment — `EffectVmEmitTransferSound.absorbedCols`). So the moved content of a
`setFieldA` — the written field column — is an IN-COMMITMENT state-block column, EXACTLY like
transfer's `bal_lo`. The write is therefore bound + anti-ghosted by the same injective-commitment
tooth, NOT a params/effects-hash carrier (the class-C `setPermissions`/`setVK` gap). This is the
genuine per-cell class-A bar: the moved field column is forced to the written value, every other
column frozen, the WHOLE post-block bound under Poseidon2 CR, connected to the verified executor
`execFullA … (.setFieldA …)`.

## The descriptor (the per-field write, parameterized by the written slot)

`setFieldVmDescriptor slot` (`slot : Fin 8`): the per-row gates write `fields[slot]_after =
param.VALUE` (the written value rides the `param.AMOUNT` column, here named `VALUE`, the SAME role
transfer's amount column plays), and FREEZE every other state-block column — `bal_lo`, `bal_hi`,
`nonce`, `cap_root`, `reserved`, and the OTHER seven field columns. So the descriptor pins the WHOLE
per-cell post-block: one field moved to the written value, the rest literally frozen.

## What is bound (class A) vs the boundary (named)

  * BOUND + anti-ghosted (the 13 absorbed columns): `fields[slot]_after = VALUE` (the move) AND
    every other state-block column frozen. Tampering ANY of them moves `state_commit` ⇒ UNSAT
    (`setFieldVm_commit_binds_block`, inherited from the keystone's `absorbed_determined_by_commit`).
  * UNIFIED to the executor: `unify_setField_exec` welds the descriptor's bound block to
    `execFullA`'s `SetFieldSpec` post-state (the conserved `balLo` frozen; the written slot's value
    is the executor's `fieldOf (slotName slot) (cell)`).
  * THE BOUNDARY (named, the same shape transfer's nonce/turn-layer residual has): the
    executor's `SetFieldSpec` ALSO carries (a) the caveat+authority+membership+liveness GUARD (the
    executor's domain restriction — `SetFieldGuard`, NOT a per-row state-block fact; it is the
    record-layer guard the `SetFieldCommit` corner welds) and (b) the one-row receipt LOG append (off
    the per-row 13-column block — the turn/record-layer commitment). We state these exactly
    (`setField_guard_is_offrow`, `setField_log_is_offrow`) rather than papering them. The moved field
    + the frozen frame — the per-cell STATE transition — is fully bound; the guard and the log are
    the executor/record-layer legs, cited.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem; Poseidon2 CR enters
ONLY as the named `Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only (the keystone Sound module + the universe-A `cellstatefield` spec).
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatefield

namespace Dregg2.Circuit.Emit.EffectVmEmitSetField

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub ePrm gBalHi gNonce gCapPass gResPass gFieldPass
   transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec (balOf balanceField)
open Dregg2.Exec.TurnExecutorFull (execFullA)
open Dregg2.Exec.EffectsState (fieldOf setField setField_balOf)
open Dregg2.Circuit.Spec.CellStateField (SetFieldSpec SetFieldGuard setFieldCellMap
  execFullA_setFieldA_iff_spec setFieldSpec_writes_slot setFieldSpec_cell_frame)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the `setField` selector + the value-carrier param column. -/

/-- The `setField` selector column index (runtime `sel::SET_FIELD`). A LOCAL constant. -/
def SEL_SET_FIELD : Nat := 54

/-- The written value rides the `param.AMOUNT` column (the same carrier role transfer's amount has).
We name it `VALUE` for clarity: `fields[slot]_after = param.VALUE`. -/
def VALUE : Nat := param.AMOUNT

/-- The row is a setField row: `s_set_field = 1`, `s_noop = 0`. -/
def IsSetFieldRow (env : VmRowEnv) : Prop :=
  env.loc SEL_SET_FIELD = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — the per-row gates: write `fields[slot]`, freeze every other column.

`slot : Fin 8` is the written field slot. The write gate `gFieldWrite slot` forces
`fields[slot]_after = param.VALUE`. The other seven field columns + bal/nonce/cap/reserved are
FROZEN (passthrough). The nonce here is FROZEN (a field write does not tick the on-trace seq-nonce;
the runtime metadata bump is the `incrementNonce` row, distinct). -/

/-- The field-`slot` WRITE gate: `fields[slot]_after − param.VALUE = 0`. -/
def gFieldWrite (slot : Fin 8) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + slot.val)) (ePrm VALUE)

/-- Balance-lo FREEZE body. -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce FREEZE body (a field write does NOT tick the on-trace seq-nonce). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-- The seven OTHER field-passthrough gates (every field column except `slot`). -/
def gOtherFieldsAll (slot : Fin 8) : List VmConstraint :=
  ((List.range 8).filter (· ≠ slot.val)).map (fun i => VmConstraint.gate (gFieldPass i))

/-- The per-row gates: write `fields[slot]`, freeze the rest of the block. -/
def setFieldRowGates (slot : Fin 8) : List VmConstraint :=
  [ .gate (gFieldWrite slot), .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gOtherFieldsAll slot

/-! ## §2 — the emitted descriptor (slot-parameterized, keystone hash sites + PI pins). -/

def setFieldVmAirName : String := "dregg-effectvm-setfield-v1"

/-- **`setFieldVmDescriptor slot`** — the `setFieldA` EffectVM-row circuit for written slot `slot`:
the write+freeze gates ++ the 4 ordered GROUP-4 hash sites binding the WHOLE after-block (with the
written `fields[slot]` among the 13 absorbed columns) into the published `state_commit`. -/
def setFieldVmDescriptor (slot : Fin 8) : EffectVmDescriptor :=
  { name := setFieldVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := setFieldRowGates slot
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — the ROW INTENT: write `fields[slot]` to the value, freeze everything else. -/

/-- **`SetFieldRowIntent slot env`** — the field-`slot` write: `fields[slot]_after = param.VALUE`;
every OTHER state-block column FROZEN (bal limbs, nonce, cap_root, reserved, the other 7 fields). -/
def SetFieldRowIntent (slot : Fin 8) (env : VmRowEnv) : Prop :=
  env.loc (saCol (state.FIELD_BASE + slot.val)) = env.loc (prmCol VALUE)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, i ≠ slot.val →
      env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the field-write intent. -/

theorem setFieldVm_faithful (slot : Fin 8) (env : VmRowEnv) :
    (∀ c ∈ setFieldRowGates slot, c.holdsVm env false false) ↔ SetFieldRowIntent slot env := by
  unfold setFieldRowGates gOtherFieldsAll SetFieldRowIntent
  constructor
  · intro h
    have hWr  := h (.gate (gFieldWrite slot)) (by simp)
    have hLo  := h (.gate gBalLoFreeze) (by simp)
    have hHi  := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → i ≠ slot.val →
        VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi hne
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
        decide_eq_true_eq]
      exact Or.inr ⟨i, ⟨hi, hne⟩, rfl⟩
    simp only [VmConstraint.holdsVm, gFieldWrite, gBalLoFreeze, gBalHi, gNonceFreeze, gCapPass,
      gResPass, eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hWr hLo hHi hNon hCap hRes
    refine ⟨by linarith [hWr], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi hne
    have := hFld i hi hne
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hWr, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, ⟨hi, hne⟩, rfl⟩
    · simp only [VmConstraint.holdsVm, gFieldWrite, eSA, ePrm, eSub, EmittedExpr.eval]
      rw [hWr]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFreeze, eSA, eSB, eSub, EmittedExpr.eval]; rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi hne]; ring

/-! ## §5 — ANTI-GHOST (gate level): a wrong write / moved bystander column is rejected. -/

theorem setFieldVm_rejects_wrong_output (slot : Fin 8) (env : VmRowEnv)
    (hwrong : ¬ SetFieldRowIntent slot env) :
    ¬ (∀ c ∈ setFieldRowGates slot, c.holdsVm env false false) :=
  fun h => hwrong ((setFieldVm_faithful slot env).mp h)

/-- **Anti-ghost (wrong written value).** A row whose `fields[slot]_after ≠ VALUE` fails the write
gate — the written slot cannot carry anything but the bound value. -/
theorem setFieldVm_rejects_wrong_value (slot : Fin 8) (env : VmRowEnv)
    (hwrong : env.loc (saCol (state.FIELD_BASE + slot.val)) ≠ env.loc (prmCol VALUE)) :
    ¬ (VmConstraint.gate (gFieldWrite slot)).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gFieldWrite, eSA, ePrm, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-- **Anti-ghost (balance moved).** A field write that silently moves `bal_lo` fails the freeze gate. -/
theorem setFieldVm_rejects_moved_balance (slot : Fin 8) (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith

/-! ## §6 — the commitment binding (the WHOLE after-block, incl. the written field, is bound).

The hash sites are the keystone's, so the keystone's injective-commitment lemma applies verbatim:
the published `state_commit` is the genuine H4-of-H4 digest of the after-block's 13 absorbed columns
— and `fields[slot]` is one of them. So a prover cannot keep the published `NEW_COMMIT` while
tampering the written slot OR any frozen column. This is the class-A anti-ghost-on-ALL-of-it tooth. -/

theorem setFieldVm_commit_binds_block (slot : Fin 8) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §7 — the structured per-cell spec + RowEncodes decoding. -/

/-- `RowEncodesSF env pre post` ties the row's state-block columns to a `(pre, post)` transition,
plus the written-value column (`prmCol VALUE = post.fields slot`). -/
def RowEncodesSF (slot : Fin 8) (env : VmRowEnv) (pre post : CellState) : Prop :=
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
  ∧ env.loc (prmCol VALUE) = post.fields slot
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellSetFieldSpec slot pre v post`** — the per-cell FULL-state field-write spec: `fields[slot]`
written to `v`, every other field + bal/nonce/cap/reserved FROZEN. -/
def CellSetFieldSpec (slot : Fin 8) (pre : CellState) (v : ℤ) (post : CellState) : Prop :=
  post.fields slot = v
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved
  ∧ (∀ i : Fin 8, i ≠ slot → post.fields i = pre.fields i)

theorem intent_to_cellSpec (slot : Fin 8) (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesSF slot env pre post) (hint : SetFieldRowIntent slot env) :
    CellSetFieldSpec slot pre (env.loc (prmCol VALUE)) post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hVal, hOld, hNew⟩ := henc
  obtain ⟨hwr, hlo, hhi, hnon, hcap, hres, hflds⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaF slot]; exact hwr
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres
  · intro i hine
    have hiv : i.val ≠ slot.val := fun h => hine (Fin.ext h)
    rw [← hsaF i, ← hsbF i]; exact hflds i.val i.isLt hiv

/-! ## §8 — the full descriptor soundness + the commitment binding. -/

theorem setFieldDescriptor_full_sound (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesSF slot env pre post)
    (hsat : satisfiedVm hash (setFieldVmDescriptor slot) env true true) :
    CellSetFieldSpec slot pre (env.loc (prmCol VALUE)) post := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates : ∀ c ∈ setFieldRowGates slot, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ (setFieldVmDescriptor slot).constraints := hc
    have hh := hcs c hmem
    -- every constraint in `setFieldRowGates` is a `.gate`; `holdsVm` of a gate ignores the flags,
    -- so the `true true` satisfaction gives the `false false` form definitionally.
    unfold setFieldRowGates gOtherFieldsAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, _, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellSpec slot env pre post henc ((setFieldVm_faithful slot env).mp hgates)

theorem setFieldDescriptor_commit_binds_state (slot : Fin 8) (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash) (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash (setFieldVmDescriptor slot) e₁ true true)
    (hsat₂ : satisfiedVm hash (setFieldVmDescriptor slot) e₂ true true)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  setFieldVm_commit_binds_block slot hash hCR e₁ e₂ hsat₁.2.1 hsat₂.2.1 hcommit

/-! ## §9 — THE EXECUTOR UNIFICATION + the named honest boundary.

`cellProjF k cell slot` reads the cell's conserved balance into `balLo` and the developer field
`fieldOf (slotName slot) (cell)` into `fields slot`. A committed `execFullA … (.setFieldA …)`
(= `SetFieldSpec`, the cellstatefield executor⟺spec corner) writes that slot to `v` and freezes the
balance. We weld the descriptor's bound block to it, and NAME the two executor/record-layer legs the
per-row block does not carry: the GUARD and the LOG. -/

/-- The developer field-name for EffectVM slot `slot` (the runtime layout: slot `i` ↔ the i-th
developer field). A field write to `setField actor cell (slotName slot) v` lands in `fields slot`.
The eight slot names `field0..field7` are all DISTINCT from the conserved `balanceField` ("balance"),
so a field write to a `slot` never moves the conserved balance (`slotName_ne_balance`). -/
def slotName (slot : Fin 8) : FieldName := s!"slotfield{slot.val}"

/-- The eight slot field-names are distinct from the conserved `balanceField` — so a `setFieldA` to a
`slot` column freezes the conserved balance (`setField_balOf`). -/
theorem slotName_ne_balance (slot : Fin 8) : slotName slot ≠ balanceField := by
  fin_cases slot <;> decide

/-- Read cell `c`'s conserved balance + the field-`slot` value out of the real record-kernel state. -/
def cellProjF (k : RecordKernelState) (c : CellId) (slot : Fin 8) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun i => if i = slot then fieldOf (slotName slot) (k.cell c) else 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_setField_exec` — the executor unification.** A committed `execFullA … (.setFieldA actor
cell (slotName slot) v)` writes the `slot` field to exactly `v` and freezes the conserved balance —
so the per-cell `cellProjF` block AGREES with the descriptor's bound block: the written slot reads `v`
(the moved field) and `balLo` is frozen. The OTHER `cellProjF` field columns are the projection's
constant `0` (the projection carries only the touched slot + balance, the others having no per-cell
universe-A balance analogue — the same cellProj convention mint/transfer use). -/
theorem unify_setField_exec (s s' : RecChainedState) (actor cell : CellId) (slot : Fin 8) (v : Int)
    (h : execFullA s (.setFieldA actor cell (slotName slot) v) = some s') :
    (cellProjF s'.kernel cell slot).fields slot = v
    ∧ (cellProjF s'.kernel cell slot).balLo = (cellProjF s.kernel cell slot).balLo := by
  have hspec := (execFullA_setFieldA_iff_spec s actor cell (slotName slot) v s').mp h
  refine ⟨?_, ?_⟩
  · show (if slot = slot then fieldOf (slotName slot) (s'.kernel.cell cell) else 0) = v
    rw [if_pos rfl]; exact setFieldSpec_writes_slot hspec
  · show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
    -- the spec writes the target cell to `setField (slotName slot) (pre cell) (.int v)`; that slot
    -- is ≠ balanceField, so the conserved balance is frozen (`setField_balOf`).
    have htgt : s'.kernel.cell cell = setField (slotName slot) (s.kernel.cell cell) (.int v) := by
      rw [hspec.2.1]; simp only [setFieldCellMap, if_pos]
    rw [htgt]
    exact setField_balOf (slotName slot) (s.kernel.cell cell) (.int v) (slotName_ne_balance slot)

/-- **`setField_guard_is_offrow` — the named GUARD boundary.** A committed `setFieldA` carries the
4-leg admissibility guard (caveat ∧ authority ∧ membership ∧ liveness — `SetFieldGuard`). This is the
executor's DOMAIN RESTRICTION, NOT a per-row state-block column: the EffectVM row binds the STATE
TRANSITION (the moved field + frozen frame), while the guard is the record-layer gate the
`SetFieldCommit` corner welds (`setfield_circuit_full_sound`). Cited, not papered. -/
theorem setField_guard_is_offrow (s s' : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') :
    SetFieldGuard s actor cell f v :=
  ((execFullA_setFieldA_iff_spec s actor cell f v s').mp h).1

/-- **`setField_log_is_offrow` — the named LOG boundary.** A committed `setFieldA` prepends one
self-targeted receipt row to the chain log. The receipt LOG is off the per-row 13-column state block
(it is the turn/record-layer commitment `SetFieldCommit.cSFLog` binds, not a state-block column the
deployed EffectVM row carries). Cited, not papered. -/
theorem setField_log_is_offrow (s s' : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) (h : execFullA s (.setFieldA actor cell f v) = some s') :
    s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log :=
  ((execFullA_setFieldA_iff_spec s actor cell f v s').mp h).2.2.1

/-- **`setFieldDescriptor_classA` — the per-cell class-A capstone (the transfer bar, per cell).**
Satisfying the runnable descriptor under `RowEncodesSF`, for the written slot of a committed
`execFullA … (.setFieldA …)`, forces: (a) the FULL per-cell `CellSetFieldSpec` (the slot written to
the bound value, the WHOLE rest of the block frozen) from the descriptor; (b) the post-state
published as `PI[NEW_COMMIT]` and anti-ghosted on all 13 absorbed columns
(`setFieldDescriptor_commit_binds_state`); and (c) AGREEMENT with the executor's post-state on the
written slot value (= `v`) and the frozen balance. The guard + log are the named executor/record-layer
legs (`setField_guard_is_offrow` / `setField_log_is_offrow`). This is the transfer class-A capstone
shape, per cell. -/
theorem setFieldDescriptor_classA (slot : Fin 8) (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell : CellId) (v : Int) (post : CellState)
    (henc : RowEncodesSF slot env (cellProjF s.kernel cell slot) post)
    (hval : env.loc (prmCol VALUE) = v)
    (hsat : satisfiedVm hash (setFieldVmDescriptor slot) env true true)
    (hexec : execFullA s (.setFieldA actor cell (slotName slot) v) = some s') :
    CellSetFieldSpec slot (cellProjF s.kernel cell slot) v post
    ∧ post.fields slot = (cellProjF s'.kernel cell slot).fields slot
    ∧ post.balLo = (cellProjF s'.kernel cell slot).balLo := by
  have hspec := setFieldDescriptor_full_sound slot hash env (cellProjF s.kernel cell slot) post henc hsat
  rw [hval] at hspec
  obtain ⟨heVal, heBal⟩ := unify_setField_exec s s' actor cell slot v hexec
  refine ⟨hspec, ?_, ?_⟩
  · rw [hspec.1, heVal]
  · rw [hspec.2.1]
    show (cellProjF s.kernel cell slot).balLo = (cellProjF s'.kernel cell slot).balLo
    rw [heBal]

/-! ## §10 — NON-VACUITY (concrete literal-column witnesses).

The witness row branches on the LITERAL column indices (`saCol (FIELD_BASE+0)=79`, `prmCol VALUE=68`,
`sbCol/saCol BALANCE_LO=54/76`, `NONCE=56/78`), pinned by `#guard`s for anti-drift. So the realization
+ rejection proofs reduce by `decide`. -/

/-- A concrete setField row (slot 0): `fields[0] 0 → 7` (the written VALUE `7`), the rest frozen
(bal_lo 100 → 100, nonce 5 → 5). Literal columns (`#guard`-pinned below): 54=SEL_SET_FIELD,
79=saCol field0, 68=prmCol VALUE, 54=sbCol bal_lo, 76=saCol bal_lo, 56=sbCol nonce, 78=saCol nonce. -/
def goodSFRow : VmRowEnv where
  loc := fun w =>
    if w = 79 then 7        -- saCol field0 (the written slot)
    else if w = 68 then 7   -- prmCol VALUE (the written value carrier)
    else if w = 54 then 100 -- sbCol bal_lo
    else if w = 76 then 100 -- saCol bal_lo
    else if w = 56 then 5   -- sbCol nonce
    else if w = 78 then 5   -- saCol nonce
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness columns ARE the symbolic carriers (anti-drift).
#guard saCol (state.FIELD_BASE + (0 : Fin 8).val) == 79
#guard prmCol VALUE == 68
#guard sbCol state.BALANCE_LO == 54
#guard saCol state.BALANCE_LO == 76
#guard sbCol state.NONCE == 56
#guard saCol state.NONCE == 78

/-- **NON-VACUITY (witness TRUE).** `goodSFRow` REALIZES the field-write intent (`fields[0] := 7`,
the rest frozen). -/
theorem goodSFRow_realizes_intent : SetFieldRowIntent 0 goodSFRow := by
  have hF0 : saCol (state.FIELD_BASE + (0 : Fin 8).val) = 79 := by decide
  have hV  : prmCol VALUE = 68 := by decide
  have hsbL : sbCol state.BALANCE_LO = 54 := by decide
  have hsaL : saCol state.BALANCE_LO = 76 := by decide
  have hsbH : sbCol state.BALANCE_HI = 55 := by decide
  have hsaH : saCol state.BALANCE_HI = 77 := by decide
  have hsbN : sbCol state.NONCE = 56 := by decide
  have hsaN : saCol state.NONCE = 78 := by decide
  have hsbC : sbCol state.CAP_ROOT = 65 := by decide
  have hsaC : saCol state.CAP_ROOT = 87 := by decide
  have hsbR : sbCol state.RESERVED = 67 := by decide
  have hsaR : saCol state.RESERVED = 89 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show goodSFRow.loc (saCol (state.FIELD_BASE + (0:Fin 8).val)) = goodSFRow.loc (prmCol VALUE)
    rw [hF0, hV]; decide
  · show goodSFRow.loc (saCol state.BALANCE_LO) = goodSFRow.loc (sbCol state.BALANCE_LO)
    rw [hsaL, hsbL]; decide
  · show goodSFRow.loc (saCol state.BALANCE_HI) = goodSFRow.loc (sbCol state.BALANCE_HI)
    rw [hsaH, hsbH]; decide
  · show goodSFRow.loc (saCol state.NONCE) = goodSFRow.loc (sbCol state.NONCE)
    rw [hsaN, hsbN]; decide
  · show goodSFRow.loc (saCol state.CAP_ROOT) = goodSFRow.loc (sbCol state.CAP_ROOT)
    rw [hsaC, hsbC]; decide
  · show goodSFRow.loc (saCol state.RESERVED) = goodSFRow.loc (sbCol state.RESERVED)
    rw [hsaR, hsbR]; decide
  · intro i hi hne
    have hiv : i ≠ 0 := by simpa using hne
    show goodSFRow.loc (saCol (state.FIELD_BASE + i)) = goodSFRow.loc (sbCol (state.FIELD_BASE + i))
    have hsa : saCol (state.FIELD_BASE + i) = 79 + i := by
      simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
        NUM_PARAMS, state.FIELD_BASE]; omega
    have hsb : sbCol (state.FIELD_BASE + i) = 57 + i := by
      simp only [sbCol, STATE_BEFORE_BASE, NUM_EFFECTS, state.FIELD_BASE]; omega
    rw [hsa, hsb]
    show goodSFRow.loc (79 + i) = goodSFRow.loc (57 + i)
    simp only [goodSFRow]
    have a1 : (79 + i = 79) = False := eq_false (by omega)
    have a2 : (79 + i = 68) = False := eq_false (by omega)
    have a3 : (79 + i = 54) = False := eq_false (by omega)
    have a4 : (79 + i = 76) = False := eq_false (by omega)
    have a5 : (79 + i = 56) = False := eq_false (by omega)
    have a6 : (79 + i = 78) = False := eq_false (by omega)
    have b1 : (57 + i = 79) = False := eq_false (by omega)
    have b2 : (57 + i = 68) = False := eq_false (by omega)
    have b3 : (57 + i = 54) = False := eq_false (by omega)
    have b4 : (57 + i = 76) = False := eq_false (by omega)
    have b5 : (57 + i = 56) = False := eq_false (by omega)
    have b6 : (57 + i = 78) = False := eq_false (by omega)
    simp only [a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, b6, if_false]

/-- A FORGED setField row: `goodSFRow` with the written `fields[0]` (col 79) overwritten to
`999 ≠ VALUE`. -/
def badSFRow : VmRowEnv where
  loc := fun w => if w = 79 then 999 else goodSFRow.loc w
  nxt := goodSFRow.nxt
  pub := goodSFRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSFRow`'s written `fields[0]` is forged
(`999 ≠ 7`), so the write gate REJECTS it. -/
theorem badSFRow_rejected : ¬ (VmConstraint.gate (gFieldWrite 0)).holdsVm badSFRow false false := by
  apply setFieldVm_rejects_wrong_value
  have hF0 : saCol (state.FIELD_BASE + (0 : Fin 8).val) = 79 := by decide
  have hV  : prmCol VALUE = 68 := by decide
  rw [hF0, hV]
  show badSFRow.loc 79 ≠ badSFRow.loc 68
  decide

/-! ## §11 — Axiom-hygiene tripwires + layout pins. -/

#guard (setFieldVmDescriptor 0).constraints.length == 6 + 7
#guard (setFieldVmDescriptor 0).hashSites.length == 4
#guard (setFieldVmDescriptor 0).traceWidth == 186
#guard VALUE == param.AMOUNT

#assert_axioms setFieldVm_faithful
#assert_axioms setFieldVm_rejects_wrong_output
#assert_axioms setFieldVm_rejects_wrong_value
#assert_axioms setFieldVm_rejects_moved_balance
#assert_axioms setFieldVm_commit_binds_block
#assert_axioms intent_to_cellSpec
#assert_axioms setFieldDescriptor_full_sound
#assert_axioms setFieldDescriptor_commit_binds_state
#assert_axioms slotName_ne_balance
#assert_axioms unify_setField_exec
#assert_axioms setField_guard_is_offrow
#assert_axioms setField_log_is_offrow
#assert_axioms setFieldDescriptor_classA
#assert_axioms goodSFRow_realizes_intent
#assert_axioms badSFRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSetField
