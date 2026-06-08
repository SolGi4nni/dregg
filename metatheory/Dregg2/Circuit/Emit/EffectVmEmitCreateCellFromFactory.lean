/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory — the `createCellFromFactory` effect's
  EffectVM-row circuit, EMITTED.

`createCellFromFactory` looks up a conforming registered factory, MINTS a fresh `newCell` carrying the
factory's `initialFields` + program-VK slot + `slotCaveats`, born-empty on every per-cell side-table,
grows `accounts`, and prepends a creation receipt. Its FULL universe-A soundness is
`Inst.CreateCellFromFactoryA.createCellFromFactoryA_full_sound ⇒ CreateFromFactorySpec` (the
EffectCommit2-QUINT layer; all 18 components + log, existentially over the looked-up `FactoryEntry`).

This module emits the EffectVM-ROW face and connects it to that guarantee.

## What the EffectVM row CAN pin (finding-#2, honest)

The row carries one cell's 14-column ECONOMIC state-block. For `createCellFromFactory`, the minted
`newCell` is born `balance == 0` (the factory's `initialFields` are NON-`balance` slots — guaranteed
by `FactoryEntry.conforms ⇒ initialFieldsNoBalance`), so the cell's ECONOMIC block (the `balance`
measure) is the ZERO value. The row pins the post-block is the born-empty ZERO economic block, bound
into the published `state_commit` under Poseidon2 CR.

## What the EffectVM row CANNOT enforce (the honest boundary)

The HEART of `createCellFromFactory` is OFF-ROW:
  * the factory `initialFields` + program-VK installed into the minted cell's RECORD — these map into
    the cell-record's NON-`balance` fields, which have NO EffectVM-column counterpart (the 14-col
    block carries the conserved `balance` measure, not arbitrary record fields);
  * the factory `slotCaveats` install (the cell's published lifetime invariants);
  * `accounts` GROWTH; the per-cell side-table resets; the creation receipt;
  * the factory-existence + conformance + freshness + mint-authority guard (`factoryAdmit`).

These live ONLY in `createCellFromFactoryA_full_sound`/`CreateFromFactorySpec`; the row witnesses NONE
of them. We connect the ONE overlap (the minted cell's ECONOMIC balance is 0) and FLAG the rest as
off-row.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
hypothesis. No `sorry`, no `:= True`, no `native_decide`. Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.factorycreation

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eSA)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (installInitialFields factoryVkField)
open Dregg2.Exec.EffectsState (setField)
open Dregg2.Circuit.Spec.FactoryCreation

set_option linter.unusedVariables false

/-! ## §0 — the `createCellFromFactory` selector column (local). -/

/-- The `createCellFromFactory` selector column index (next free after `createCell`). -/
def SEL_CREATECELLFROMFACTORY : Nat := 3

/-! ## §1 — the BORN-EMPTY (frozen-to-zero) per-row gates (the minted cell's economic block is zero).

Identical SHAPE to `createCell`: the row witnessing `newCell` carries the ZERO economic block (the
factory writes only NON-`balance` record fields, which have no economic-column counterpart). -/

/-- The born-empty zero gate for state-block column `off`: `state_after[off] = 0`. -/
def gZero (off : Nat) : VmConstraint := .gate (eSA off)

/-- The 13 born-empty zero gates over the economic-data columns. -/
def factoryRowGates : List VmConstraint :=
  [ gZero state.BALANCE_LO, gZero state.BALANCE_HI, gZero state.NONCE
  , gZero state.CAP_ROOT, gZero state.RESERVED ]
  ++ (List.range 8).map (fun i => gZero (state.FIELD_BASE + i))

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused, ordered). -/

/-- The ordered GROUP-4 hash sites (the per-row layout, reused). -/
def factoryHashSites : List VmHashSite := EffectVmEmitTransfer.transferHashSites

/-! ## §3 — the emitted descriptor. -/

/-- The `createCellFromFactory` EffectVM-row AIR identity. -/
def factoryVmAirName : String := "dregg-effectvm-createcellfromfactory-v1"

/-- **`factoryVmDescriptor`** — the `createCellFromFactory` EffectVM-row circuit: the born-empty zero
gates + the 4 ordered GROUP-4 hash sites binding the zero economic block into `state_commit`. -/
def factoryVmDescriptor : EffectVmDescriptor :=
  { name := factoryVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := factoryRowGates
  , hashSites := factoryHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the BORN-EMPTY row intent. -/

/-- **`BornEmptyRowIntent env`** — the row's post-block is the all-zero economic block. -/
def BornEmptyRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = 0
  ∧ env.loc (saCol state.BALANCE_HI) = 0
  ∧ env.loc (saCol state.NONCE) = 0
  ∧ env.loc (saCol state.CAP_ROOT) = 0
  ∧ env.loc (saCol state.RESERVED) = 0
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = 0)

/-! ## §5 — FAITHFULNESS: the emitted per-row gates ⟺ the born-empty intent. -/

theorem factoryVm_faithful (env : VmRowEnv) :
    (∀ c ∈ factoryRowGates, c.holdsVm env false false) ↔ BornEmptyRowIntent env := by
  unfold factoryRowGates BornEmptyRowIntent
  constructor
  · intro h
    have hLo := h (gZero state.BALANCE_LO) (by simp [gZero])
    have hHi := h (gZero state.BALANCE_HI) (by simp [gZero])
    have hN  := h (gZero state.NONCE) (by simp [gZero])
    have hCap := h (gZero state.CAP_ROOT) (by simp [gZero])
    have hRes := h (gZero state.RESERVED) (by simp [gZero])
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (gZero (state.FIELD_BASE + i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at hLo hHi hN hCap hRes
    refine ⟨hLo, hHi, hN, hCap, hRes, ?_⟩
    intro i hi
    have := hFld i hi
    simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval] at this
    exact this
  · rintro ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
    · exact hLo
    · exact hHi
    · exact hN
    · exact hCap
    · exact hRes
    · exact hFld i hi

/-! ## §6 — ANTI-GHOST. -/

theorem factoryVm_rejects_nonzero (env : VmRowEnv) (hwrong : ¬ BornEmptyRowIntent env) :
    ¬ (∀ c ∈ factoryRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((factoryVm_faithful env).mp h)

theorem factoryVm_rejects_nonzero_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ 0) :
    ¬ (gZero state.BALANCE_LO).holdsVm env false false := by
  simp only [gZero, VmConstraint.holdsVm, eSA, EmittedExpr.eval]
  exact hwrong

/-! ## §7 — the commitment binding (inherited from the keystone). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols absorbed_determined_by_commit)

theorem factoryVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ factoryHashSites)
    (hs₂ : siteHoldsAll hash e₂ factoryHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — the minted cell's ECONOMIC balance is `0` (the overlap with the executor).

The factory writes only NON-`balance` record fields (`FactoryEntry.conforms ⇒ initialFieldsNoBalance`).
We prove `balOf (factoryPostCell base newCell e newCell) = 0` whenever the base cell carries `balance
== 0` — by induction over `installInitialFields` through `setField_balOf` (each install touches a
field `≠ balanceField`), then the outer `factoryVkField` write (also `≠ balanceField`). -/

/-- `installInitialFields` over a list of NON-`balance` fields preserves `balOf`. -/
theorem installInitialFields_balOf (cell : Value) (fs : List (FieldName × Int))
    (hnb : fs.all (fun p => p.1 != balanceField) = true) :
    balOf (installInitialFields cell fs) = balOf cell := by
  induction fs generalizing cell with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨f, v⟩ := hd
      simp only [List.all_cons, Bool.and_eq_true] at hnb
      obtain ⟨hf, htl⟩ := hnb
      have hfne : f ≠ balanceField := by simpa using hf
      simp only [installInitialFields]
      rw [ih (setField f cell (.int v)) htl, EffectsState.setField_balOf f cell (.int v) hfne]

/-- **`factoryPostCell_balOf_zero` — the minted cell carries `balance == 0`.** Under a conforming
factory `e`, the post-cell built over the born-empty base (`default`, `balOf default = 0`) has
`balOf = 0`: the program-VK write (`factoryVkField ≠ balanceField`) and the conforming
non-`balance` initial fields both preserve `balOf`. -/
theorem factoryPostCell_balOf_zero (base : CellId → Value) (newCell : CellId) (e : FactoryEntry)
    (hconf : e.conforms = true) (hbase : balOf (base newCell) = 0) :
    balOf (factoryPostCell base newCell e newCell) = 0 := by
  have hnb := FactoryEntry.conforms_no_balance e hconf
  unfold factoryPostCell
  rw [if_pos rfl]
  have hvkne : factoryVkField ≠ balanceField := by decide
  rw [EffectsState.setField_balOf factoryVkField _ (.int e.programVk) hvkne]
  rw [installInitialFields_balOf (base newCell) e.initialFields hnb, hbase]

/-! ## §9 — CONNECTOR to universe-A `CreateFromFactorySpec` via `cellProj`. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`factory_newcell_is_zero` — the OVERLAP, from the executor.** A committed
`createCellFromFactory` (`CreateFromFactorySpec`) mints `newCell` with `balance == 0`: the projected
after-block of `newCell` is the all-zero economic block. So `BornEmptyRowIntent` is the executor's
effect on `newCell`'s economic block. -/
theorem factory_newcell_is_zero (st st' : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hspec : CreateFromFactorySpec st actor newCell vk st') :
    (cellProj st'.kernel newCell).balLo = 0
    ∧ (cellProj st'.kernel newCell).balHi = 0
    ∧ (cellProj st'.kernel newCell).nonce = 0
    ∧ (cellProj st'.kernel newCell).capRoot = 0
    ∧ (cellProj st'.kernel newCell).reserved = 0
    ∧ (∀ i, (cellProj st'.kernel newCell).fields i = 0) := by
  obtain ⟨e, hadm, _, _, hcell, _⟩ := hspec
  obtain ⟨_, _, hconf, _, _⟩ := hadm
  refine ⟨?_, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  -- balLo = balOf (k'.cell newCell) = balOf (factoryPostCell (factoryBornCell ...) newCell e) = 0
  show balOf (st'.kernel.cell newCell) = 0
  rw [hcell]
  apply factoryPostCell_balOf_zero
  · exact hconf
  · -- the born-empty base at newCell is `default`, balOf default = 0
    show balOf (factoryBornCell st.kernel newCell newCell) = 0
    unfold factoryBornCell
    rw [if_pos rfl]
    rfl

/-- **`factory_row_matches_executor` — the CONNECTOR.** If the row's after-block decodes to `post`,
the gates hold, and the executor commits `CreateFromFactorySpec`, the row's pinned economic block is
the executor's minted-`newCell` economic block (all zero). -/
theorem factory_row_matches_executor (env : VmRowEnv) (pre post : CellState)
    (p : EffectVmEmitTransferSound.TransferParams)
    (henc : RowEncodes env pre p post)
    (hgates : ∀ c ∈ factoryRowGates, c.holdsVm env false false)
    (st st' : RecChainedState) (actor newCell : CellId) (vk : Int)
    (hspec : CreateFromFactorySpec st actor newCell vk st') :
    post.balLo = (cellProj st'.kernel newCell).balLo
    ∧ post.balHi = (cellProj st'.kernel newCell).balHi
    ∧ post.capRoot = (cellProj st'.kernel newCell).capRoot
    ∧ post.reserved = (cellProj st'.kernel newCell).reserved
    ∧ (∀ i, post.fields i = (cellProj st'.kernel newCell).fields i) := by
  obtain ⟨hLo, hHi, hN, hCap, hRes, hFld⟩ := (factoryVm_faithful env).mp hgates
  obtain ⟨eLo, eHi, eN, eCap, eRes, eFld⟩ := factory_newcell_is_zero st st' actor newCell vk hspec
  obtain ⟨_, _, _, _, _, _, _, _, _, hsaLo, hsaHi, _, hsaF, hsaCap, hsaRes, _, _, _⟩ := henc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [eLo, ← hsaLo]; exact hLo
  · rw [eHi, ← hsaHi]; exact hHi
  · rw [eCap, ← hsaCap]; exact hCap
  · rw [eRes, ← hsaRes]; exact hRes
  · intro i; rw [eFld i, ← hsaF i]; exact hFld i.val i.isLt

/-! ## §10 — THE HONEST BOUNDARY: the LARGE off-row side-effect.

`CreateFromFactorySpec` enforces FIVE things the EffectVM row does NOT carry: the factory
`initialFields`/program-VK install into the cell record, the `slotCaveats` install, `accounts` growth,
the per-cell side-table resets, and the creation receipt — plus the factory-existence/conformance/
freshness/mint guard. The row's `BornEmptyRowIntent` constrains NONE of these (no EffectVM column
carries arbitrary record fields, caveats, the accounts set, or the log). -/

/-- **`factory_offrow_unenforced` — the loud off-row finding.** `BornEmptyRowIntent` is invariant
under any change to columns OTHER than the `state_after` economic block: two rows agreeing on the
economic after-columns satisfy the intent equally, regardless of (the unrepresented) factory
fields/VK/caveats, accounts growth, side-tables, or receipt. The factory-install / account-growth /
caveat soundness lives ONLY in `createCellFromFactoryA_full_sound`. -/
theorem factory_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off)) →
      (BornEmptyRowIntent env₁ ↔ BornEmptyRowIntent env₂)) := by
  intro env₁ env₂ hagree
  unfold BornEmptyRowIntent
  rw [hagree state.BALANCE_LO, hagree state.BALANCE_HI, hagree state.NONCE,
      hagree state.CAP_ROOT, hagree state.RESERVED]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [← hagree (state.FIELD_BASE + i)]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by rw [hagree (state.FIELD_BASE + i)]; exact f i hi⟩

/-! ## §11 — NON-VACUITY. -/

/-- A concrete born-empty row. -/
def zeroRow : VmRowEnv where
  loc := fun v => if v = SEL_CREATECELLFROMFACTORY then 1 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `zeroRow` realizes the born-empty intent. -/
theorem zeroRow_realizes_intent : BornEmptyRowIntent zeroRow := by
  unfold BornEmptyRowIntent zeroRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (if saCol state.BALANCE_LO = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.BALANCE_HI = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.NONCE = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.CAP_ROOT = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · show (if saCol state.RESERVED = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]; · decide
  · intro i hi
    show (if saCol (state.FIELD_BASE + i) = SEL_CREATECELLFROMFACTORY then (1:ℤ) else 0) = 0
    rw [if_neg]
    simp only [saCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE,
      NUM_PARAMS, state.FIELD_BASE, SEL_CREATECELLFROMFACTORY]
    omega

/-- A FORGED row: `zeroRow` with post-`bal_lo` tampered to `5`. -/
def forgedRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 5 else zeroRow.loc v
  nxt := zeroRow.nxt
  pub := zeroRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `forgedRow`'s post-`bal_lo` is non-zero. -/
theorem forgedRow_rejected : ¬ (gZero state.BALANCE_LO).holdsVm forgedRow false false := by
  apply factoryVm_rejects_nonzero_balance
  show (if saCol state.BALANCE_LO = saCol state.BALANCE_LO then (5:ℤ)
    else zeroRow.loc (saCol state.BALANCE_LO)) ≠ 0
  rw [if_pos rfl]; norm_num

/-! ## §12 — axiom-hygiene tripwires. -/

#guard factoryVmDescriptor.constraints.length == 13
#guard factoryVmDescriptor.hashSites.length == 4
#guard factoryVmDescriptor.traceWidth == 186

#assert_axioms factoryVm_faithful
#assert_axioms factoryVm_rejects_nonzero
#assert_axioms factoryVm_rejects_nonzero_balance
#assert_axioms factoryVm_commit_binds_block
#assert_axioms installInitialFields_balOf
#assert_axioms factoryPostCell_balOf_zero
#assert_axioms factory_newcell_is_zero
#assert_axioms factory_row_matches_executor
#assert_axioms factory_offrow_unenforced
#assert_axioms zeroRow_realizes_intent
#assert_axioms forgedRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCreateCellFromFactory
