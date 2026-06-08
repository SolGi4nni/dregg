/-
# Dregg2.Circuit.Emit.EffectVmEmitNoteSpend — the noteSpend (note-NULLIFIER / anti-replay) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/noteSpendA.lean`, `Spec/notenullifier.lean`) carries the FULL-state soundness
`execFullA_noteSpend_iff_spec ⇒ NoteSpendSpec`: a committed spend PREPENDS the consumed nullifier `nf`
onto the `nullifiers` SET, advances the chained `log` by `escrowReceiptA actor ::`, and is otherwise
TOTALLY NEUTRAL — it is balance-neutral (`execFullA_noteSpend_bal_frame`) and FREEZES all 16 other
kernel fields. Its GUARD is the §8 spending proof (`spendProof = true`) ∧ the DOUBLE-SPEND gate
(`nf ∉ nullifiers`).

## THE KEY STRUCTURAL FACT (and the honest IR boundary)

A noteSpend touches NEITHER the per-asset `bal` ledger NOR any per-cell state-block column. The ONLY
state it mutates is the `nullifiers` SET — a set the EffectVM 14-column state block has NO column for,
and the GROUP-4 hash-sites absorb NONE of. So, projected onto ONE EffectVM cell's state block, a
noteSpend is a PURE FREEZE: every state-block column (balance limbs, nonce, the 8 fields, cap_root,
reserved) is UNCHANGED (`state_after = state_before`), and the published `state_commit` is the genuine
digest of the FROZEN after-state.

What the IR DOES support is exactly this FREEZE + the commitment binding of the frozen block: the
descriptor pins `state_after = state_before` per column and binds the (unchanged) after-state into
`state_commit` via the SAME GROUP-4 chain as transfer. This is the conservation / balance-neutrality
tooth — genuine (a row claiming a noteSpend but mutating any cell is UNSAT).

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
  (eSB eSA eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The noteSpend selector. -/

/-- The note-nullifier-spend selector column index. -/
def SEL_NOTE_SPEND : Nat := 5

/-- The spend row is a noteSpend row: `s_note_spend = 1`, `s_noop = 0`. -/
def IsNoteSpendRow (env : VmRowEnv) : Prop :=
  env.loc SEL_NOTE_SPEND = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (WHOLE state-block FREEZE). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — the spend moves no value). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the spend leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted descriptor. -/

/-- The note-nullifier-spend AIR identity. -/
def noteSpendVmAirName : String := "dregg-effectvm-notespend-v1"

/-- The per-row gates: WHOLE state block frozen. -/
def noteSpendRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonceFreeze
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

/-- **`NoteSpendRowIntent env`** — the intended noteSpend move on the row `env.loc`: every state-block
column UNCHANGED. The nullifier-set insert + no-double-spend gate are out-of-row (the §IR flags). -/
def NoteSpendRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the freeze intent. -/

/-- **`noteSpendVm_faithful`.** On a noteSpend row, the emitted descriptor's per-row gates all hold
IFF `NoteSpendRowIntent` holds — the gates pin EXACTLY the whole-block freeze. -/
theorem noteSpendVm_faithful (env : VmRowEnv) :
    (∀ c ∈ noteSpendRowGates, c.holdsVm env false false) ↔ NoteSpendRowIntent env := by
  unfold noteSpendRowGates gFieldPassAll NoteSpendRowIntent
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

/-! ## §5 — ANTI-GHOST: a row that MUTATES any state-block cell on a noteSpend is rejected. -/

/-- **Anti-ghost (general).** A noteSpend row whose state block is NOT frozen does NOT satisfy the
per-row gates — the conservation tooth. -/
theorem noteSpendVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ NoteSpendRowIntent env) :
    ¬ (∀ c ∈ noteSpendRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((noteSpendVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A noteSpend row whose post-`bal_lo` is NOT the pre-`bal_lo`
(value forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem noteSpendVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the FROZEN cell. -/

/-- `RowEncodesSpend env pre post` ties the row's state-block columns to a `(pre, post)` cell
transition (no params — a noteSpend carries the nullifier off-block). -/
def RowEncodesSpend (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellSpendSpec pre post`** — the per-cell FULL-state noteSpend spec: the WHOLE cell state is
FROZEN. This is the EffectVM-row projection of `NoteSpendSpec`'s balance-neutrality + per-cell frame
freeze (the nullifier-set insert + no-double-spend are off-block — the §IR flags). -/
def CellSpendSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesSpend`, `NoteSpendRowIntent` IS the structured `CellSpendSpec`. -/
theorem intent_to_cellSpendSpec (env : VmRowEnv) (pre post : CellState)
    (henc : RowEncodesSpend env pre post) (hint : NoteSpendRowIntent env) :
    CellSpendSpec pre post := by
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

/-- **`noteSpendDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesSpend`, forces the structured per-cell FREEZE `CellSpendSpec` AND publishes the post-commit
as `PI[NEW_COMMIT]`. -/
theorem noteSpendDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState)
    (henc : RowEncodesSpend env pre post)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true) :
    CellSpendSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
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
  have hint := (noteSpendVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpendSpec env pre post henc hint, ?_⟩
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
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
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

/-- **`unify_spend_freeze`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`NoteSpendSpec` post-state, satisfies the keystone's `CellSpendSpec` EXACTLY: `balLo` FROZEN
(`bal' = bal`, balance-neutral); balHi/nonce/fields/capRoot/reserved frozen. So `CellSpendSpec` IS
`NoteSpendSpec`'s per-cell frame image — NOT a fourth spec. -/
theorem unify_spend_freeze (st st' : RecChainedState) (nf : Nat) (actor c : CellId)
    (asset : AssetId) (spendProof : Bool)
    (hspec : NoteSpendSpec st nf actor spendProof st') :
    CellSpendSpec (cellProjSpend st.kernel.bal c asset) (cellProjSpend st'.kernel.bal c asset) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- NoteSpendSpec: guard ∧ nullifiers ∧ log ∧ accounts ∧ cell ∧ caps ∧ escrows ∧ revoked ∧
  --               commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_spend`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed noteSpend agrees with the executor's per-cell post-state: the descriptor's
pinned (frozen) post-state equals the executor's frozen cell on every state-block column. The
nullifier-set insert + no-double-spend are out-of-IR (reported as the §IR flags). -/
theorem descriptor_agrees_with_executor_spend
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (nf : Nat) (actor c : CellId) (asset : AssetId) (spendProof : Bool)
    (pre post : CellState)
    (hpre : pre = cellProjSpend st.kernel.bal c asset)
    (henc : RowEncodesSpend env pre post)
    (hsat : satisfiedVm hash noteSpendVmDescriptor env true true)
    (hspec : NoteSpendSpec st nf actor spendProof st') :
    post.balLo = (cellProjSpend st'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjSpend st'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjSpend st'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjSpend st'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjSpend st'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := noteSpendDescriptor_full_sound hash env pre post henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ := unify_spend_freeze st st' nf actor c asset spendProof hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

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

/-! ## §12 — NON-VACUITY: a concrete frozen noteSpend row realizes the intent; a minting one rejected. -/

/-- A concrete noteSpend row: every state-block column frozen (bal_lo 100 → 100, nonce 5 → 5, frame 0). -/
def goodSpendRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_NOTE_SPEND then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodSpendRow` REALIZES the noteSpend freeze intent: every
state-block column unchanged. -/
theorem goodSpendRow_realizes_intent : NoteSpendRowIntent goodSpendRow := by
  unfold NoteSpendRowIntent goodSpendRow
  simp only [sbCol, saCol, SEL_NOTE_SPEND, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
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
    have f1 : (54 + (3 + i) = 5) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED noteSpend row: `goodSpendRow` with the post-`bal_lo` minted to `999`. -/
def badSpendRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodSpendRow.loc v
  nxt := goodSpendRow.nxt
  pub := goodSpendRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSpendRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badSpendRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badSpendRow false false := by
  apply noteSpendVm_rejects_balance_mint
  simp only [badSpendRow, goodSpendRow, sbCol, saCol, SEL_NOTE_SPEND, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
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
#assert_axioms unify_spend_freeze
#assert_axioms descriptor_agrees_with_executor_spend
#assert_axioms noteSpend_nullifier_insert_is_out_of_row
#assert_axioms noteSpend_no_double_spend_is_turn_property
#assert_axioms noteSpend_proof_gate_is_out_of_row
#assert_axioms goodSpendRow_realizes_intent
#assert_axioms badSpendRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
