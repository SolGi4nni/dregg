/-
# Dregg2.Circuit.Emit.EffectVmEmitCellDestroy — the `cellDestroy` effect's EffectVM-row circuit,
EMITTED, RECONCILED onto the RUNNING hand-AIR's columns (cutover convention) and GRADUATED into the
descriptor cutover (v2).

`cellDestroy` flips `cell`'s `lifecycle` SIDE-TABLE entry to `Destroyed` and binds a `deathCert` at
`cell`, BALANCE-NEUTRAL, self-targeted receipt prepended. Its FULL universe-A soundness is
`Inst.cellDestroyA.cellDestroyA_full_sound ⇒ CellDestroySpec` (the EffectCommit2-DUAL layer; all 18
components + log, with `lifecycle`/`deathCert` the two TOUCHED side-tables and the cell's economic
state literally frozen).

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation, v2)

The running prover runs `CellDestroy` (selector 47) as a member of the **Stage-3 passthrough batch**:
every state-block column UNCHANGED EXCEPT the GLOBAL nonce, which TICKS by 1 on this non-NoOp row. The
PRE-v2 descriptor FROZE the nonce AND carried NO last-row balance PI binding — so (a) the honest TICKED
trace was UNSAT and (b) the forged-`FINAL_BAL_LO` anti-ghost tooth did not bite. This v2 swaps the
nonce-freeze gate to the runtime TICK gate `gNonce` and appends `transitionAll ++ boundaryFirstPins ++
boundaryLastPins`, so the descriptor AGREES with the hand-AIR on the honest witness AND both the
forged-balance + forged-state-commit anti-ghost teeth bite (the createSealPair-v2 / transfer gauntlet).

## What the EffectVM row CAN pin (honest)

  * the cell's economic block (bal/fields/cap/reserved) is FROZEN; the nonce TICKS by 1;
  * the post-state is bound into `state_commit` (GROUP-4) and published as `NEW_COMMIT`.

## What the EffectVM row CANNOT enforce (the boundary — the WHOLE point of the effect)

  * the `lifecycle` flip to `Destroyed` — a per-cell SIDE-TABLE, NO EffectVM column;
  * the `deathCert` bind — likewise a side-table;
  * the self-targeted receipt; the self-authority + not-already-destroyed guard.

The destroy SOUNDNESS lives ONLY in `cellDestroyA_full_sound`.

## The mod-p denotation (DEBT-A Phase 0)

`VmConstraint.holdsVm` asserts `≡ 0 [ZMOD 2013265921]` (the deployed BabyBear field), NOT `= 0`
over ℤ. The ℤ-stated row intent is read back through the EXPLICIT canonicality envelope
`CellDestroyRowCanon` — every state-block cell a canonical representative in `[0, p)`, a boolean
NOOP selector, and an in-field nonce tick (the deployed range-check invariant, carried as named
hypotheses). Negative teeth prove `¬ (p ∣ residual)` under the same envelope; no tooth is dropped
or weakened.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR named hypothesis only.
Read-only imports.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.celllifecycle

namespace Dregg2.Circuit.Emit.EffectVmEmitCellDestroy

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState RowEncodes absorbedCols absorbed_determined_by_commit)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec
open Dregg2.Circuit.Spec.CellLifecycle

set_option linter.unusedVariables false

/-! ## §0 — the `cellDestroy` selector column (runtime `sel::CELL_DESTROY = 47`). -/

/-- The `cellDestroy` selector column index (runtime `sel::CELL_DESTROY = 47`). -/
def SEL_CELLDESTROY : Nat := 47

/-! ## §1 — the per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def cellDestroyRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-! ## §2 — the GROUP-4 state-commitment hash sites (reused). -/

def cellDestroyHashSites : List VmHashSite := transferHashSites

/-! ## §3 — the emitted descriptor (v2 = runtime-reconciled, last-row PI pins). -/

def cellDestroyVmAirName : String := "dregg-effectvm-celldestroy-v2"

/-- **`cellDestroyVmDescriptor`** — the `cellDestroy` EffectVM-row circuit, RECONCILED onto the runtime
hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++ the 7 boundary
PI pins (incl. the last-row `FINAL_BAL_LO`/`FINAL_BAL_HI`/`NEW_COMMIT`), the 4 ordered GROUP-4 hash
sites and the 2 balance-limb range checks. -/
def cellDestroyVmDescriptor : EffectVmDescriptor :=
  { name := cellDestroyVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 42
  , constraints := cellDestroyRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 47
  , hashSites := cellDestroyHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §4 — the ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`CellDestroyRowIntent env`** — the intended runtime cellDestroy move: every economic state-block
column UNCHANGED EXCEPT the nonce, which TICKS by 1 (on a non-NoOp row `s_noop = 0`). The lifecycle flip
+ deathCert bind + authority guard are out-of-row (the §off-row finding). -/
def CellDestroyRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- **`CellDestroyRowCanon env`** — the row's EXPLICIT canonicality envelope (the deployed
range-check / field-representative invariant, carried as named hypotheses): every state-block
cell of both windows is a canonical BabyBear representative in `[0, p)`; the NOOP selector is
boolean (GROUP-1 selector validity); and the pre-nonce tick stays in-field
(`nonce_before + 1 < p` — the per-cell sequence counter is far below `p`). Under the mod-p
`holdsVm` denotation these are exactly the hypotheses that let the ℤ-stated row intent be read
back off the field-checked gates (a `≡ 0 [ZMOD p]` residual strictly inside `(-p, p)` is `0`). -/
def CellDestroyRowCanon (env : VmRowEnv) : Prop :=
  (∀ off, off < STATE_SIZE →
      (0 ≤ env.loc (sbCol off) ∧ env.loc (sbCol off) < 2013265921)
      ∧ (0 ≤ env.loc (saCol off) ∧ env.loc (saCol off) < 2013265921))
  ∧ (env.loc sel.NOOP = 0 ∨ env.loc sel.NOOP = 1)
  ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921

/-! ## §5 — FAITHFULNESS (mod-p, under the explicit canonicality envelope). -/

theorem cellDestroyVm_faithful (env : VmRowEnv) (hcanon : CellDestroyRowCanon env) :
    (∀ c ∈ cellDestroyRowGates, c.holdsVm env false false) ↔ CellDestroyRowIntent env := by
  obtain ⟨hcells, hnoopB, hovf⟩ := hcanon
  have hnoop01 : 0 ≤ env.loc sel.NOOP ∧ env.loc sel.NOOP ≤ 1 := by
    rcases hnoopB with h | h <;> rw [h] <;> norm_num
  have hbLo := hcells state.BALANCE_LO (by norm_num [state.BALANCE_LO, STATE_SIZE])
  have hbHi := hcells state.BALANCE_HI (by norm_num [state.BALANCE_HI, STATE_SIZE])
  have hbN := hcells state.NONCE (by norm_num [state.NONCE, STATE_SIZE])
  have hbCap := hcells state.CAP_ROOT (by norm_num [state.CAP_ROOT, STATE_SIZE])
  have hbRes := hcells state.RESERVED (by norm_num [state.RESERVED, STATE_SIZE])
  unfold cellDestroyRowGates gFieldPassAll CellDestroyRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gResPass,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [Int.modEq_zero_iff_dvd] at hLo hHi hNon hCap hRes
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    intro i hi
    have hFi := hFld i hi
    have hbF := hcells (state.FIELD_BASE + i) (by simp only [state.FIELD_BASE, STATE_SIZE]; omega)
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at hFi
    rw [Int.modEq_zero_iff_dvd] at hFi
    omega
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]; omega
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [Int.modEq_zero_iff_dvd]
      have := hFld i hi
      omega

/-! ## §6 — ANTI-GHOST. -/

theorem cellDestroyVm_rejects_wrong_output (env : VmRowEnv) (hcanon : CellDestroyRowCanon env)
    (hwrong : ¬ CellDestroyRowIntent env) :
    ¬ (∀ c ∈ cellDestroyRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((cellDestroyVm_faithful env hcanon).mp h)

/-- **Anti-ghost (balance moved).** A row whose post-`bal_lo` ≠ pre-`bal_lo` fails the freeze gate — a
lifecycle flag flip cannot silently move value. Both cells canonical in `[0, p)` (the deployed
range-check invariant), so the moved-balance residual is nonzero strictly inside `(-p, p)`:
`¬ (p ∣ residual)`. -/
theorem cellDestroyVm_rejects_moved_balance (env : VmRowEnv)
    (hsa : 0 ≤ env.loc (saCol state.BALANCE_LO) ∧ env.loc (saCol state.BALANCE_LO) < 2013265921)
    (hsb : 0 ≤ env.loc (sbCol state.BALANCE_LO) ∧ env.loc (sbCol state.BALANCE_LO) < 2013265921)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  rw [Int.modEq_zero_iff_dvd]
  intro h
  exact hwrong (by omega)

/-- **Anti-ghost (nonce tamper).** A row whose nonce does NOT tick by 1 fails the reconciled `gNonce`
tick gate — a frozen-nonce trace (the pre-v2 convention) is now correctly UNSAT. Canonicality: both
nonce cells canonical, the tick in-field (`nonce_before + 1 < p`), the NOOP selector boolean — the
tampered residual lies strictly inside `(-p, p)` and is nonzero: `¬ (p ∣ residual)`. -/
theorem cellDestroyVm_rejects_nonce_freeze (env : VmRowEnv)
    (hsa : 0 ≤ env.loc (saCol state.NONCE) ∧ env.loc (saCol state.NONCE) < 2013265921)
    (hsb : 0 ≤ env.loc (sbCol state.NONCE) ∧ env.loc (sbCol state.NONCE) + 1 < 2013265921)
    (hnoopB : env.loc sel.NOOP = 0 ∨ env.loc sel.NOOP = 1)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  rw [Int.modEq_zero_iff_dvd]
  intro h
  have hnoop01 : 0 ≤ env.loc sel.NOOP ∧ env.loc sel.NOOP ≤ 1 := by
    rcases hnoopB with h' | h' <;> rw [h'] <;> norm_num
  exact hwrong (by omega)

/-! ## §7 — the commitment binding (REUSED; hash sites identical to transfer's). -/

theorem cellDestroyVm_commit_binds_block (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ cellDestroyHashSites)
    (hs₂ : siteHoldsAll hash e₂ cellDestroyHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ :=
  absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — the structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesDestroy env pre post` ties the row's state-block columns to a `(pre, post)` transition. -/
def RowEncodesDestroy (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellDestroyCellSpec pre post`** — the per-cell FULL-state cellDestroy spec: economic block FROZEN;
the nonce TICKS by 1. -/
def CellDestroyCellSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesDestroy env pre post) (hint : CellDestroyRowIntent env) :
    CellDestroyCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN, hnon, hnoop]; ring
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §9 — the full descriptor soundness + the commitment binding. -/

theorem cellDestroyDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (hcanon : CellDestroyRowCanon env)
    (hpubc : 0 ≤ env.pub pi.NEW_COMMIT ∧ env.pub pi.NEW_COMMIT < 2013265921)
    (henc : RowEncodesDestroy env pre post)
    (hgatesat : satisfiedVm hash cellDestroyVmDescriptor env true false)
    (hsat : satisfiedVm hash cellDestroyVmDescriptor env true true) :
    CellDestroyCellSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  obtain ⟨hcsT, _⟩ := hgatesat
  have hgates' : ∀ c ∈ cellDestroyRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ cellDestroyVmDescriptor.constraints := by
      unfold cellDestroyVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcsT c hmem
    unfold cellDestroyRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (cellDestroyVm_faithful env hcanon).mp hgates'
  refine ⟨intent_to_cellSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ cellDestroyVmDescriptor.constraints := by
      unfold cellDestroyVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢
        exact hh
  -- The NEW_COMMIT pin (mod-p) lifted to ℤ equality by canonicality of the commit cell + the PI.
  have hmod := (boundaryLast_pins env hlast).1
  have hdvd := Int.ModEq.dvd hmod
  have hcell := (hcanon.1 state.STATE_COMMIT (by norm_num [state.STATE_COMMIT, STATE_SIZE])).2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]
  omega

theorem cellDestroyDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hc₁ : 0 ≤ e₁.loc (saCol state.STATE_COMMIT) ∧ e₁.loc (saCol state.STATE_COMMIT) < 2013265921)
    (hc₂ : 0 ≤ e₂.loc (saCol state.STATE_COMMIT) ∧ e₂.loc (saCol state.STATE_COMMIT) < 2013265921)
    (hsat₁ : satisfiedVm hash cellDestroyVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash cellDestroyVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ cellDestroyHashSites := hsat₁.2.1
  have hs₂ : siteHoldsAll hash e₂ cellDestroyHashSites := hsat₂.2.1
  -- Each satisfying env pins its commit cell to PI[NEW_COMMIT] mod p; the shared PI value then
  -- chains the two commit cells (both canonical) into ℤ equality — no PI canonicality needed.
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash cellDestroyVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) ≡ e.pub pi.NEW_COMMIT [ZMOD 2013265921] := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ cellDestroyVmDescriptor.constraints := by
        unfold cellDestroyVmDescriptor
        simp only [List.mem_append]
        exact Or.inl (Or.inr hc)
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢
          exact hh
    exact (boundaryLast_pins e hlast).1
  have h₁ := hc e₁ hsat₁
  have h₂ := hc e₂ hsat₂
  rw [hpub] at h₁
  have hdvd := Int.ModEq.dvd (h₁.trans h₂.symm)
  have hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT) := by omega
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §10 — CONNECTOR to universe-A `CellDestroySpec` via `cellProj`.

`CellDestroySpec` freezes the cell record (`s'.kernel.cell = s.kernel.cell`), so the projected economic
block is preserved across destroy — EXACTLY the row's frozen frame on the balance dimension. -/

/-- Read cell `c`'s economic block out of the real record-kernel state. -/
def cellProj (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`cellDestroy_balance_frozen` — the OVERLAP, from the executor.** A committed `cellDestroy` freezes
the cell's economic balance (the cell record is framed unchanged). -/
theorem cellDestroy_balance_frozen (s s' : RecChainedState) (actor cell : CellId) (certHash : Nat)
    (hspec : CellDestroySpec s actor cell certHash s') :
    (cellProj s'.kernel cell).balLo = (cellProj s.kernel cell).balLo := by
  obtain ⟨_, _, _, _, _, hcellmap, _⟩ := hspec
  show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
  rw [hcellmap]

/-- **`descriptor_agrees_with_executor_destroy`** — a satisfying run of the runnable descriptor encoding
the destroyed cell agrees with the executor's post-state on the FROZEN balance dimension (`balLo`); the
nonce-tick is the runtime cell-bookkeeping leg (off universe-A state). -/
theorem descriptor_agrees_with_executor_destroy
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (hcanon : CellDestroyRowCanon env)
    (hpubc : 0 ≤ env.pub pi.NEW_COMMIT ∧ env.pub pi.NEW_COMMIT < 2013265921)
    (s s' : RecChainedState) (actor cell : CellId) (certHash : Nat) (pre post : CellState)
    (hpre : pre = cellProj s.kernel cell)
    (henc : RowEncodesDestroy env pre post)
    (hgatesat : satisfiedVm hash cellDestroyVmDescriptor env true false)
    (hsat : satisfiedVm hash cellDestroyVmDescriptor env true true)
    (hspec : CellDestroySpec s actor cell certHash s') :
    post.balLo = (cellProj s'.kernel cell).balLo := by
  obtain ⟨hcirc, _⟩ :=
    cellDestroyDescriptor_full_sound hash env pre post hnoop hcanon hpubc henc hgatesat hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := cellDestroy_balance_frozen s s' actor cell certHash hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §11 — THE BOUNDARY: the lifecycle/deathCert/receipt side-effect is OFF-ROW. -/

/-- **`cellDestroy_offrow_unenforced` — the loud finding.** The frozen-frame intent is invariant under
any change OUTSIDE the economic state-block columns (modulo the `s_noop` nonce tick): two rows agreeing
on all economic columns and `s_noop` satisfy the intent equally, regardless of the (unrepresented)
lifecycle flag, death cert, or receipt. The lifecycle transition is OFF-ROW; the row CANNOT distinguish
a destroyed cell from a live one. -/
theorem cellDestroy_offrow_unenforced :
    (∀ env₁ env₂ : VmRowEnv,
      (∀ off : Nat, env₁.loc (saCol off) = env₂.loc (saCol off) ∧
                     env₁.loc (sbCol off) = env₂.loc (sbCol off)) →
      env₁.loc sel.NOOP = env₂.loc sel.NOOP →
      (CellDestroyRowIntent env₁ ↔ CellDestroyRowIntent env₂)) := by
  intro env₁ env₂ hagree hnoop
  unfold CellDestroyRowIntent
  rw [(hagree state.BALANCE_LO).1, (hagree state.BALANCE_LO).2,
      (hagree state.BALANCE_HI).1, (hagree state.BALANCE_HI).2,
      (hagree state.NONCE).1, (hagree state.NONCE).2, hnoop,
      (hagree state.CAP_ROOT).1, (hagree state.CAP_ROOT).2,
      (hagree state.RESERVED).1, (hagree state.RESERVED).2]
  constructor
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [← (hagree (state.FIELD_BASE + i)).1, ← (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩
  · rintro ⟨a, b, c, d, e, f⟩
    exact ⟨a, b, c, d, e, fun i hi => by
      rw [(hagree (state.FIELD_BASE + i)).1, (hagree (state.FIELD_BASE + i)).2]; exact f i hi⟩

/-! ## §12 — NON-VACUITY. -/

/-- A concrete cellDestroy row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6). -/
def goodDestroyRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_CELLDESTROY then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodDestroyRow_noop : goodDestroyRow.loc sel.NOOP = 0 := by
  show goodDestroyRow.loc 0 = 0
  simp only [goodDestroyRow, SEL_CELLDESTROY, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodDestroyRow` REALIZES the runtime cellDestroy intent. -/
theorem goodDestroyRow_realizes_intent : CellDestroyRowIntent goodDestroyRow := by
  unfold CellDestroyRowIntent
  have hnoop : goodDestroyRow.loc sel.NOOP = 0 := goodDestroyRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodDestroyRow.loc (saCol state.NONCE) = goodDestroyRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodDestroyRow, SEL_CELLDESTROY, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodDestroyRow.loc (saCol (state.FIELD_BASE + i)) = goodDestroyRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodDestroyRow, SEL_CELLDESTROY, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 47) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 47) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- **NON-VACUITY (canonicality witness).** The honest row satisfies the explicit canonicality
envelope — the mod-p hypotheses are jointly satisfiable, not a vacuous guard. -/
theorem goodDestroyRow_canonical : CellDestroyRowCanon goodDestroyRow := by
  refine ⟨?_, Or.inl goodDestroyRow_noop, ?_⟩
  · intro off hoff
    have hall : ∀ v, 0 ≤ goodDestroyRow.loc v ∧ goodDestroyRow.loc v < 2013265921 := by
      intro v
      simp only [goodDestroyRow]
      split_ifs <;> norm_num
    exact ⟨hall _, hall _⟩
  · show goodDestroyRow.loc (sbCol state.NONCE) + 1 < 2013265921
    simp only [goodDestroyRow, SEL_CELLDESTROY, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num

/-- A FORGED cellDestroy row: `goodDestroyRow` with the post-`bal_lo` minted to `999`. -/
def badDestroyRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodDestroyRow.loc v
  nxt := goodDestroyRow.nxt
  pub := goodDestroyRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badDestroyRow`'s post-`bal_lo` is forged, so
`gBalLoFreeze` REJECTS it. -/
theorem badDestroyRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badDestroyRow false false := by
  apply cellDestroyVm_rejects_moved_balance <;>
    · simp only [badDestroyRow, goodDestroyRow, sbCol, saCol, SEL_CELLDESTROY, STATE_BEFORE_BASE,
        STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
        state.NONCE]
      norm_num

/-- A FROZEN-NONCE cellDestroy row: `goodDestroyRow` with the post-nonce held at `5`. -/
def staleNonceDestroyRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodDestroyRow.loc v
  nxt := goodDestroyRow.nxt
  pub := goodDestroyRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate. -/
theorem staleNonceDestroyRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceDestroyRow false false := by
  apply cellDestroyVm_rejects_nonce_freeze
  · simp only [staleNonceDestroyRow, goodDestroyRow, sbCol, saCol, SEL_CELLDESTROY,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · simp only [staleNonceDestroyRow, goodDestroyRow, sbCol, saCol, SEL_CELLDESTROY,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · left
    simp only [staleNonceDestroyRow, goodDestroyRow, sel.NOOP, sbCol, saCol, SEL_CELLDESTROY,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num
  · simp only [staleNonceDestroyRow, goodDestroyRow, sel.NOOP, sbCol, saCol, SEL_CELLDESTROY,
      STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
      state.BALANCE_LO, state.NONCE]
    norm_num

/-! ## §13 — axiom-hygiene tripwires. -/

#guard cellDestroyVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard cellDestroyVmDescriptor.hashSites.length == 4
#guard cellDestroyVmDescriptor.traceWidth == 188

#assert_axioms cellDestroyVm_faithful
#assert_axioms cellDestroyVm_rejects_wrong_output
#assert_axioms cellDestroyVm_rejects_moved_balance
#assert_axioms cellDestroyVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSpec
#assert_axioms cellDestroyDescriptor_full_sound
#assert_axioms cellDestroyDescriptor_commit_binds_state
#assert_axioms cellDestroy_balance_frozen
#assert_axioms descriptor_agrees_with_executor_destroy
#assert_axioms cellDestroy_offrow_unenforced
#assert_axioms goodDestroyRow_realizes_intent
#assert_axioms goodDestroyRow_canonical
#assert_axioms badDestroyRow_rejected
#assert_axioms staleNonceDestroyRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitCellDestroy
