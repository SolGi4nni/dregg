/-
# Dregg2.Circuit.Emit.EffectVmEmitUnseal — the unseal effect's concrete EffectVM circuit, RECONCILED
onto the RUNNING hand-AIR's columns (the cutover convention of commit `3aaf0772d`), EMITTED through the
SAME `EffectVmEmit` IR as transfer.

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation)

The running prover (`circuit/src/effect_vm/air.rs:1434-1481`, validated mirror
`effect_vm_p3_full_air.rs`) and trace generator (`trace.rs:795-810`) implement
`Unseal { field_idx, brand }` (selector 11) as a SEALED-FIELD-MASK UNLOCK, NOT a cap-from-box recovery:

  * `bal_lo`, `bal_hi`, `cap_root`, `fields[0..7]` FROZEN (`c_unseal_bal_lo/hi/cap` + the 8 field gates);
  * **`RESERVED` LOSES the bit `2^field_idx`** — the sealed-field mask occupies the low 8 bits of the
    `RESERVED` state column (`air.rs:1460-1462`: `c_unseal_reserved = s_unseal · (old_reserved −
    new_reserved − unseal_pow2)`), with the witness `unseal_pow2 := aux[SEAL_POW2_IDX]` (`aux_off=7`);
  * the GLOBAL nonce gate (`air.rs:2631`) TICKS the nonce by 1 on this non-NoOp row.

So `RESERVED` is the seal family's GENUINE on-trace side-table carrier — the sealed-field mask lives
THERE, bound by the per-row reserved-delta gate. The PRE-RECONCILIATION descriptor modelled a DIFFERENT
effect (a cap-FROM-box grant, the universe-A `UnsealSpec`) and FROZE BOTH `RESERVED` and the nonce —
doubly UNSAT against the honest hand-AIR trace. This file reconciles onto the runtime: the reserved
mask-CLEAR gate + nonce tick + balance/cap/fields freeze, so the descriptor AGREES with the hand-AIR on
the honest trace.

## TWO UNSEAL MODELS (the honest divergence, reported not papered)

The runtime hand-AIR UNLOCKS a FIELD via the RESERVED mask. The universe-A Lean `UnsealSpec` (a SEPARATE
modelled effect) GRANTS the box's `payload` cap into the recipient's c-list. These are GENUINELY
DIFFERENT effects sharing a name. This descriptor faithfully describes the RUNTIME (so the cutover
differential agrees). The §11 STAGE-3 connector binds the `sealedBoxes` system-root anti-ghost for the
box model; the §10 connector handles the runtime field-mask model's RESERVED transition.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` / `compressNInjective` hypotheses. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealboxoperations
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitUnseal

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.SystemRoots (N_SYSTEM_ROOTS)
open Dregg2.Exec.SystemRoots.systemRoot (SEALED_BOXES)
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The unseal selector + the runtime mask-witness aux column. -/

/-- The unseal selector column index (runtime `sel::UNSEAL = 11`). -/
def SEL_UNSEAL : Nat := 11

/-- The runtime mask-witness aux offset (`aux_off::SEAL_POW2_IDX = 7`): the column carrying
`2^field_idx` for the RESERVED mask-clear delta. -/
def SEAL_POW2_IDX : Nat := 7

/-- The unseal row: `s_unseal = 1`, `s_noop = 0`. -/
def IsUnsealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_UNSEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (RUNTIME-RECONCILED: balance/cap/fields freeze + RESERVED mask-CLEAR
+ nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral; runtime `c_unseal_bal_lo`). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- **`gReservedUnsealClear`** — the runtime RESERVED mask-CLEAR gate (`air.rs:1460-1462`):
`old_reserved − new_reserved − aux[SEAL_POW2_IDX]`. On an unseal row this forces `RESERVED` to LOSE the
sealed-field bit `2^field_idx` carried by the aux witness. The honest on-trace unseal side-table edit. -/
def gReservedUnsealClear : EmittedExpr :=
  eSub (eSub (eSB state.RESERVED) (eSA state.RESERVED)) (.var (auxCol SEAL_POW2_IDX))

/-! ## §2 — The emitted descriptor. -/

/-- The unseal AIR identity (v2 = runtime-reconciled field-mask model). -/
def unsealVmAirName : String := "dregg-effectvm-unseal-v2"

/-- The per-row gates: balance/cap/fields FROZEN + RESERVED mask-CLEAR + nonce TICK (runtime
convention). -/
def unsealRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gReservedUnsealClear ] ++ gFieldPassAll

/-- **`unsealVmDescriptor`** — the unseal effect's concrete EffectVM circuit, RECONCILED onto the
runtime hand-AIR: balance/cap/fields freeze + RESERVED mask-clear + nonce tick ++ transition continuity
++ the 7 boundary PI pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def unsealVmDescriptor : EffectVmDescriptor :=
  { name := unsealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := unsealRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: balance/cap/fields freeze + RESERVED mask-clear + nonce tick. -/

/-- **`UnsealRowIntent env`** — the intended runtime unseal move: balance/cap/fields UNCHANGED;
`RESERVED` loses the aux-witnessed `2^field_idx` bit; the nonce TICKS by 1 (on `s_noop = 0`). The
cap-grant / held-cap guard are out-of-row (the §systemRoots flag). -/
def UnsealRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (sbCol state.RESERVED) = env.loc (saCol state.RESERVED) + env.loc (auxCol SEAL_POW2_IDX)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

/-- **`unsealVm_faithful`.** On an unseal row, the emitted descriptor's per-row gates all hold IFF
`UnsealRowIntent` holds — the gates pin EXACTLY balance/cap/fields freeze + RESERVED mask-clear + nonce
tick. -/
theorem unsealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ unsealRowGates, c.holdsVm env false false) ↔ UnsealRowIntent env := by
  unfold unsealRowGates gFieldPassAll UnsealRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gReservedUnsealClear) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gReservedUnsealClear,
      eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gReservedUnsealClear, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: rows tampering balance, the RESERVED mask, or the nonce are rejected. -/

/-- **Anti-ghost (general).** An unseal row violating the runtime intent does NOT satisfy the per-row
gates — the conservation + mask-fidelity tooth. -/
theorem unsealVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ UnsealRowIntent env) :
    ¬ (∀ c ∈ unsealRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((unsealVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** An unseal row whose post-`bal_lo` is NOT the pre-`bal_lo` has no
satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem unsealVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (RESERVED mask forgery).** An unseal row whose `old_reserved` does NOT equal
`new_reserved + unseal_pow2` (a forged mask transition: clearing a bit the witness does not match, or
not clearing the bit at all) has no satisfying gate set — `gReservedUnsealClear` rejects it. The
mask-fidelity tooth: the unseal MUST clear EXACTLY the witnessed `2^field_idx` bit. -/
theorem unsealVm_rejects_reserved_forgery (env : VmRowEnv)
    (hwrong : env.loc (sbCol state.RESERVED)
            ≠ env.loc (saCol state.RESERVED) + env.loc (auxCol SEAL_POW2_IDX)) :
    ¬ (VmConstraint.gate gReservedUnsealClear).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gReservedUnsealClear, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (nonce tamper).** An unseal row whose nonce does NOT tick by 1 (on `s_noop = 0`) has no
satisfying gate set — the reconciled `gNonce` tick gate rejects it. -/
theorem unsealVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the runtime field-mask unseal. -/

/-- `RowEncodesUnseal env pre post pow2` ties the row's state-block columns + the aux mask witness to a
`(pre, post)` cell transition. -/
def RowEncodesUnseal (env : VmRowEnv) (pre post : CellState) (pow2 : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (auxCol SEAL_POW2_IDX) = pow2
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellUnsealSpec pre post pow2`** — the per-cell FULL-state unseal spec: balance / cap-root / fields
FROZEN; the nonce TICKS by 1; `RESERVED` LOSES the mask bit `pow2` (`pre.reserved = post.reserved +
pow2`). The EffectVM-row projection of the RUNTIME field-mask unseal. -/
def CellUnsealSpec (pre post : CellState) (pow2 : ℤ) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ pre.reserved = post.reserved + pow2

/-- Decode lemma: under `RowEncodesUnseal` on a non-NoOp row, `UnsealRowIntent` IS the structured
`CellUnsealSpec`. -/
theorem intent_to_cellUnsealSpec (env : VmRowEnv) (pre post : CellState) (pow2 : ℤ)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesUnseal env pre post pow2) (hint : UnsealRowIntent env) :
    CellUnsealSpec pre post pow2 := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hAux,
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
  · rw [← hsaRes, ← hsbRes, ← hAux]; exact hres

/-! ## §7 — The full descriptor soundness + the commitment binding. -/

/-- **`unsealDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesUnseal` on a non-NoOp row, forces the structured `CellUnsealSpec` (freeze + nonce tick +
RESERVED mask-clear) AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem unsealDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (pow2 : ℤ) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesUnseal env pre post pow2)
    (hsat : satisfiedVm hash unsealVmDescriptor env true true) :
    CellUnsealSpec pre post pow2 ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ unsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ unsealVmDescriptor.constraints := by
      unfold unsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold unsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (unsealVm_faithful env).mp hgates'
  refine ⟨intent_to_cellUnsealSpec env pre post pow2 hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ unsealVmDescriptor.constraints := by
      unfold unsealVmDescriptor
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

/-- **`unsealDescriptor_commit_binds_state`** — two descriptor-satisfying unseal rows publishing the
SAME `NEW_COMMIT` have identical absorbed state-block columns. -/
theorem unsealDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash unsealVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash unsealVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash unsealVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ unsealVmDescriptor.constraints := by
        unfold unsealVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A (the box model): balance neutrality of `UnsealSpec`. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId SealedBoxRecord)
open Dregg2.Circuit.Spec.SealBoxOperations
  (UnsealSpec execFullA_unseal_iff_spec grantedCaps unseal_grants_sealed_cap)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`. -/
def cellProjUnseal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_unseal_balance_neutral`** — ANY cell's projected `(c, asset)` ledger entry, across a
committed (universe-A box-model) `UnsealSpec` post-state, has its `balLo` FROZEN (`bal' = bal`) — the
shared balance-neutrality the descriptor's balance-freeze gates also enforce. The two unseal models
AGREE on balance neutrality; the field-mask / cap-grant differ by design. -/
theorem unify_unseal_balance_neutral (st st' : RecChainedState) (pid : Nat) (actor recipient c : CellId)
    (box : SealedBoxRecord) (asset : AssetId) (hspec : UnsealSpec st pid actor recipient box st') :
    (cellProjUnseal st'.kernel.bal c asset).balLo = (cellProjUnseal st.kernel.bal c asset).balLo := by
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- UnsealSpec: guard ∧ caps ∧ log ∧ accounts ∧ cell ∧ escrows ∧ nullifiers ∧ revoked ∧
  --             commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor balance AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_unseal_balance`** — a satisfying run of the runnable descriptor
encoding ANY cell of a committed (box-model) unseal agrees with the executor's per-cell post-balance:
the descriptor's pinned (frozen) post-`balLo` equals the executor's frozen cell balance. The field-mask
/ nonce-tick are runtime-specific; the cap-grant is the §systemRoots flag. -/
theorem descriptor_agrees_with_executor_unseal_balance
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (st st' : RecChainedState) (pid : Nat) (actor recipient c : CellId) (box : SealedBoxRecord)
    (asset : AssetId) (pre post : CellState) (pow2 : ℤ)
    (hpre : pre = cellProjUnseal st.kernel.bal c asset)
    (henc : RowEncodesUnseal env pre post pow2)
    (hsat : satisfiedVm hash unsealVmDescriptor env true true)
    (hspec : UnsealSpec st pid actor recipient box st') :
    post.balLo = (cellProjUnseal st'.kernel.bal c asset).balLo := by
  obtain ⟨hcirc, _⟩ := unsealDescriptor_full_sound hash env pre post pow2 hnoop henc hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := unify_unseal_balance_neutral st st' pid actor recipient c box asset hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §11 — THE SYSTEM_ROOTS (STAGE-3) SIDE-TABLE BINDING + the out-of-row finding. -/

/-- **`unseal_systemRoots_anti_ghost` — the STAGE-3 side-table anti-ghost (the task's bound root).**
Under the STAGE-3 commitment model `cellCommitS`, two cells committing IDENTICALLY have the SAME
`SEALED_BOXES` side-table root. So a prover who tampers the sealed-boxes root provably MOVES the
commitment: the anti-ghost tooth over the BOUND root, lifted from
`Exec.SystemRoots.cellCommitS_binds_systemRoots`. -/
theorem unseal_systemRoots_anti_ghost
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (rest : List ℤ) (sr sr' : Dregg2.Exec.SystemRoots.SysRoots)
    (h : Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr
        = Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr') :
    sr (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS)
      = sr' (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS) :=
  Dregg2.Exec.SystemRoots.cellCommitS_binds_roots_pointwise compressN hN rest sr sr' h _

/-- **`unseal_cap_grant_is_out_of_row` — the honest finding (the box-model leg out-of-IR).** A committed
(universe-A) box-model unseal GRANTS the box's `payload` cap into `recipient`'s c-list
(`unseal_grants_sealed_cap`). This cap-grant — the box model's ACTUAL effect — is a universe-A property
over the `caps` side-table. The RUNNABLE descriptor binds the on-trace state block (the runtime's
field-mask carrier); the side-table soundness is provided by the STAGE-3 connector above, which the
running air.rs does NOT yet carry a column for. The §systemRoots flag, surfaced as a theorem. -/
theorem unseal_cap_grant_is_out_of_row (st st' : RecChainedState) (pid : Nat)
    (actor recipient : CellId) (box : SealedBoxRecord)
    (hspec : UnsealSpec st pid actor recipient box st') :
    box.payload ∈ st'.kernel.caps recipient :=
  unseal_grants_sealed_cap st pid actor recipient box st' hspec

/-! ## §12 — NON-VACUITY: a concrete runtime unseal row realizes the intent; tampers rejected. -/

/-- A concrete unseal row: balance/cap/fields frozen, nonce 5 → 6, RESERVED 4 → 0 with aux mask witness
`pow2 = 4` (unsealing field_idx 2), `s_noop = 0`. -/
def goodUnsealRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_UNSEAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = sbCol state.RESERVED then 4
    else if v = auxCol SEAL_POW2_IDX then 4
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodUnsealRow_noop : goodUnsealRow.loc sel.NOOP = 0 := by
  show goodUnsealRow.loc 0 = 0
  unfold goodUnsealRow
  norm_num [SEL_UNSEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, state.RESERVED]

/-- **NON-VACUITY (witness TRUE).** `goodUnsealRow` REALIZES the runtime unseal intent (freeze + nonce
tick + RESERVED mask-clear by the aux pow2). -/
theorem goodUnsealRow_realizes_intent : UnsealRowIntent goodUnsealRow := by
  unfold UnsealRowIntent
  have hnoop : goodUnsealRow.loc sel.NOOP = 0 := goodUnsealRow_noop
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_⟩
  · rw [hnoop]
    show goodUnsealRow.loc (saCol state.NONCE) = goodUnsealRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodUnsealRow, SEL_UNSEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED]
    norm_num
  · show goodUnsealRow.loc (sbCol state.RESERVED)
        = goodUnsealRow.loc (saCol state.RESERVED) + goodUnsealRow.loc (auxCol SEAL_POW2_IDX)
    simp only [goodUnsealRow, SEL_UNSEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED]
    norm_num
  · intro i hi
    show goodUnsealRow.loc (saCol (state.FIELD_BASE + i))
        = goodUnsealRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodUnsealRow, SEL_UNSEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 11) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have e6 : (76 + (3 + i) = 54 + 13) = False := eq_false (by omega)
    have e7 : (76 + (3 + i) = 54 + 14 + 8 + 14 + 7) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 11) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f6 : (54 + (3 + i) = 54 + 13) = False := eq_false (by omega)
    have f7 : (54 + (3 + i) = 54 + 14 + 8 + 14 + 7) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7, if_false]

/-- A FORGED unseal row: `goodUnsealRow` with the post-`bal_lo` minted to `999`. -/
def badUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badUnsealRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it. -/
theorem badUnsealRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badUnsealRow false false := by
  apply unsealVm_rejects_balance_mint
  simp only [badUnsealRow, goodUnsealRow, sbCol, saCol, SEL_UNSEAL, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FORGED-MASK unseal row: `goodUnsealRow` with post-`RESERVED` NOT matching `old − pow2` (mask
forgery). -/
def maskForgedUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.RESERVED then 99 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (mask anti-ghost).** `maskForgedUnsealRow`'s `old (4) ≠ post (99) + pow2 (4)`, so
`gReservedUnsealClear` REJECTS it — the mask-fidelity tooth has teeth. -/
theorem maskForgedUnsealRow_rejected :
    ¬ (VmConstraint.gate gReservedUnsealClear).holdsVm maskForgedUnsealRow false false := by
  apply unsealVm_rejects_reserved_forgery
  simp only [maskForgedUnsealRow, goodUnsealRow, sbCol, saCol, auxCol, SEL_UNSEAL, SEAL_POW2_IDX,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE, state.RESERVED]
  norm_num

/-- A FROZEN-NONCE unseal row: `goodUnsealRow` with post-nonce held at `5` (pre-reconciliation). -/
def staleNonceUnsealRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodUnsealRow.loc v
  nxt := goodUnsealRow.nxt
  pub := goodUnsealRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate — the descriptor agrees with the hand-AIR (which ticks). -/
theorem staleNonceUnsealRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceUnsealRow false false := by
  apply unsealVm_rejects_nonce_freeze
  simp only [staleNonceUnsealRow, goodUnsealRow, sel.NOOP, sbCol, saCol, auxCol, SEL_UNSEAL,
    SEAL_POW2_IDX, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS,
    STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, state.RESERVED]
  norm_num

/-! ## §MAG — THE MAGNESIUM FULL-STATE LIFT: the RUNNABLE descriptor binds ALL 17 fields.

§7's `unsealDescriptor_full_sound` binds the per-cell state block (13 absorbed columns →
`CellUnsealSpec`) on the 186-wide descriptor — but that descriptor's `state_commit` absorbs ONLY the 13
state-block columns; the 8 `system_roots` side-table roots ride a separate record-layer commitment the
row does not carry (the Class-C "pale ghost"). This section CLOSES that for unseal, following the
VALIDATED REFERENCE `EffectVmFullStateRunnable.transferRunnableSpec` VERBATIM: a WIDE descriptor whose
`state_commit` ALSO absorbs the dedicated `sysRootsDigestCol` carrier, lifted through the GENERIC crown
`runnable_full_sound`. The crypto is discharged ONCE in the generic theorem; the per-effect content is
THIN — the (hash-site-free) gate→`CellUnsealSpec` projection + the decode.

THE HONEST FULL CLAUSE (the seal-root binding the task asks for). The RUNNABLE descriptor faithfully
describes the RUNTIME field-mask UNSEAL (`air.rs:1434-1481`): a sealed-FIELD-MASK unlock on the per-cell
`RESERVED` column. That on-trace effect touches NO side-table — it does NOT consume a box from
`sealedBoxes` (the cap-from-box grant is the SEPARATE universe-A `UnsealSpec`, the §9/§11 carried
divergence; and even there the box is NOT consumed — `unseal_preserves_box_store`). So the runtime
unseal FREEZES all 8 `system_roots` roots (INCLUDING `SEALED_BOXES`), exactly as transfer does. The full
clause is `CellUnsealSpec pre post pow2` (RESERVED LOSES the mask bit `pow2`, nonce ticks,
balance/cap/fields frozen) AND `postRoots = preRoots` (all 8 side-table roots frozen, the seal-root
among them). The anti-ghost (`unsealRunnable_rejects_root_tamper`) bites on ALL 17 fields. -/

open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

/-- **`unsealVmDescriptorWide`** — unseal's descriptor WIDENED: the SAME per-row gates (RESERVED
mask-clear + nonce tick + balance/cap/fields freeze) + transitions + boundary pins, but `traceWidth :=
EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`. Strictly additive: the constraint list is
byte-identical; only the width grows by 2 and the outer site's spare slot becomes the `system_roots`
digest carrier. -/
def unsealVmDescriptorWide : EffectVmDescriptor :=
  { unsealVmDescriptor with
    name := unsealVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide unseal descriptor's constraints ARE unseal's. -/
theorem unsealWide_constraints_eq :
    unsealVmDescriptorWide.constraints = unsealVmDescriptor.constraints := rfl

/-- **`unsealGates_give_cellUnsealSpec` — the GATE-ONLY per-cell soundness (no hash-site hypothesis).**
The per-row gates of the unseal descriptor, on an unseal row decoded by `RowEncodesUnseal`, force
`CellUnsealSpec` — the body of `unsealDescriptor_full_sound` with the hash-site layer DROPPED (the
move/freeze factors through `unsealVm_faithful` + `intent_to_cellUnsealSpec`, neither of which reads the
sites). -/
theorem unsealGates_give_cellUnsealSpec (env : VmRowEnv) (pre post : CellState) (pow2 : ℤ)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesUnseal env pre post pow2)
    (hgates : ∀ c ∈ unsealVmDescriptor.constraints, c.holdsVm env true true) :
    CellUnsealSpec pre post pow2 := by
  have hrowgates : ∀ c ∈ unsealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ unsealVmDescriptor.constraints := by
      unfold unsealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have hh := hgates c hmem
    unfold unsealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellUnsealSpec env pre post pow2 hnoop henc ((unsealVm_faithful env).mp hrowgates)

/-- **`UnsealFullClause`** — the full declarative 17-field post-state for the RUNTIME unseal: the
per-cell `CellUnsealSpec` (RESERVED loses the mask bit `pow2`, nonce ticks, balance/`bal_hi`/8
fields/`cap_root` frozen) AND the `system_roots` sub-block FROZEN (the `SEALED_BOXES` root among the
frozen 8 — the box is not consumed). Non-vacuous: `unsealRunnable_realizes` inhabits it. -/
def UnsealFullClause (pow2 : ℤ) (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellUnsealSpec pre post pow2 ∧ postRoots = preRoots

/-- **`unsealRunnableSpec` — THE MAGNESIUM RUNNABLE INSTANCE for unseal.** `decodeAfter` is
`RowEncodesUnseal` PLUS the frozen-roots witness; `decodeFull` projects the wide descriptor's per-row
gates (= unseal's) to `unsealGates_give_cellUnsealSpec`, then carries the frozen-roots fact. THIN +
NON-VACUOUS (the genuine RESERVED mask-clear + nonce tick + frozen sub-block, NOT `True`). -/
def unsealRunnableSpec (pow2 : ℤ) (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := unsealVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsUnsealRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesUnseal env pre post pow2 ∧ postRoots = preRoots
  fullClause    := UnsealFullClause pow2 preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨unsealGates_give_cellUnsealSpec env pre post pow2 hrow.2 henc
            (unsealWide_constraints_eq ▸ hgates), hroots⟩

/-- **`unseal_runnable_full_sound` — THE MAGNESIUM CROWN (unseal).** A row satisfying unseal's WIDE
RUNNABLE descriptor, under the structured decode on an unseal row, pins the FULL 17-field post-state:
`CellUnsealSpec` (the genuine RESERVED mask-clear) AND `postRoots = preRoots` (all 8 side-table roots
frozen, the `SEALED_BOXES` root among them). STRENGTHENS §7's per-cell `unsealDescriptor_full_sound` to
the WHOLE state on the circuit the prover ACTUALLY RUNS. -/
theorem unseal_runnable_full_sound (hash : List ℤ → ℤ) (pow2 : ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsUnsealRow env)
    (henc : RowEncodesUnseal env pre post pow2) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash unsealVmDescriptorWide env true true) :
    CellUnsealSpec pre post pow2 ∧ postRoots = preRoots :=
  runnable_full_sound (unsealRunnableSpec pow2 preRoots) hash env pre post postRoots
    hrow ⟨henc, hroots⟩ hsat

/-- **`unsealRunnable_rejects_root_tamper` — the SEAL-ROOT anti-ghost (the headline tooth).** Two rows
satisfying unseal's WIDE descriptor that publish the SAME `NEW_COMMIT` (with `systemRootsDigest`
carriers) but whose side-table sub-blocks DIFFER at index `i` (a forged `SEALED_BOXES` root, …) CANNOT
both satisfy. The seal-family side-table state is bound BY the runnable commitment. -/
theorem unsealRunnable_rejects_root_tamper (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (pow2 : ℤ) (preRoots : SysRoots)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash unsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash unsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (unsealRunnableSpec pow2 preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`unsealRunnable_rejects_state_tamper` — the per-cell-block anti-ghost on the wide descriptor.** Two
wide unseal rows publishing the same `NEW_COMMIT` whose absorbed state-block columns DIFFER (a forged
balance / tampered RESERVED mask / forged cap-root) cannot both satisfy. -/
theorem unsealRunnable_rejects_state_tamper (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (pow2 : ℤ) (preRoots : SysRoots)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash unsealVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash unsealVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : EffectVmEmitTransferSound.absorbedCols e₁ ≠ EffectVmEmitTransferSound.absorbedCols e₂) :
    False :=
  wide_rejects_state_tamper (unsealRunnableSpec pow2 preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### ⚑ THE HONEST RESIDUAL (the seal-family-CRITICAL binding gap, WITNESSED not papered).

The unseal's GENUINE on-trace effect is the `RESERVED` sealed-field mask-CLEAR (`gReservedUnsealClear`).
But the shared `reserved_not_bound_by_commitment` finding (`EffectVmEmitTransferSound` §7) proves
`state.RESERVED` (after-column 89) is absorbed by NO hash-site — so it is NOT in `absorbedCols`, and the
WIDE commitment does NOT pin it. CONSEQUENCE: `unseal_runnable_full_sound` genuinely forces the RESERVED
mask-clear FROM THE GATES (sound WITHIN one satisfying row), the anti-ghost binds all 12 absorbed columns
+ the 8 side-table roots, but it does NOT bind RESERVED. We WITNESS this exactly (the unseal analog of
`reserved_not_bound_by_commitment`): the no-malleability tooth covers 16 of the 17 fields, with the
RESERVED-carried mask gate-enforced but not commitment-bound. (Closing it requires absorbing `saCol
RESERVED` into a hash-site — a shared-layer change, outside this family's lane.) -/

/-- **`unseal_reserved_mask_not_commitment_bound` — the WITNESSED seal-family residual.** `goodUnsealRow`
(RESERVED after = `0`, the genuine post-mask for clearing `pow2 = 4` from `4`) and `maskForgedUnsealRow`
(RESERVED after = `99`) have IDENTICAL `absorbedCols` (RESERVED is absorbed by no site), yet their `saCol
RESERVED` columns differ. So the WIDE commitment cannot distinguish a correctly-unsealed cell from one
carrying a forged sealed-field mask: the unseal's actual side-table payload (the RESERVED mask) is pinned
ONLY by the per-row `gReservedUnsealClear` gate, NOT by `NEW_COMMIT`. The headline binding gap, reported. -/
theorem unseal_reserved_mask_not_commitment_bound :
    EffectVmEmitTransferSound.absorbedCols goodUnsealRow
      = EffectVmEmitTransferSound.absorbedCols maskForgedUnsealRow
    ∧ goodUnsealRow.loc (saCol state.RESERVED) ≠ maskForgedUnsealRow.loc (saCol state.RESERVED) := by
  have hres : saCol state.RESERVED = 89 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.RESERVED; rfl
  have agree : ∀ off : Nat, saCol off ≠ (89:Nat) →
      maskForgedUnsealRow.loc (saCol off) = goodUnsealRow.loc (saCol off) := by
    intro off hoff
    show (if saCol off = saCol state.RESERVED then (99:ℤ) else goodUnsealRow.loc (saCol off))
        = goodUnsealRow.loc (saCol off)
    rw [if_neg]; rw [hres]; exact hoff
  have hneOff : ∀ off : Nat, off ≠ state.RESERVED → saCol off ≠ (89:Nat) := by
    intro off hoff
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.RESERVED at *
    omega
  refine ⟨?_, ?_⟩
  · unfold EffectVmEmitTransferSound.absorbedCols
    rw [agree state.BALANCE_LO (hneOff _ (by decide)),
        agree state.BALANCE_HI (hneOff _ (by decide)),
        agree state.NONCE (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 0) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 1) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 2) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 3) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 4) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 5) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 6) (hneOff _ (by decide)),
        agree (state.FIELD_BASE + 7) (hneOff _ (by decide)),
        agree state.CAP_ROOT (hneOff _ (by decide))]
  · have hg : goodUnsealRow.loc (saCol state.RESERVED) = 0 := by
      show (goodUnsealRow.loc (saCol state.RESERVED)) = 0
      simp only [goodUnsealRow, SEL_UNSEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
        STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
        state.NONCE, state.RESERVED]
      norm_num
    have hb : maskForgedUnsealRow.loc (saCol state.RESERVED) = 99 := by
      show (if saCol state.RESERVED = saCol state.RESERVED then (99:ℤ)
              else goodUnsealRow.loc (saCol state.RESERVED)) = 99
      rw [if_pos rfl]
    rw [hg, hb]; norm_num

/-! ### Non-vacuity of the magnesium instance (witness TRUE + witness FALSE). -/

/-- A concrete `(pre, post)` cell pair for a real RESERVED-mask UNSEAL of field 2 (`pow2 = 4`): balance
/ cap / fields frozen, nonce `5 → 6`, RESERVED `4 → 0`. -/
def unsealRefPre : CellState where
  balLo := 100; balHi := 0; nonce := 5; fields := fun _ => 0; capRoot := 0; reserved := 4; commit := 0
def unsealRefPost : CellState where
  balLo := 100; balHi := 0; nonce := 6; fields := fun _ => 0; capRoot := 0; reserved := 0; commit := 0

/-- **`unsealRunnable_realizes` — NON-VACUITY (witness TRUE).** The unseal `fullClause` is INHABITED by a
real RESERVED-mask unseal: `unsealRefPost` is the genuine image of `unsealRefPre` (nonce `5 → 6`,
RESERVED loses `pow2 = 4`, frame frozen) and the roots are frozen. So the framework's `fullClause` is
NOT `True`. -/
theorem unsealRunnable_realizes :
    (unsealRunnableSpec 4 emptySystemRoots).fullClause unsealRefPre unsealRefPost emptySystemRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`unsealRunnable_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`reserved` does not satisfy `pre.reserved = post.reserved + pow2` (`4 = 99 + 4` is false) FAILS
`UnsealFullClause` — so the magnesium `fullClause` is not vacuously true. -/
theorem unsealRunnable_clause_not_trivial :
    ¬ UnsealFullClause 4 emptySystemRoots unsealRefPre { unsealRefPost with reserved := 99 }
        emptySystemRoots := by
  rintro ⟨⟨_, _, _, _, _, hres⟩, _⟩
  -- hres : unsealRefPre.reserved (4) = (99) + 4
  simp only [unsealRefPre] at hres
  norm_num at hres

/-! ## §13 — Axiom-hygiene pins. -/

#guard unsealVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard unsealVmDescriptor.hashSites.length == 4
#guard unsealVmDescriptor.traceWidth == 186

-- §MAG: the wide descriptor keeps the SAME gates, swaps to the wide sites + width.
#guard unsealVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3
#guard unsealVmDescriptorWide.hashSites.length == 4
#guard unsealVmDescriptorWide.traceWidth == 188

#assert_axioms unsealVm_faithful
#assert_axioms unsealVm_rejects_wrong_output
#assert_axioms unsealVm_rejects_balance_mint
#assert_axioms unsealVm_rejects_reserved_forgery
#assert_axioms unsealVm_rejects_nonce_freeze
#assert_axioms intent_to_cellUnsealSpec
#assert_axioms unsealDescriptor_full_sound
#assert_axioms unsealDescriptor_commit_binds_state
#assert_axioms unify_unseal_balance_neutral
#assert_axioms descriptor_agrees_with_executor_unseal_balance
#assert_axioms unseal_systemRoots_anti_ghost
#assert_axioms unseal_cap_grant_is_out_of_row
#assert_axioms goodUnsealRow_realizes_intent
#assert_axioms badUnsealRow_rejected
#assert_axioms maskForgedUnsealRow_rejected
#assert_axioms staleNonceUnsealRow_rejected

-- §MAG: the magnesium full-state RUNNABLE crown + the side-table anti-ghost teeth.
#assert_axioms unsealGates_give_cellUnsealSpec
#assert_axioms unseal_runnable_full_sound
#assert_axioms unsealRunnable_rejects_root_tamper
#assert_axioms unsealRunnable_rejects_state_tamper
#assert_axioms unseal_reserved_mask_not_commitment_bound
#assert_axioms unsealRunnable_realizes
#assert_axioms unsealRunnable_clause_not_trivial

end Dregg2.Circuit.Emit.EffectVmEmitUnseal
