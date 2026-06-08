/-
# Dregg2.Circuit.Emit.EffectVmEmitSeal — the seal effect's concrete EffectVM circuit, RECONCILED onto
the RUNNING hand-AIR's columns (the cutover convention of commit `3aaf0772d`), EMITTED through the SAME
`EffectVmEmit` IR as transfer.

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation)

The running prover (`circuit/src/effect_vm/air.rs:1388-1432`, validated mirror
`effect_vm_p3_full_air.rs`) and trace generator (`generate_effect_vm_trace`, `trace.rs:781-793`)
implement `Seal { field_idx }` (selector 10) as a SEALED-FIELD-MASK lock, NOT a cap-into-box prepend:

  * `bal_lo`, `bal_hi`, `cap_root`, `fields[0..7]` FROZEN (`c_seal_bal_lo/hi/cap` + the 8 field gates);
  * **`RESERVED` GAINS the bit `2^field_idx`** — the sealed-field mask occupies the low 8 bits of the
    `RESERVED` state column (`air.rs:1411-1413`: `c_seal_reserved = s_seal · (new_reserved −
    old_reserved − seal_pow2)`), with the witness `seal_pow2 := aux[SEAL_POW2_IDX]` (`aux_off=7`);
  * the GLOBAL nonce gate (`air.rs:2631`) TICKS the nonce by 1 on this non-NoOp row.

So `RESERVED` is the seal family's GENUINE on-trace side-table carrier — the sealed-field mask lives
THERE, bound by the per-row reserved-delta gate. The PRE-RECONCILIATION descriptor here modelled a
DIFFERENT effect (a `⟨pid, actor, payload⟩` cap-into-box prepend, the universe-A `SealSpec`) and FROZE
BOTH `RESERVED` and the nonce — doubly UNSAT against the honest hand-AIR trace (the `3aaf0772d`
"`exec_nonce_is_frozen_not_ticked`" + wrong-column bug). This file reconciles onto the runtime: the
reserved mask-set gate + nonce tick + balance/cap/fields freeze, so the descriptor AGREES with the
hand-AIR on the honest trace.

## TWO SEAL MODELS (the honest divergence, reported not papered)

The runtime hand-AIR seals a FIELD via the RESERVED mask. The universe-A Lean `SealSpec` (a SEPARATE
modelled effect) prepends a CAPABILITY box into the `sealedBoxes` side-table. These are GENUINELY
DIFFERENT effects sharing a name (cf. the notes divergence of `3aaf0772d`). This descriptor faithfully
describes the RUNTIME (so the cutover differential agrees). The §11 STAGE-3 connector binds the
`sealedBoxes` system-root anti-ghost for the box model; the §10 connector handles the runtime
field-mask model's RESERVED transition.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` / `compressNInjective` hypotheses. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealboxoperations
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitSeal

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

/-! ## §0 — The seal selector + the runtime mask-witness aux column. -/

/-- The seal selector column index (runtime `sel::SEAL = 10`). -/
def SEL_SEAL : Nat := 10

/-- The runtime mask-witness aux offset (`aux_off::SEAL_POW2_IDX = 7`): the column carrying
`2^field_idx` for the RESERVED mask-set delta. -/
def SEAL_POW2_IDX : Nat := 7

/-- The seal row: `s_seal = 1`, `s_noop = 0`. -/
def IsSealRow (env : VmRowEnv) : Prop :=
  env.loc SEL_SEAL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (RUNTIME-RECONCILED: balance/cap/fields freeze + RESERVED mask-set
+ nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — sealing a field moves no
value; runtime `c_seal_bal_lo`). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-- **`gReservedSealSet`** — the runtime RESERVED mask-SET gate (`air.rs:1411-1413`):
`new_reserved − old_reserved − aux[SEAL_POW2_IDX]`. On a seal row this forces `RESERVED` to GAIN the
sealed-field bit `2^field_idx` carried by the aux witness. The honest on-trace seal side-table edit. -/
def gReservedSealSet : EmittedExpr :=
  eSub (eSub (eSA state.RESERVED) (eSB state.RESERVED)) (.var (auxCol SEAL_POW2_IDX))

/-! ## §2 — The emitted descriptor. -/

/-- The seal AIR identity (v2 = runtime-reconciled field-mask model). -/
def sealVmAirName : String := "dregg-effectvm-seal-v2"

/-- The per-row gates: balance/cap/fields FROZEN + RESERVED mask-SET + nonce TICK (runtime
convention). -/
def sealRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gReservedSealSet ] ++ gFieldPassAll

/-- **`sealVmDescriptor`** — the seal effect's concrete EffectVM circuit, RECONCILED onto the runtime
hand-AIR: balance/cap/fields freeze + RESERVED mask-set + nonce tick ++ transition continuity ++ the 7
boundary PI pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def sealVmDescriptor : EffectVmDescriptor :=
  { name := sealVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := sealRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: balance/cap/fields freeze + RESERVED mask-set + nonce tick. -/

/-- **`SealRowIntent env`** — the intended runtime seal move: balance/cap/fields UNCHANGED; `RESERVED`
gains the aux-witnessed `2^field_idx` bit; the nonce TICKS by 1 (on `s_noop = 0`). The box-store /
held-cap guard are out-of-row (the §systemRoots flag). -/
def SealRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED) + env.loc (auxCol SEAL_POW2_IDX)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

/-- **`sealVm_faithful`.** On a seal row, the emitted descriptor's per-row gates all hold IFF
`SealRowIntent` holds — the gates pin EXACTLY balance/cap/fields freeze + RESERVED mask-set + nonce
tick. -/
theorem sealVm_faithful (env : VmRowEnv) :
    (∀ c ∈ sealRowGates, c.holdsVm env false false) ↔ SealRowIntent env := by
  unfold sealRowGates gFieldPassAll SealRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoFreeze) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonce) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gReservedSealSet) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoFreeze, gBalHi, gNonce, gCapPass, gReservedSealSet,
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
    · simp only [VmConstraint.holdsVm, gReservedSealSet, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: rows tampering balance, the RESERVED mask, or the nonce are rejected. -/

/-- **Anti-ghost (general).** A seal row violating the runtime intent does NOT satisfy the per-row
gates — the conservation + mask-fidelity tooth. -/
theorem sealVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SealRowIntent env) :
    ¬ (∀ c ∈ sealRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((sealVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A seal row whose post-`bal_lo` is NOT the pre-`bal_lo` (value
forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem sealVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (RESERVED mask forgery).** A seal row whose post-`RESERVED` does NOT equal
`old_reserved + seal_pow2` (a forged mask transition: sealing a bit the witness does not match, or not
setting the bit at all) has no satisfying gate set — `gReservedSealSet` rejects it. This is the
mask-fidelity tooth: the seal MUST set EXACTLY the witnessed `2^field_idx` bit. -/
theorem sealVm_rejects_reserved_forgery (env : VmRowEnv)
    (hwrong : env.loc (saCol state.RESERVED)
            ≠ env.loc (sbCol state.RESERVED) + env.loc (auxCol SEAL_POW2_IDX)) :
    ¬ (VmConstraint.gate gReservedSealSet).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gReservedSealSet, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (nonce tamper).** A seal row whose nonce does NOT tick by 1 (on `s_noop = 0`) has no
satisfying gate set — the reconciled `gNonce` tick gate rejects it. A frozen-nonce trace (the
pre-reconciliation convention) is now correctly UNSAT. -/
theorem sealVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): the runtime field-mask seal. -/

/-- `RowEncodesSeal env pre post pow2` ties the row's state-block columns + the aux mask witness to a
`(pre, post)` cell transition. -/
def RowEncodesSeal (env : VmRowEnv) (pre post : CellState) (pow2 : ℤ) : Prop :=
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

/-- **`CellSealSpec pre post pow2`** — the per-cell FULL-state seal spec: balance / cap-root / fields
FROZEN; the nonce TICKS by 1; `RESERVED` GAINS the mask bit `pow2`. The EffectVM-row projection of the
RUNTIME field-mask seal. -/
def CellSealSpec (pre post : CellState) (pow2 : ℤ) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved + pow2

/-- Decode lemma: under `RowEncodesSeal` on a non-NoOp row, `SealRowIntent` IS the structured
`CellSealSpec`. -/
theorem intent_to_cellSealSpec (env : VmRowEnv) (pre post : CellState) (pow2 : ℤ)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesSeal env pre post pow2) (hint : SealRowIntent env) :
    CellSealSpec pre post pow2 := by
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

/-- **`sealDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under `RowEncodesSeal`
on a non-NoOp row, forces the structured `CellSealSpec` (freeze + nonce tick + RESERVED mask-set) AND
publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem sealDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (pow2 : ℤ) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesSeal env pre post pow2)
    (hsat : satisfiedVm hash sealVmDescriptor env true true) :
    CellSealSpec pre post pow2 ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ sealRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ sealVmDescriptor.constraints := by
      unfold sealVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold sealRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (sealVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSealSpec env pre post pow2 hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ sealVmDescriptor.constraints := by
      unfold sealVmDescriptor
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

/-- **`sealDescriptor_commit_binds_state`** — two descriptor-satisfying seal rows publishing the SAME
`NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep `NEW_COMMIT` while
tampering any absorbed cell of the post-state. -/
theorem sealDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash sealVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash sealVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash sealVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ sealVmDescriptor.constraints := by
        unfold sealVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A (the box model): balance neutrality of `SealSpec`.

The runtime descriptor models the FIELD-MASK seal. The universe-A `SealSpec` models the SEPARATE
cap-into-box seal. They reconcile on the SHARED invariant both enforce: BALANCE-NEUTRALITY (`bal' =
bal`). We project ONE cell and prove the universe-A box-seal is balance-neutral on every projected cell,
matching the descriptor's balance-freeze gates. The runtime nonce-tick + RESERVED mask are
runtime-specific (off the universe-A `RecChainedState`); the box prepend is the §systemRoots flag. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Authority (Cap)
open Dregg2.Circuit.Spec.SealBoxOperations
  (SealSpec execFullA_seal_iff_spec sealedBoxPrepend seal_box_binds_payload)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`. -/
def cellProjSeal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_seal_balance_neutral`** — ANY cell's projected `(c, asset)` ledger entry, across a
committed (universe-A box-model) `SealSpec` post-state, has its `balLo` FROZEN (`bal' = bal`) — the
shared balance-neutrality the descriptor's balance-freeze gates also enforce. The two seal models AGREE
on balance neutrality (the cross-model invariant); the field-mask / box prepend differ by design. -/
theorem unify_seal_balance_neutral (st st' : RecChainedState) (pid : Nat) (actor c : CellId)
    (payload : Cap) (asset : AssetId) (hspec : SealSpec st pid actor payload st') :
    (cellProjSeal st'.kernel.bal c asset).balLo = (cellProjSeal st.kernel.bal c asset).balLo := by
  show st'.kernel.bal c asset = st.kernel.bal c asset
  -- SealSpec: guard ∧ sealedBoxes ∧ log ∧ accounts ∧ cell ∧ caps ∧ escrows ∧ nullifiers ∧ revoked ∧
  --           commitments ∧ bal ∧ … — `bal` is the 11th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor balance AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_seal_balance`** — a satisfying run of the runnable descriptor
encoding ANY cell of a committed (box-model) seal agrees with the executor's per-cell post-balance: the
descriptor's pinned (frozen) post-`balLo` equals the executor's frozen cell balance. The field-mask /
nonce-tick are runtime-specific; the box prepend is the §systemRoots flag. -/
theorem descriptor_agrees_with_executor_seal_balance
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (st st' : RecChainedState) (pid : Nat) (actor c : CellId) (payload : Cap) (asset : AssetId)
    (pre post : CellState) (pow2 : ℤ)
    (hpre : pre = cellProjSeal st.kernel.bal c asset)
    (henc : RowEncodesSeal env pre post pow2)
    (hsat : satisfiedVm hash sealVmDescriptor env true true)
    (hspec : SealSpec st pid actor payload st') :
    post.balLo = (cellProjSeal st'.kernel.bal c asset).balLo := by
  obtain ⟨hcirc, _⟩ := sealDescriptor_full_sound hash env pre post pow2 hnoop henc hsat
  obtain ⟨hcLo, _, _, _, _, _⟩ := hcirc
  have heLo := unify_seal_balance_neutral st st' pid actor c payload asset hspec
  subst hpre
  rw [hcLo, heLo]

/-! ## §11 — THE SYSTEM_ROOTS (STAGE-3) SIDE-TABLE BINDING + the out-of-row finding. -/

/-- **`seal_systemRoots_anti_ghost` — the STAGE-3 side-table anti-ghost (the task's bound root).** Under
the STAGE-3 commitment model `cellCommitS` (which absorbs the 8 side-table roots' digest as one extra
limb), two cells committing IDENTICALLY have the SAME `SEALED_BOXES` side-table root. So a prover who
tampers the sealed-boxes root (the side-table the box-model seal touches) provably MOVES the commitment:
the anti-ghost tooth over the BOUND root, lifted from `Exec.SystemRoots.cellCommitS_binds_systemRoots`.
This is the soundness the system_roots STAGE-3 home BUYS for the seal family. -/
theorem seal_systemRoots_anti_ghost
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (rest : List ℤ) (sr sr' : Dregg2.Exec.SystemRoots.SysRoots)
    (h : Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr
        = Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr') :
    sr (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS)
      = sr' (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS) :=
  Dregg2.Exec.SystemRoots.cellCommitS_binds_roots_pointwise compressN hN rest sr sr' h _

/-- **`seal_box_prepend_is_out_of_row` — the honest finding (the box-model leg out-of-IR).** A committed
(universe-A) box-model seal's `sealedBoxes` store gains the box `⟨pid, actor, payload⟩` at its head
(`seal_box_binds_payload`). This box prepend — the box model's ACTUAL effect — is a universe-A property
over the `sealedBoxes` side-table. The RUNNABLE descriptor binds the on-trace state block (the runtime's
field-mask carrier); the side-table soundness is provided by the STAGE-3 connector above, which the
running air.rs does NOT yet carry a column for. The §systemRoots flag, surfaced as a theorem. -/
theorem seal_box_prepend_is_out_of_row (st st' : RecChainedState) (pid : Nat) (actor : CellId)
    (payload : Cap) (hspec : SealSpec st pid actor payload st') :
    st'.kernel.sealedBoxes.head? = some { pairId := pid, sealer := actor, payload := payload } :=
  seal_box_binds_payload st pid actor payload st' hspec

/-! ## §12 — NON-VACUITY: a concrete runtime seal row realizes the intent; tampers rejected. -/

/-- A concrete seal row: balance/cap/fields frozen, nonce 5 → 6, RESERVED 0 → 4 with aux mask witness
`pow2 = 4` (i.e. sealing field_idx 2: `2^2 = 4`), `s_noop = 0`. -/
def goodSealRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_SEAL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = saCol state.RESERVED then 4
    else if v = auxCol SEAL_POW2_IDX then 4
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodSealRow_noop : goodSealRow.loc sel.NOOP = 0 := by
  show goodSealRow.loc 0 = 0
  unfold goodSealRow
  norm_num [SEL_SEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, state.RESERVED]

/-- **NON-VACUITY (witness TRUE).** `goodSealRow` REALIZES the runtime seal intent (freeze + nonce tick
+ RESERVED mask-set by the aux pow2). -/
theorem goodSealRow_realizes_intent : SealRowIntent goodSealRow := by
  unfold SealRowIntent
  have hnoop : goodSealRow.loc sel.NOOP = 0 := goodSealRow_noop
  refine ⟨rfl, rfl, ?_, rfl, ?_, ?_⟩
  · rw [hnoop]
    show goodSealRow.loc (saCol state.NONCE) = goodSealRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodSealRow, SEL_SEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED]
    norm_num
  · show goodSealRow.loc (saCol state.RESERVED)
        = goodSealRow.loc (sbCol state.RESERVED) + goodSealRow.loc (auxCol SEAL_POW2_IDX)
    simp only [goodSealRow, SEL_SEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED]
    norm_num
  · intro i hi
    show goodSealRow.loc (saCol (state.FIELD_BASE + i)) = goodSealRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodSealRow, SEL_SEAL, SEAL_POW2_IDX, sbCol, saCol, auxCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.RESERVED, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 10) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have e6 : (76 + (3 + i) = 76 + 13) = False := eq_false (by omega)
    have e7 : (76 + (3 + i) = 54 + 14 + 8 + 14 + 7) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 10) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 76 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f6 : (54 + (3 + i) = 76 + 13) = False := eq_false (by omega)
    have f7 : (54 + (3 + i) = 54 + 14 + 8 + 14 + 7) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, e6, e7, f1, f2, f3, f4, f5, f6, f7, if_false]

/-- A FORGED seal row: `goodSealRow` with the post-`bal_lo` minted to `999`. -/
def badSealRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodSealRow.loc v
  nxt := goodSealRow.nxt
  pub := goodSealRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSealRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badSealRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badSealRow false false := by
  apply sealVm_rejects_balance_mint
  simp only [badSealRow, goodSealRow, sbCol, saCol, SEL_SEAL, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FORGED-MASK seal row: `goodSealRow` with post-`RESERVED` NOT matching `old + pow2` (mask forgery:
sets the wrong/no bit while claiming the aux witness). -/
def maskForgedSealRow : VmRowEnv where
  loc := fun v => if v = saCol state.RESERVED then 99 else goodSealRow.loc v
  nxt := goodSealRow.nxt
  pub := goodSealRow.pub

/-- **NON-VACUITY (mask anti-ghost).** `maskForgedSealRow`'s post-`RESERVED` (99) ≠ `old (0) + pow2 (4)`,
so `gReservedSealSet` REJECTS it — the mask-fidelity tooth has teeth. -/
theorem maskForgedSealRow_rejected :
    ¬ (VmConstraint.gate gReservedSealSet).holdsVm maskForgedSealRow false false := by
  apply sealVm_rejects_reserved_forgery
  simp only [maskForgedSealRow, goodSealRow, sbCol, saCol, auxCol, SEL_SEAL, SEAL_POW2_IDX,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE, state.RESERVED]
  norm_num

/-- A FROZEN-NONCE seal row: `goodSealRow` with post-nonce held at `5` (pre-reconciliation convention). -/
def staleNonceSealRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodSealRow.loc v
  nxt := goodSealRow.nxt
  pub := goodSealRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate — the descriptor agrees with the hand-AIR (which ticks). -/
theorem staleNonceSealRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNonceSealRow false false := by
  apply sealVm_rejects_nonce_freeze
  simp only [staleNonceSealRow, goodSealRow, sel.NOOP, sbCol, saCol, auxCol, SEL_SEAL,
    SEAL_POW2_IDX, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, AUX_BASE, NUM_EFFECTS,
    STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, state.RESERVED]
  norm_num

/-! ## §13 — Axiom-hygiene pins. -/

#guard sealVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard sealVmDescriptor.hashSites.length == 4
#guard sealVmDescriptor.traceWidth == 186

#assert_axioms sealVm_faithful
#assert_axioms sealVm_rejects_wrong_output
#assert_axioms sealVm_rejects_balance_mint
#assert_axioms sealVm_rejects_reserved_forgery
#assert_axioms sealVm_rejects_nonce_freeze
#assert_axioms intent_to_cellSealSpec
#assert_axioms sealDescriptor_full_sound
#assert_axioms sealDescriptor_commit_binds_state
#assert_axioms unify_seal_balance_neutral
#assert_axioms descriptor_agrees_with_executor_seal_balance
#assert_axioms seal_systemRoots_anti_ghost
#assert_axioms seal_box_prepend_is_out_of_row
#assert_axioms goodSealRow_realizes_intent
#assert_axioms badSealRow_rejected
#assert_axioms maskForgedSealRow_rejected
#assert_axioms staleNonceSealRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSeal
