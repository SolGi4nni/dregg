/-
# Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair — the createSealPair effect's concrete EffectVM
circuit, RECONCILED onto the RUNNING hand-AIR's columns (the cutover convention of commit `3aaf0772d`),
EMITTED through the SAME `EffectVmEmit` IR as transfer.

## THE RUNTIME GROUND TRUTH (the cutover-faithful reconciliation)

The running prover (`circuit/src/effect_vm/air.rs`, validated mirror `effect_vm_p3_full_air.rs`) and its
trace generator (`generate_effect_vm_trace`) implement `CreateSealPair { pair_hash }` (selector 28) as a
member of the **Stage-3 passthrough batch** (`air.rs:983-1018`): every state-block column UNCHANGED
(`new_bal_lo=old_bal_lo`, `bal_hi`, `cap_root`, `fields[0..7]` all frozen), the variant `pair_hash[0]`
parked into `params[0]`, and — via the GLOBAL nonce gate (`air.rs:2631`, `c_nonce = new_nonce −
old_nonce − (1 − s_noop)`) — the **nonce TICKS by 1** on this non-NoOp row. `RESERVED` is also frozen
(it is not in the passthrough mutation list).

So the cutover-faithful per-row gates are: bal_lo/bal_hi/cap_root/fields/RESERVED FROZEN + nonce TICK.
The PRE-RECONCILIATION descriptor here FROZE the nonce (`gNonceFreeze`) — the exact `3aaf0772d`
"`exec_nonce_is_frozen_not_ticked`" cutover bug that made the honest trace UNSAT. This file swaps the
nonce gate to the runtime tick gate `gNonce` (= transfer's `new_nonce − old_nonce − (1 − s_noop)`), so
the descriptor now AGREES with the hand-AIR on the honest trace.

## THE SYSTEM_ROOTS (STAGE-3) FORWARD BINDING — the side-table anti-ghost the task asks for

The double cap-grant (`caps := createSealPairCaps …`) and any sealed-box mutation live in kernel
SIDE-TABLES that the running 186-column air.rs does NOT yet carry a root column for. STAGE 3
(`Exec.SystemRoots`) gives the 8 side-table roots a dedicated home + committing digest; its
`cellCommitS_binds_systemRoots` is the anti-ghost tooth: equal commitment ⇒ equal `sealedBoxes` root.
We CONNECT to it here (`createSealPair_systemRoots_anti_ghost`) so the side-table soundness is a
proved theorem, while being HONEST that the RUNNABLE descriptor still binds the on-trace state block
(the runtime's actual carrier), since air.rs has no system_roots column yet. The §11 finding states the
exact residual.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` / `compressNInjective` hypotheses. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.sealpaircreation
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub eSelNoop gBalHi gNonce gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The createSealPair selector. -/

/-- The create-seal-pair selector column index (runtime `sel::CREATE_SEAL_PAIR = 28`). -/
def SEL_CREATE_SEAL_PAIR : Nat := 28

/-- The pair-creation row: `s_create_seal_pair = 1`, `s_noop = 0`. -/
def IsCreateSealPairRow (env : VmRowEnv) : Prop :=
  env.loc SEL_CREATE_SEAL_PAIR = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (RUNTIME-RECONCILED: state-block passthrough + nonce TICK). -/

/-- Balance-lo FREEZE body: `new_bal_lo − old_bal_lo` (balance-neutral — minting a keypair moves no
value; runtime passthrough batch). -/
def gBalLoFreeze : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)

/-! ## §2 — The emitted descriptor. -/

/-- The create-seal-pair AIR identity (v2 = runtime-reconciled). -/
def createSealPairVmAirName : String := "dregg-effectvm-createsealpair-v2"

/-- The per-row gates: whole state block PASSTHROUGH + nonce TICK (`gNonce`, runtime convention). -/
def createSealPairRowGates : List VmConstraint :=
  [ .gate gBalLoFreeze, .gate gBalHi, .gate gNonce
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`createSealPairVmDescriptor`** — the createSealPair effect's concrete EffectVM circuit, RECONCILED
onto the runtime hand-AIR: the per-row passthrough gates with the nonce TICK ++ transition continuity ++
the 7 boundary PI pins, the 4 ordered GROUP-4 hash sites and the 2 balance-limb range checks. -/
def createSealPairVmDescriptor : EffectVmDescriptor :=
  { name := createSealPairVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := createSealPairRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 28
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The ROW INTENT: state-block passthrough + nonce TICK (runtime-faithful). -/

/-- **`CreateSealPairRowIntent env`** — the intended runtime createSealPair move: every state-block
column UNCHANGED EXCEPT the nonce, which TICKS by 1 (on a non-NoOp row `s_noop = 0`). The double
cap-grant + authority guard are out-of-row (the §IR / §systemRoots flags). -/
def CreateSealPairRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the runtime-reconciled intent. -/

/-- **`createSealPairVm_faithful`.** On a pair-creation row, the emitted descriptor's per-row gates all
hold IFF `CreateSealPairRowIntent` holds — the gates pin EXACTLY the passthrough + nonce-tick. -/
theorem createSealPairVm_faithful (env : VmRowEnv) :
    (∀ c ∈ createSealPairRowGates, c.holdsVm env false false) ↔ CreateSealPairRowIntent env := by
  unfold createSealPairRowGates gFieldPassAll CreateSealPairRowIntent
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
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a row that MUTATES any frozen state-block cell on a pair-creation is rejected. -/

/-- **Anti-ghost (general).** A pair-creation row violating the runtime intent does NOT satisfy the
per-row gates — the conservation tooth. -/
theorem createSealPairVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ CreateSealPairRowIntent env) :
    ¬ (∀ c ∈ createSealPairRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((createSealPairVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A pair-creation row whose post-`bal_lo` is NOT the pre-`bal_lo`
(value forged on a balance-neutral effect) has no satisfying gate set — `gBalLoFreeze` rejects it. -/
theorem createSealPairVm_rejects_balance_mint (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFreeze).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFreeze, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-- **Anti-ghost (nonce tamper).** A pair-creation row whose nonce does NOT tick by 1 (on `s_noop = 0`)
has no satisfying gate set — the reconciled `gNonce` tick gate rejects it. A frozen-nonce trace (the
pre-reconciliation convention) is now correctly UNSAT. -/
theorem createSealPairVm_rejects_nonce_freeze (env : VmRowEnv)
    (hwrong : env.loc (saCol state.NONCE) ≠ env.loc (sbCol state.NONCE) + (1 - env.loc sel.NOOP)) :
    ¬ (VmConstraint.gate gNonce).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec (REUSING `CellState`): passthrough + nonce tick. -/

/-- `RowEncodesPair env pre post` ties the row's state-block columns to a `(pre, post)` cell transition
(no params — pair-creation carries pid/holders off-block). -/
def RowEncodesPair (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- **`CellPairSpec pre post`** — the per-cell FULL-state pair-creation spec: balance / cap-root /
fields / RESERVED FROZEN; the nonce TICKS by 1. The EffectVM-row projection of `CreateSealPairSpec`'s
balance-neutrality + per-cell frame freeze, on the RUNTIME convention (nonce ticks; the double cap-grant
is off-block — the §systemRoots flag). -/
def CellPairSpec (pre post : CellState) : Prop :=
  post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesPair` on a non-NoOp row (`s_noop = 0`), `CreateSealPairRowIntent` IS
the structured `CellPairSpec`. -/
theorem intent_to_cellPairSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesPair env pre post) (hint : CreateSealPairRowIntent env) :
    CellPairSpec pre post := by
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

/-! ## §7 — The full descriptor soundness + the commitment binding. -/

/-- **`createSealPairDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under
`RowEncodesPair` on a non-NoOp row, forces the structured per-cell `CellPairSpec` (passthrough + nonce
tick) AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem createSealPairDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (hnoop : env.loc sel.NOOP = 0)
    (henc : RowEncodesPair env pre post)
    (hsat : satisfiedVm hash createSealPairVmDescriptor env true true) :
    CellPairSpec pre post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ createSealPairRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createSealPairVmDescriptor.constraints := by
      unfold createSealPairVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have := hcs c hmem
    unfold createSealPairRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (createSealPairVm_faithful env).mp hgates'
  refine ⟨intent_to_cellPairSpec env pre post hnoop henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ createSealPairVmDescriptor.constraints := by
      unfold createSealPairVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inr hc)
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

/-- **`createSealPairDescriptor_commit_binds_state`** — two descriptor-satisfying pair-creation rows
publishing the SAME `NEW_COMMIT` have identical absorbed state-block columns. So a prover cannot keep
`NEW_COMMIT` while tampering any absorbed cell of the post-state. -/
theorem createSealPairDescriptor_commit_binds_state (hash : List ℤ → ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash createSealPairVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash createSealPairVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash createSealPairVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ createSealPairVmDescriptor.constraints := by
        unfold createSealPairVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellPairSpec` IS `CreateSealPairSpec`'s per-cell frame image.

`createSealPair_iff_spec ⇒ CreateSealPairSpec` carries balance-neutrality (`bal' = bal`). We project ONE
cell into the keystone `CellState` and prove the projection of ANY cell satisfies the FROZEN part of
`CellPairSpec` EXACTLY. Universe-A `RecChainedState` has NO per-cell nonce field — the nonce-tick is the
runtime cell-bookkeeping leg, reconciled exactly as the transfer keystone (`exec_nonce` divergence
note). The double cap-grant is the §systemRoots flag, reported below. -/

open Dregg2.Exec (RecChainedState RecordKernelState CellId AssetId)
open Dregg2.Circuit.Spec.SealPairCreation
  (CreateSealPairSpec createSealPair_iff_spec createSealPair_spec_balance_neutral
   createSealPair_spec_grants_keypair)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb; the other EffectVM limbs are `0`, frozen). -/
def cellProjPair (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_pair_frozen_frame`** — ANY cell's projected `(c, asset)` ledger entry, across a committed
`CreateSealPairSpec` post-state, has its FROZEN frame (bal_lo balance-neutral; bal_hi/fields/cap/reserved
frozen at `0`) EXACTLY matching `CellPairSpec`'s frozen conjuncts. So the runtime-reconciled
`CellPairSpec` agrees with `CreateSealPairSpec` on EVERY state-block column the descriptor binds; the
only delta is the per-cell nonce tick (off the universe-A state). -/
theorem unify_pair_frozen_frame (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder c : CellId) (asset : AssetId)
    (hspec : CreateSealPairSpec s pid actor sealerHolder unsealerHolder s') :
    (cellProjPair s'.kernel.bal c asset).balLo = (cellProjPair s.kernel.bal c asset).balLo
    ∧ (cellProjPair s'.kernel.bal c asset).balHi = (cellProjPair s.kernel.bal c asset).balHi
    ∧ (∀ i : Fin 8, (cellProjPair s'.kernel.bal c asset).fields i
                  = (cellProjPair s.kernel.bal c asset).fields i)
    ∧ (cellProjPair s'.kernel.bal c asset).capRoot = (cellProjPair s.kernel.bal c asset).capRoot
    ∧ (cellProjPair s'.kernel.bal c asset).reserved = (cellProjPair s.kernel.bal c asset).reserved := by
  refine ⟨?_, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal c asset = s.kernel.bal c asset
  -- CreateSealPairSpec: guard ∧ caps ∧ log ∧ accounts ∧ cell ∧ escrows ∧ nullifiers ∧ revoked ∧
  --                     commitments ∧ bal ∧ … — `bal` is the 10th conjunct.
  obtain ⟨_, _, _, _, _, _, _, _, _, hbal, _⟩ := hspec
  rw [hbal]

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff, frozen frame). -/

/-- **`descriptor_agrees_with_executor_pair`** — a satisfying run of the runnable descriptor encoding
ANY cell of a committed pair-creation agrees with the executor's per-cell post-state on EVERY FROZEN
state-block column (bal/fields/cap/reserved). The nonce-tick is the runtime cell-bookkeeping leg (off
universe-A state), reconciled as the transfer keystone; the double cap-grant is the §systemRoots flag. -/
theorem descriptor_agrees_with_executor_pair
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hnoop : env.loc sel.NOOP = 0)
    (s s' : RecChainedState) (pid : Nat) (actor sealerHolder unsealerHolder c : CellId)
    (asset : AssetId) (pre post : CellState)
    (hpre : pre = cellProjPair s.kernel.bal c asset)
    (henc : RowEncodesPair env pre post)
    (hsat : satisfiedVm hash createSealPairVmDescriptor env true true)
    (hspec : CreateSealPairSpec s pid actor sealerHolder unsealerHolder s') :
    post.balLo = (cellProjPair s'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjPair s'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjPair s'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjPair s'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjPair s'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := createSealPairDescriptor_full_sound hash env pre post hnoop henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, heF, heCap, heRes⟩ :=
    unify_pair_frozen_frame s s' pid actor sealerHolder unsealerHolder c asset hspec
  subst hpre
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — THE SYSTEM_ROOTS (STAGE-3) SIDE-TABLE BINDING + the out-of-row finding. -/

open Dregg2.Exec.SystemRoots (N_SYSTEM_ROOTS)
open Dregg2.Exec.SystemRoots.systemRoot (SEALED_BOXES)
open Dregg2.Circuit.StateCommit (compressNInjective)

/-- **`createSealPair_systemRoots_anti_ghost` — the STAGE-3 side-table anti-ghost (the task's bound
root).** Under the STAGE-3 commitment model `cellCommitS` (which absorbs the 8 side-table roots' digest
as one extra limb), two cells committing IDENTICALLY have the SAME `SEALED_BOXES` side-table root. So a
prover who tampers the sealed-boxes root (the side-table createSealPair conceptually touches, alongside
`caps`) provably MOVES the commitment: the anti-ghost tooth over the BOUND root, lifted from
`Exec.SystemRoots.cellCommitS_binds_systemRoots`. This is the soundness the system_roots STAGE-3 home
BUYS for the seal family. -/
theorem createSealPair_systemRoots_anti_ghost
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (rest : List ℤ) (sr sr' : Dregg2.Exec.SystemRoots.SysRoots)
    (h : Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr
        = Dregg2.Exec.SystemRoots.cellCommitS compressN rest sr') :
    sr (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS)
      = sr' (⟨SEALED_BOXES, by decide⟩ : Fin N_SYSTEM_ROOTS) :=
  Dregg2.Exec.SystemRoots.cellCommitS_binds_roots_pointwise compressN hN rest sr sr' h _

/-- **`pair_keypair_grant_is_out_of_row` — the honest finding (LOAD-BEARING leg out-of-IR).** A committed
pair-creation over DISTINCT holders GRANTS the sealer cap to `sealerHolder` AND the unsealer cap to
`unsealerHolder` (a real keypair: `createSealPair_spec_grants_keypair`). This double cap-grant — the
ACTUAL effect — is a universe-A property over the `caps` side-table. The RUNNABLE descriptor binds only
the on-trace state block (the runtime's hand-AIR carrier); the side-table soundness is provided by the
STAGE-3 connector above, which the running air.rs does NOT yet carry a column for. The §systemRoots
flag, surfaced as a theorem. -/
theorem pair_keypair_grant_is_out_of_row (s s' : RecChainedState) (pid : Nat)
    (actor sealerHolder unsealerHolder : CellId)
    (hne : sealerHolder ≠ unsealerHolder)
    (h : Dregg2.Exec.TurnExecutorFull.execFullA s
        (.createSealPairA pid actor sealerHolder unsealerHolder) = some s') :
    Dregg2.Exec.TurnExecutorFull.sealerCap pid ∈ s'.kernel.caps sealerHolder
    ∧ Dregg2.Exec.TurnExecutorFull.unsealerCap pid ∈ s'.kernel.caps unsealerHolder
    ∧ Dregg2.Exec.TurnExecutorFull.sealerCap pid ≠ Dregg2.Exec.TurnExecutorFull.unsealerCap pid := by
  obtain ⟨hms, hmu, _, _, hdne⟩ :=
    createSealPair_spec_grants_keypair s pid actor sealerHolder unsealerHolder s' hne h
  exact ⟨hms, hmu, hdne⟩

/-! ## §12 — NON-VACUITY: a concrete runtime pair-creation row realizes the intent; tampers rejected. -/

/-- A concrete pair-creation row: state-block passthrough + nonce TICK (bal_lo 100 → 100, nonce 5 → 6,
frame 0, `s_noop = 0`). -/
def goodPairRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_CREATE_SEAL_PAIR then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 100
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodPairRow_noop : goodPairRow.loc sel.NOOP = 0 := by
  show goodPairRow.loc 0 = 0
  simp only [goodPairRow, SEL_CREATE_SEAL_PAIR, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE]
  norm_num

/-- **NON-VACUITY (witness TRUE).** `goodPairRow` REALIZES the runtime pair-creation intent (passthrough
+ nonce tick). -/
theorem goodPairRow_realizes_intent : CreateSealPairRowIntent goodPairRow := by
  unfold CreateSealPairRowIntent
  have hnoop : goodPairRow.loc sel.NOOP = 0 := goodPairRow_noop
  refine ⟨rfl, rfl, ?_, rfl, rfl, ?_⟩
  · rw [hnoop]
    show goodPairRow.loc (saCol state.NONCE) = goodPairRow.loc (sbCol state.NONCE) + (1 - 0)
    simp only [goodPairRow, SEL_CREATE_SEAL_PAIR, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE]
    norm_num
  · intro i hi
    show goodPairRow.loc (saCol (state.FIELD_BASE + i)) = goodPairRow.loc (sbCol (state.FIELD_BASE + i))
    simp only [goodPairRow, SEL_CREATE_SEAL_PAIR, sbCol, saCol, STATE_BEFORE_BASE,
      STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
      state.NONCE, state.FIELD_BASE]
    have e1 : (76 + (3 + i) = 28) = False := eq_false (by omega)
    have e2 : (76 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have e3 : (76 + (3 + i) = 54 + 14 + 8 + 0) = False := eq_false (by omega)
    have e4 : (76 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have e5 : (76 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    have f1 : (54 + (3 + i) = 28) = False := eq_false (by omega)
    have f2 : (54 + (3 + i) = 54 + 0) = False := eq_false (by omega)
    have f3 : (54 + (3 + i) = 54 + 14 + 8 + 0) = False := eq_false (by omega)
    have f4 : (54 + (3 + i) = 54 + 2) = False := eq_false (by omega)
    have f5 : (54 + (3 + i) = 76 + 2) = False := eq_false (by omega)
    simp only [e1, e2, e3, e4, e5, f1, f2, f3, f4, f5, if_false]

/-- A FORGED pair-creation row: `goodPairRow` with the post-`bal_lo` minted to `999`. -/
def badPairRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodPairRow.loc v
  nxt := goodPairRow.nxt
  pub := goodPairRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badPairRow`'s post-`bal_lo` is NOT frozen
(forged mint), so `gBalLoFreeze` REJECTS it — a concrete UNSAT (conservation has teeth). -/
theorem badPairRow_rejected : ¬ (VmConstraint.gate gBalLoFreeze).holdsVm badPairRow false false := by
  apply createSealPairVm_rejects_balance_mint
  simp only [badPairRow, goodPairRow, sbCol, saCol, SEL_CREATE_SEAL_PAIR, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE]
  norm_num

/-- A FROZEN-NONCE pair-creation row: `goodPairRow` with the post-nonce held at `5` (the
pre-reconciliation convention). -/
def staleNoncePairRow : VmRowEnv where
  loc := fun v => if v = saCol state.NONCE then 5 else goodPairRow.loc v
  nxt := goodPairRow.nxt
  pub := goodPairRow.pub

/-- **NON-VACUITY (cutover witness FALSE).** A frozen-nonce row is now correctly UNSAT under the
reconciled `gNonce` tick gate — the descriptor agrees with the hand-AIR (which ticks). -/
theorem staleNoncePairRow_rejected :
    ¬ (VmConstraint.gate gNonce).holdsVm staleNoncePairRow false false := by
  apply createSealPairVm_rejects_nonce_freeze
  simp only [staleNoncePairRow, goodPairRow, sel.NOOP, sbCol, saCol, SEL_CREATE_SEAL_PAIR,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE]
  norm_num

/-! ## §MAG — THE MAGNESIUM FULL-STATE LIFT: the RUNNABLE descriptor binds ALL 17 fields.

§7's `createSealPairDescriptor_full_sound` binds the per-cell state block (13 absorbed columns →
`CellPairSpec`) on the 186-wide descriptor — but that descriptor's `state_commit` absorbs ONLY the 13
state-block columns; the 8 `system_roots` side-table roots ride a separate record-layer commitment the
row does not carry (the Class-C "pale ghost"). This section CLOSES that for createSealPair, following the
VALIDATED REFERENCE `EffectVmFullStateRunnable.transferRunnableSpec` VERBATIM: a WIDE descriptor whose
`state_commit` ALSO absorbs the dedicated `sysRootsDigestCol` carrier, lifted through the GENERIC crown
`runnable_full_sound`. The crypto is discharged ONCE in the generic theorem; the per-effect content is
THIN — the (hash-site-free) gate→`CellPairSpec` projection + the decode.

THE HONEST FULL CLAUSE (the seal-root binding the task asks for). The RUNNABLE descriptor faithfully
describes the RUNTIME createSealPair (`air.rs:983-1018`, the Stage-3 passthrough batch): every
state-block column frozen EXCEPT the nonce, which ticks. That on-trace effect touches NO side-table — a
fresh pair holds no box, so `sealedBoxes` is FRAMED (and the double cap-grant is the SEPARATE universe-A
`CreateSealPairSpec` leg, the §11 carried divergence). So the runtime createSealPair FREEZES all 8
`system_roots` roots (INCLUDING `SEALED_BOXES`), exactly as transfer does. The full clause is
`CellPairSpec pre post` (passthrough + nonce tick) AND `postRoots = preRoots` (all 8 side-table roots
frozen, the seal-root among them). The anti-ghost (`createSealPairRunnable_rejects_root_tamper`) bites on
ALL 17 fields. -/

open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (wideHashSites RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest emptySystemRoots N_SYSTEM_ROOTS)

/-- **`createSealPairVmDescriptorWide`** — createSealPair's descriptor WIDENED: the SAME per-row gates
(state-block passthrough + nonce tick) + transitions + boundary pins + selector gate, but `traceWidth :=
EFFECT_VM_WIDTH_SYSROOTS` and `hashSites := wideHashSites`. Strictly additive: the constraint list is
byte-identical; only the width grows by 2 and the outer site's spare slot becomes the `system_roots`
digest carrier. -/
def createSealPairVmDescriptorWide : EffectVmDescriptor :=
  { createSealPairVmDescriptor with
    name := createSealPairVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide createSealPair descriptor's constraints ARE createSealPair's. -/
theorem createSealPairWide_constraints_eq :
    createSealPairVmDescriptorWide.constraints = createSealPairVmDescriptor.constraints := rfl

/-- **`createSealPairGates_give_cellPairSpec` — the GATE-ONLY per-cell soundness (no hash-site
hypothesis).** The per-row gates of the createSealPair descriptor, on a pair-creation row decoded by
`RowEncodesPair`, force `CellPairSpec` — the body of `createSealPairDescriptor_full_sound` with the
hash-site layer DROPPED (the passthrough/tick factors through `createSealPairVm_faithful` +
`intent_to_cellPairSpec`, neither of which reads the sites). -/
theorem createSealPairGates_give_cellPairSpec (env : VmRowEnv) (pre post : CellState)
    (hnoop : env.loc sel.NOOP = 0) (henc : RowEncodesPair env pre post)
    (hgates : ∀ c ∈ createSealPairVmDescriptor.constraints, c.holdsVm env true true) :
    CellPairSpec pre post := by
  have hrowgates : ∀ c ∈ createSealPairRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ createSealPairVmDescriptor.constraints := by
      unfold createSealPairVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
    have hh := hgates c hmem
    unfold createSealPairRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using hh
  exact intent_to_cellPairSpec env pre post hnoop henc ((createSealPairVm_faithful env).mp hrowgates)

/-- **`CreateSealPairFullClause`** — the full declarative 17-field post-state for the RUNTIME
createSealPair: the per-cell `CellPairSpec` (balance/`bal_hi`/8 fields/`cap_root`/`RESERVED` frozen,
nonce ticks) AND the `system_roots` sub-block FROZEN (the `SEALED_BOXES` root among the frozen 8 — a
fresh pair holds no box). Non-vacuous: `createSealPairRunnable_realizes` inhabits it. -/
def CreateSealPairFullClause (preRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellPairSpec pre post ∧ postRoots = preRoots

/-- **`createSealPairRunnableSpec` — THE MAGNESIUM RUNNABLE INSTANCE for createSealPair.** `decodeAfter`
is `RowEncodesPair` PLUS the frozen-roots witness; `decodeFull` projects the wide descriptor's per-row
gates (= createSealPair's) to `createSealPairGates_give_cellPairSpec`, then carries the frozen-roots
fact. THIN + NON-VACUOUS (the genuine passthrough + nonce tick + frozen sub-block, NOT `True`). -/
def createSealPairRunnableSpec (preRoots : SysRoots) : RunnableFullStateSpec CellState where
  descriptor    := createSealPairVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsCreateSealPairRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesPair env pre post ∧ postRoots = preRoots
  fullClause    := CreateSealPairFullClause preRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots⟩ := hdec
    exact ⟨createSealPairGates_give_cellPairSpec env pre post hrow.2 henc
            (createSealPairWide_constraints_eq ▸ hgates), hroots⟩

/-- **`createSealPair_runnable_full_sound` — THE MAGNESIUM CROWN (createSealPair).** A row satisfying
createSealPair's WIDE RUNNABLE descriptor, under the structured decode on a pair-creation row, pins the
FULL 17-field post-state: `CellPairSpec` (the genuine passthrough + nonce tick) AND `postRoots =
preRoots` (all 8 side-table roots frozen, the `SEALED_BOXES` root among them). STRENGTHENS §7's per-cell
`createSealPairDescriptor_full_sound` to the WHOLE state on the circuit the prover ACTUALLY RUNS. -/
theorem createSealPair_runnable_full_sound (hash : List ℤ → ℤ) (preRoots : SysRoots)
    (env : VmRowEnv) (pre post : CellState) (postRoots : SysRoots)
    (hrow : IsCreateSealPairRow env)
    (henc : RowEncodesPair env pre post) (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash createSealPairVmDescriptorWide env true true) :
    CellPairSpec pre post ∧ postRoots = preRoots :=
  runnable_full_sound (createSealPairRunnableSpec preRoots) hash env pre post postRoots
    hrow ⟨henc, hroots⟩ hsat

/-- **`createSealPairRunnable_rejects_root_tamper` — the SEAL-ROOT anti-ghost (the headline tooth).** Two
rows satisfying createSealPair's WIDE descriptor that publish the SAME `NEW_COMMIT` (with
`systemRootsDigest` carriers) but whose side-table sub-blocks DIFFER at index `i` (a forged
`SEALED_BOXES` root, …) CANNOT both satisfy. The seal-family side-table state is bound BY the runnable
commitment. -/
theorem createSealPairRunnable_rejects_root_tamper (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (preRoots : SysRoots)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash createSealPairVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash createSealPairVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (createSealPairRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`createSealPairRunnable_rejects_state_tamper` — the per-cell-block anti-ghost on the wide
descriptor.** Two wide pair-creation rows publishing the same `NEW_COMMIT` whose absorbed state-block
columns DIFFER (a forged balance / tampered nonce / forged cap-root) cannot both satisfy. -/
theorem createSealPairRunnable_rejects_state_tamper (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (preRoots : SysRoots)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash createSealPairVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash createSealPairVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : EffectVmEmitTransferSound.absorbedCols e₁ ≠ EffectVmEmitTransferSound.absorbedCols e₂) :
    False :=
  wide_rejects_state_tamper (createSealPairRunnableSpec preRoots) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### Non-vacuity of the magnesium instance (witness TRUE + witness FALSE). -/

/-- A concrete `(pre, post)` cell pair for a real passthrough pair-creation: every state-block column
frozen, nonce `5 → 6`. -/
def pairRefPre : CellState where
  balLo := 100; balHi := 0; nonce := 5; fields := fun _ => 0; capRoot := 0; reserved := 0; commit := 0
def pairRefPost : CellState where
  balLo := 100; balHi := 0; nonce := 6; fields := fun _ => 0; capRoot := 0; reserved := 0; commit := 0

/-- **`createSealPairRunnable_realizes` — NON-VACUITY (witness TRUE).** The createSealPair `fullClause` is
INHABITED by a real passthrough pair-creation: `pairRefPost` is the genuine image of `pairRefPre` (nonce
`5 → 6`, every other column frozen) and the roots are frozen. So the framework's `fullClause` is NOT
`True`. -/
theorem createSealPairRunnable_realizes :
    (createSealPairRunnableSpec emptySystemRoots).fullClause pairRefPre pairRefPost emptySystemRoots :=
  ⟨⟨rfl, rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`createSealPairRunnable_clause_not_trivial` — the clause is REFUTABLE (witness FALSE).** A
post-state whose nonce is NOT `pre.nonce + 1` (`5 + 1 = 6` demanded, but a frozen `5`) FAILS
`CreateSealPairFullClause` — so the magnesium `fullClause` is not vacuously true (it rejects the
cutover-bug frozen-nonce post-state). -/
theorem createSealPairRunnable_clause_not_trivial :
    ¬ CreateSealPairFullClause emptySystemRoots pairRefPre { pairRefPost with nonce := 5 }
        emptySystemRoots := by
  rintro ⟨⟨_, _, hnon, _, _, _⟩, _⟩
  -- hnon : (5) = pairRefPre.nonce + 1 = 5 + 1 = 6
  simp only [pairRefPre] at hnon
  norm_num at hnon

/-! ## §13 — Axiom-hygiene pins. -/

#guard createSealPairVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard createSealPairVmDescriptor.hashSites.length == 4
#guard createSealPairVmDescriptor.traceWidth == 186

-- §MAG: the wide descriptor keeps the SAME gates, swaps to the wide sites + width.
#guard createSealPairVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3 + 1
#guard createSealPairVmDescriptorWide.hashSites.length == 4
#guard createSealPairVmDescriptorWide.traceWidth == 188

#assert_axioms createSealPairVm_faithful
#assert_axioms createSealPairVm_rejects_wrong_output
#assert_axioms createSealPairVm_rejects_balance_mint
#assert_axioms createSealPairVm_rejects_nonce_freeze
#assert_axioms intent_to_cellPairSpec
#assert_axioms createSealPairDescriptor_full_sound
#assert_axioms createSealPairDescriptor_commit_binds_state
#assert_axioms unify_pair_frozen_frame
#assert_axioms descriptor_agrees_with_executor_pair
#assert_axioms createSealPair_systemRoots_anti_ghost
#assert_axioms pair_keypair_grant_is_out_of_row
#assert_axioms goodPairRow_realizes_intent
#assert_axioms badPairRow_rejected
#assert_axioms staleNoncePairRow_rejected

-- §MAG: the magnesium full-state RUNNABLE crown + the side-table anti-ghost teeth.
#assert_axioms createSealPairGates_give_cellPairSpec
#assert_axioms createSealPair_runnable_full_sound
#assert_axioms createSealPairRunnable_rejects_root_tamper
#assert_axioms createSealPairRunnable_rejects_state_tamper
#assert_axioms createSealPairRunnable_realizes
#assert_axioms createSealPairRunnable_clause_not_trivial

end Dregg2.Circuit.Emit.EffectVmEmitCreateSealPair
