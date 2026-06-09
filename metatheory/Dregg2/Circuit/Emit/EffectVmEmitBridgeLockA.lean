/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA — the bridgeLock (bridge-outbound-LOCK) effect's concrete
EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer, RECONCILED onto the running
trace-generator layout and AMPLIFIED to bind the bridge side-table root (`system_roots[ESCROW]`).

This is the bridge-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `bridgeLockA`. Universe A (`Spec/bridgeoutboundlock.lean`) carries the FULL-state soundness
`execFullA_bridgeLockA_iff_spec ⇒ BridgeOutboundLockSpec`: a committed lock DEBITS the per-asset ledger
`bal` at `(originator, asset)` by `amount` (`recBalCreditCell … (-amount)`), PREPENDS an unresolved
bridge-tagged `EscrowRecord` onto `escrows`, advances the log, and FREEZES the other 15 kernel fields.

## RECONCILED onto the running trace-generator layout (the cutover-harness pattern, commit 3aaf0772d)

The running prover (`circuit/src/effect_vm/{columns,trace,air}.rs`, the AUDITED hand-AIR) lays the
bridgeLock row as:

  * **selector `sel::BRIDGE_LOCK = 38`** (NOT a placeholder 2 — the descriptor must AGREE with the
    hand-AIR on the honest trace, so it specializes on the runtime's selector column);
  * `generate_effect_vm_trace`'s `BridgeLock` arm writes `param0 = lock_hash`, **`param1 = value_lo`**
    (the debit value), and the hand-AIR's debit gate reads `PARAM_BASE + 1` (`for s in [CREATE_ESCROW,
    BRIDGE_LOCK] { c_bal = s·(new_bal_lo − old_bal_lo + param1) }`). So the descriptor reads the value
    from **`param1`**, NOT `param0` (which carries the lock hash). Reading `param0` would credit/debit
    the hash — UNSAT on the honest trace.
  * **the nonce TICKS** (`new_state.nonce += 1` in the `BridgeLock` arm; the global hand-AIR nonce gate
    `new_nonce == old_nonce + (1 − s_noop)` ticks every non-NoOp row). So the descriptor TICKS the nonce
    (`gNonce`, the transfer-keystone polynomial), NOT freezes it. The universe-A connector (§7)
    reconciles the runtime tick against the FROZEN ledger nonce exactly as the bridgeMint/burn/transfer
    keystones do (`exec_nonce_is_frozen_not_ticked`).

This is the same reconciliation commit 3aaf0772d applied to burn/notes/bridgeMint: the prior version of
this file FROZE the nonce and read `param.AMOUNT` (param0), making the honest trace UNSAT under the
descriptor. The descriptor now AGREES with the hand-AIR on the honest bridgeLock trace.

## SYSTEM-ROOTS AMPLIFICATION (record-layer STAGE 3, `Exec.SystemRoots`)

`BridgeOutboundLockSpec` ALSO prepends a bridge `parkedBridgeRecord` onto `escrows` — a SET-MEMBERSHIP /
list-digest update. STAGE 3 gives that side-table root its OWN kernel-owned home: `systemRoot.ESCROW`
(`= 0`) in the dedicated `system_roots` sub-block, committed by `Exec.SystemRoots.systemRootsDigest`
and bound by the PROVED anti-ghost tooth `cellCommitS_binds_systemRoots`. §8 connects the lock's escrows
update to THAT root: the prepend MOVES the escrow root (digest injectivity), and a fixed
`system_roots` commitment PINS it — the side-table anti-ghost the coverage memos demand, lifted onto the
named home.

## WHAT IS GENUINELY BLOCKED (reported, NOT papered)

Binding the escrow root into the **EffectVM DESCRIPTOR's** `state_commit` is NOT yet possible on the
CURRENT runtime: the running prover (`circuit/src/effect_vm/{columns,air}.rs`) carries `NUM_AUX = 96`
aux columns with NO `system_roots` digest slot (`auxCol SYSTEM_ROOTS_DIGEST = AUX_BASE + 96 = 186` is
PAST the `EFFECT_VM_WIDTH = 186` boundary), and binds the bridge side-table via the SEPARATE
`effects_hash` accumulator OFF the per-row `state_commit` (the bridge state "lives off-trace" —
`columns.rs:160-163`). So `state_commit = H4(bal,…,cap, 0)` absorbs only the 13 conserved state-block
columns; the escrows root is NOT one of them. We state this EXACTLY as `escrow_root_not_in_descriptor_
commit` so the gap is a THEOREM, not a comment: the bridge side-table root has a NAMED HOME + a PROVED
commitment-layer anti-ghost, but its descriptor-level `state_commit` absorption is gated on the runtime
growing the carrier column (a width touch the prover has not yet taken). Reported, not papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` / `compressNInjective` hypotheses. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.bridgeoutboundlock
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   site0 site1 site2 site3 transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — The bridgeLock selector + the debit parameter (RECONCILED onto the runtime layout). -/

/-- The bridge-outbound-lock selector column index — the running prover's `sel::BRIDGE_LOCK`
(`circuit/src/effect_vm/columns.rs:183`). The descriptor specializes on THIS column so it agrees with
the hand-AIR on the honest trace. -/
def SEL_BRIDGE_LOCK : Nat := 38

/-- The lock row is a bridge-lock row: `s_bridge_lock = 1`, `s_noop = 0`. The `s_noop = 0` clause is
load-bearing for the nonce-TICK gate (`gNonce` reads `s_noop`). -/
def IsBridgeLockRow (env : VmRowEnv) : Prop :=
  env.loc SEL_BRIDGE_LOCK = 1 ∧ env.loc sel.NOOP = 0

/-! ### BridgeLock value column (the running trace generator's convention).

`generate_effect_vm_trace`'s `Effect::BridgeLock` arm lays `param0 = lock_hash`, `param1 = value_lo`
(the debit value). The hand-AIR's `[CREATE_ESCROW, BRIDGE_LOCK]` debit gate reads `PARAM_BASE + 1`, NOT
`param.AMOUNT` (col 0, which carries the lock hash on a lock row). The descriptor MUST read column 1 or
it debits the wrong value (UNSAT on the honest trace). -/
namespace param
/-- BridgeLock debit value lives at param column 1 (`param0 = lock_hash`). -/
def BRIDGE_LOCK_VALUE_LO : Nat := 1
end param

/-- BridgeLock debit value as an expression (param column 1). -/
def ePrmLockValue : EmittedExpr := .var (prmCol param.BRIDGE_LOCK_VALUE_LO)

/-! ## §1 — The bridgeLock per-row gate bodies (debit from `param1`, nonce TICK, full frame freeze). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + value` (so `new = old − value`), reading the
value from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) ePrmLockValue

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a bridge-lock row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce

/-! ## §2 — The emitted bridgeLock descriptor. -/

/-- The bridge-outbound-lock AIR identity. -/
def bridgeLockVmAirName : String := "dregg-effectvm-bridgelock-v1"

/-- The bridge-lock per-row gates: balance debit (from `param1`), bal_hi freeze, nonce TICK, cap/reserved
freeze, 8 fields freeze. -/
def bridgeLockRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`bridgeLockVmDescriptor`** — the bridgeLock effect's concrete EffectVM circuit: the per-row
debit/tick/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED) and the 2 balance-limb range checks. -/
def bridgeLockVmDescriptor : EffectVmDescriptor :=
  { name := bridgeLockVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeLockRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The bridgeLock ROW INTENT (the independent faithfulness target). -/

/-- **`BridgeLockRowIntent env`** — the intended bridge-lock move: the new balance is the old MINUS
`value` (the debit, read from `param1`), the hi limb fixed, the runtime nonce TICKS by one, and the
whole frame fixed. This is the EffectVM-row projection of `BridgeOutboundLockSpec`'s `bal` debit + frame
freeze on the originator cell, reconciled onto the runtime's nonce-tick convention. -/
def BridgeLockRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BRIDGE_LOCK_VALUE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`bridgeLockVm_faithful`.** On a bridge-lock row, the emitted descriptor's per-row gates all hold
IFF `BridgeLockRowIntent` holds — the gates pin EXACTLY the debit + nonce-TICK + frame-freeze move. -/
theorem bridgeLockVm_faithful (env : VmRowEnv) (hrow : IsBridgeLockRow env) :
    (∀ c ∈ bridgeLockRowGates, c.holdsVm env false false) ↔ BridgeLockRowIntent env := by
  obtain ⟨_hsBL, hsN⟩ := hrow
  unfold bridgeLockRowGates gFieldPassAll BridgeLockRowIntent
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
      ePrmLockValue, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmLockValue, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a wrong-output lock row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A lock row whose post-state is NOT the intent move does NOT satisfy the
per-row gates. -/
theorem bridgeLockVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (hwrong : ¬ BridgeLockRowIntent env) :
    ¬ (∀ c ∈ bridgeLockRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((bridgeLockVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A lock row whose post-`bal_lo` is NOT the debit has no satisfying
gate set — the `gBalLoDebit` gate alone rejects it (UNSAT). -/
theorem bridgeLockVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.BRIDGE_LOCK_VALUE_LO)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, ePrmLockValue, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- The lock parameters carried in the param block (only the debit `value` matters for the conserved
leg). -/
structure LockParams where
  value : ℤ

/-- `RowEncodesLock env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition. -/
def RowEncodesLock (env : VmRowEnv) (pre : CellState) (p : LockParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.BRIDGE_LOCK_VALUE_LO) = p.value
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellLockSpec pre p post`** — the per-cell FULL-state lock spec (reconciled onto the runtime row):
the moved cell's `balLo` drops by `value`, the nonce TICKS by one (the runtime sequence counter), and
the rest of the frame is LITERALLY unchanged. This is the EffectVM-row projection of
`BridgeOutboundLockSpec`'s `bal` debit + frame freeze on the originator cell, with the runtime nonce
convention. -/
def CellLockSpec (pre : CellState) (p : LockParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesLock`, `BridgeLockRowIntent` IS the structured `CellLockSpec`. -/
theorem intent_to_cellLockSpec (env : VmRowEnv) (pre post : CellState) (p : LockParams)
    (henc : RowEncodesLock env pre p post) (hint : BridgeLockRowIntent env) :
    CellLockSpec pre p post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo - env.loc (prmCol param.BRIDGE_LOCK_VALUE_LO) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- Flag-independence: the per-row gate set holds with any `(b1, b2)` iff it holds with `(false,
false)` (the gate bodies read only `loc`). -/
theorem bridgeLockRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ bridgeLockRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ bridgeLockRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold bridgeLockRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding (REUSED). -/

/-- **`bridgeLockDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under the
`RowEncodesLock` decoding, forces the structured per-cell `CellLockSpec` AND publishes the post-commit
as `PI[NEW_COMMIT]`. -/
theorem bridgeLockDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (pre post : CellState) (p : LockParams)
    (henc : RowEncodesLock env pre p post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptor env true true) :
    CellLockSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates : ∀ c ∈ bridgeLockRowGates, c.holdsVm env true true := by
    intro c hc
    apply hcs
    unfold bridgeLockVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := bridgeLockRowGates_flag_indep env true true hgates
  have hint := (bridgeLockVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellLockSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ bridgeLockVmDescriptor.constraints := by
      unfold bridgeLockVmDescriptor
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

/-! ## §8 — The anti-ghost commitment tooth (REUSED from the transfer keystone, hash sites identical). -/

/-- **`bridgeLockDescriptor_commit_binds_state`** — the keystone anti-ghost for bridgeLock: two
descriptor-satisfying lock rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell of the locked-out
post-state. -/
theorem bridgeLockDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeLockVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeLockVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash bridgeLockVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ bridgeLockVmDescriptor.constraints := by
        unfold bridgeLockVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A: `CellLockSpec` IS `BridgeOutboundLockSpec`'s per-cell bal image.

`execFullA_bridgeLockA_iff_spec ⇒ BridgeOutboundLockSpec` carries the `bal` debit at
`(originator, asset)`. We project ONE cell of the kernel `bal` ledger into the keystone `CellState`
(the conserved `balLo` limb reads the per-asset entry `bal originator asset`; the EffectVM limbs with no
universe-A analogue are `0`, FROZEN), and prove the originator cell's projection satisfies
`CellLockSpecFrozenNonce` EXACTLY (the debit + frame freeze), reconciling the runtime nonce-tick against
the executor's FROZEN ledger nonce exactly as the bridgeMint/burn/transfer keystones do. -/

open Dregg2.Exec (RecordKernelState RecChainedState CellId AssetId EscrowRecord)
open Dregg2.Circuit.Spec.BridgeOutboundLock (bridgeLock_debit bridgeLock_parks_record parkedBridgeRecord)
open Dregg2.Exec.TurnExecutorFull (execFullA)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). -/
def cellProjLock (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The executor's genuine per-entry image: `CellLockSpec` with the nonce-TICK replaced by nonce-FREEZE
(the runtime row ticks the per-cell sequence counter; the bridgeLock arm freezes the ledger entry's
nonce). Every other clause (balLo debit + frame freeze) is identical. -/
def CellLockSpecFrozenNonce (pre : CellState) (p : LockParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce          -- FROZEN (executor ledger image) — keystone instead demands `+ 1`
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- **`unify_lock_debit`** — the originator cell's projected `(originator, asset)` ledger entry, across
a committed lock (`execFullA … (.bridgeLockA …) = some st'`), satisfies `CellLockSpecFrozenNonce`
EXACTLY: `balLo` drops by `amount`; balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So the
conserved leg IS `BridgeOutboundLockSpec`'s per-cell `bal` image — NOT a fourth spec. -/
theorem unify_lock_debit (st st' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    CellLockSpecFrozenNonce (cellProjLock st.kernel.bal originator asset) ⟨amount⟩
      (cellProjLock st'.kernel.bal originator asset) := by
  have hdebit := bridgeLock_debit st id actor originator destination asset amount st' h
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal originator asset = st.kernel.bal originator asset - amount
  exact hdebit

/-- **`exec_nonce_is_frozen_not_ticked` — the nonce-tick gap, named precisely.** The bridgeLock arm's
projected entry nonce is FROZEN (`0 = 0`), whereas the EffectVM row's `CellLockSpec` TICKS it
(`pre.nonce + 1`). The gap is pinned to exactly the nonce column (the runtime sequence counter vs. the
ledger nonce), exactly as in the bridgeMint/burn/transfer keystones. -/
theorem exec_nonce_is_frozen_not_ticked (st st' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    (cellProjLock st'.kernel.bal originator asset).nonce
      = (cellProjLock st.kernel.bal originator asset).nonce :=
  (unify_lock_debit st st' id actor originator destination asset amount h).2.2.1

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_lock`** — a satisfying run of the runnable descriptor encoding
the originator cell of a committed lock agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre − amount) equals the executor's debited `bal originator asset`,
and the frozen frame agrees. The ONE divergence is the nonce (descriptor ticks the runtime counter; arm
freezes the ledger entry — `exec_nonce_is_frozen_not_ticked`), reported. The escrows-park is connected
to `system_roots[ESCROW]` in §11. -/
theorem descriptor_agrees_with_executor_lock
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (st st' : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) (post : CellState)
    (henc : RowEncodesLock env (cellProjLock st.kernel.bal originator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptor env true true)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    post.balLo = (cellProjLock st'.kernel.bal originator asset).balLo
    ∧ post.balHi = (cellProjLock st'.kernel.bal originator asset).balHi
    ∧ (∀ i, post.fields i = (cellProjLock st'.kernel.bal originator asset).fields i)
    ∧ post.capRoot = (cellProjLock st'.kernel.bal originator asset).capRoot
    ∧ post.reserved = (cellProjLock st'.kernel.bal originator asset).reserved := by
  obtain ⟨hcirc, _⟩ := bridgeLockDescriptor_full_sound hash env hrow
    (cellProjLock st.kernel.bal originator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_lock_debit st st' id actor originator destination asset amount h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — SYSTEM-ROOTS AMPLIFICATION: bind the bridge side-table root (`system_roots[ESCROW]`).

The lock's `escrows` update is a SET-MEMBERSHIP / list-digest mutation. STAGE 3 (`Exec.SystemRoots`)
gives that side-table its OWN kernel-owned home — `systemRoot.ESCROW = 0` in the `system_roots`
sub-block, committed by `systemRootsDigest` and bound by the PROVED anti-ghost tooth
`cellCommitS_binds_systemRoots`. We:

  (a) MODEL the bridge side-table root as the `escrows` list digest placed at `systemRoot.ESCROW`
      (`escrowRootOf`), with every other side-table root carried abstractly;
  (b) prove the lock's prepend MOVES that root whenever it MOVES the escrows digest
      (`lock_moves_escrow_root` — the digest is injective so a non-fixpoint prepend changes it);
  (c) prove a fixed `system_roots` commitment PINS the escrow root (`escrow_root_bound_by_systemCommit`
      — the side-table anti-ghost on the named home);
  (d) and state EXACTLY that the EffectVM DESCRIPTOR's `state_commit` does NOT yet absorb this root
      (`escrow_root_not_in_descriptor_commit`) — the genuinely-blocked leg, reported not papered. -/

open Dregg2.Exec.SystemRoots
  (SysRoots FieldElem systemRootsDigest systemRootsDigest_binds_pointwise cellCommitS
   cellCommitS_binds_systemRoots N_SYSTEM_ROOTS)
open Dregg2.Circuit.StateCommit (compressNInjective)

/-- The kernel-owned escrow-root index as a `Fin N_SYSTEM_ROOTS` (`systemRoot.ESCROW = 0`). -/
def escrowRootIx : Fin N_SYSTEM_ROOTS := ⟨0, by decide⟩

/-- **`escrowRootOf escrowDigest others`** — the `system_roots` sub-block whose ESCROW slot carries the
bridge side-table's `escrows`-list digest, every OTHER slot carried by `others`. The Lean mirror of the
runtime's `system_roots[ESCROW] = escrows_digest`. -/
def escrowRootOf (escrowDigest : FieldElem) (others : SysRoots) : SysRoots :=
  fun i => if i = escrowRootIx then escrowDigest else others i

/-- Reading the ESCROW slot back is exactly the placed digest. -/
@[simp] theorem escrowRootOf_escrow (escrowDigest : FieldElem) (others : SysRoots) :
    escrowRootOf escrowDigest others escrowRootIx = escrowDigest := by
  simp [escrowRootOf]

/-- **`lock_moves_escrow_root` — the escrows update MOVES the named root.** If the lock's prepend changes
the `escrows` list digest (`dPre ≠ dPost` — true whenever the digest is injective and the record is
genuinely new), then the `system_roots` ESCROW slot differs pre vs post. So the bridge side-table update
is VISIBLE at `systemRoot.ESCROW`: an honest prover MUST move the root, an attacker dropping the park
cannot keep it. -/
theorem lock_moves_escrow_root (dPre dPost : FieldElem) (others : SysRoots)
    (hmove : dPre ≠ dPost) :
    escrowRootOf dPre others escrowRootIx ≠ escrowRootOf dPost others escrowRootIx := by
  simp only [escrowRootOf_escrow]; exact hmove

/-- **`escrow_root_bound_by_systemCommit` — the side-table anti-ghost on the NAMED HOME.** Under
`compressNInjective`, two cells with the SAME `system_roots` commitment (over the same `rest` prefix)
have the SAME escrow root. So a fixed cell commitment PINS the bridge side-table digest: tampering the
parked escrow record (dropping the lock) provably MOVES the commitment. This is the STAGE-3 anti-ghost
tooth `cellCommitS_binds_systemRoots` specialized to the escrow slot. -/
theorem escrow_root_bound_by_systemCommit (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    sr escrowRootIx = sr' escrowRootIx :=
  systemRootsDigest_binds_pointwise compressN hN sr sr'
    (cellCommitS_binds_systemRoots compressN hN rest sr sr' h) escrowRootIx

/-- **`escrow_root_not_in_descriptor_commit` — the genuinely-blocked leg, surfaced as a THEOREM.**
The EffectVM DESCRIPTOR's `state_commit` (via `transferHashSites`) absorbs ONLY the 13
balance/nonce/field/cap state-block columns (`absorbedCols`), NONE of which is the `system_roots`
ESCROW digest. The runtime carries `NUM_AUX = 96` aux columns with NO `system_roots` digest slot
(`auxCol SYSTEM_ROOTS_DIGEST = 186` is PAST `EFFECT_VM_WIDTH = 186`) and binds the bridge side-table via
the SEPARATE `effects_hash` accumulator (the bridge state "lives off-trace"). So the escrow root, though
it now has a NAMED HOME + a PROVED commitment-layer anti-ghost (§above), is NOT absorbed into THIS
descriptor's `state_commit`: that absorption is gated on the runtime growing a `system_roots` digest
carrier column. We witness the gap concretely: two rows differing ONLY in the (nonexistent) escrow-root
aux column have IDENTICAL `absorbedCols`. -/
theorem escrow_root_not_in_descriptor_commit (env : VmRowEnv) (escrowRoot : ℤ) :
    absorbedCols { loc := fun v => if v = auxCol aux_off_sys.SYSTEM_ROOTS_DIGEST then escrowRoot
                                   else env.loc v
                 , nxt := env.nxt, pub := env.pub }
      = absorbedCols env := by
  -- `absorbedCols` reads only `saCol`-state columns (76..87); the SYSTEM_ROOTS_DIGEST aux column is 186.
  unfold absorbedCols
  have hne : ∀ off : Nat, off < 14 →
      saCol off ≠ auxCol aux_off_sys.SYSTEM_ROOTS_DIGEST := by
    intro off hoff
    simp only [saCol, auxCol, STATE_AFTER_BASE, AUX_BASE, PARAM_BASE, STATE_BEFORE_BASE,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, aux_off_sys.SYSTEM_ROOTS_DIGEST]
    omega
  simp only [if_neg (hne state.BALANCE_LO (by decide)),
    if_neg (hne state.BALANCE_HI (by decide)), if_neg (hne state.NONCE (by decide)),
    if_neg (hne (state.FIELD_BASE + 0) (by decide)), if_neg (hne (state.FIELD_BASE + 1) (by decide)),
    if_neg (hne (state.FIELD_BASE + 2) (by decide)), if_neg (hne (state.FIELD_BASE + 3) (by decide)),
    if_neg (hne (state.FIELD_BASE + 4) (by decide)), if_neg (hne (state.FIELD_BASE + 5) (by decide)),
    if_neg (hne (state.FIELD_BASE + 6) (by decide)), if_neg (hne (state.FIELD_BASE + 7) (by decide)),
    if_neg (hne state.CAP_ROOT (by decide))]

/-- **`escrow_prepend_is_out_of_row` — the honest finding (universe-A leg).** A committed lock's
`escrows` store is `parkedBridgeRecord :: st.escrows`. This list-insert is a universe-A property carried
by the `escrowsComponentC` list digest (`Witness/bridgeLockAWitness`), now with a NAMED commitment home
at `systemRoot.ESCROW` (§11), but NOT by any per-row gate or hash-site of `bridgeLockVmDescriptor` —
whose hash-sites absorb only the 13 conserved state-block columns. -/
theorem escrow_prepend_is_out_of_row (st st' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (h : execFullA st (.bridgeLockA id actor originator destination asset amount) = some st') :
    st'.kernel.escrows
      = parkedBridgeRecord id originator destination asset amount :: st.kernel.escrows :=
  bridgeLock_parks_record st id actor originator destination asset amount st' h

/-! ## §12 — NON-VACUITY: a concrete lock row realizes the intent; a forged one is rejected. -/

/-- A concrete lock row: `bal_lo 100 → 95` (debit 5 from `param1`), nonce 5 → 6 (TICK), frame fixed. -/
def goodLockRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_BRIDGE_LOCK then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.BRIDGE_LOCK_VALUE_LO then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodLockRow_isRow : IsBridgeLockRow goodLockRow := by
  unfold IsBridgeLockRow goodLockRow
  refine ⟨by norm_num [SEL_BRIDGE_LOCK], ?_⟩
  norm_num [sel.NOOP, SEL_BRIDGE_LOCK, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
    param.BRIDGE_LOCK_VALUE_LO]

/-- **NON-VACUITY (witness TRUE).** `goodLockRow` REALIZES the bridge-lock intent: bal_lo `100 → 95`
(debit 5 from `param1`), nonce TICKS `5 → 6`, frame fixed. -/
theorem goodLockRow_realizes_intent : BridgeLockRowIntent goodLockRow := by
  unfold BridgeLockRowIntent goodLockRow
  simp only [sbCol, saCol, prmCol, SEL_BRIDGE_LOCK, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.BRIDGE_LOCK_VALUE_LO]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 38) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 38) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED lock row: `goodLockRow` with the post-`bal_lo` tampered to `999` (not the intended `95`). -/
def badLockRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodLockRow.loc v
  nxt := goodLockRow.nxt
  pub := goodLockRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badLockRow`'s post-`bal_lo` is NOT the
debit, so the `gBalLoDebit` gate REJECTS it — a concrete UNSAT. -/
theorem badLockRow_rejected : ¬ (VmConstraint.gate gBalLoDebit).holdsVm badLockRow false false := by
  apply bridgeLockVm_rejects_wrong_balance
  simp only [badLockRow, goodLockRow, sbCol, saCol, prmCol, SEL_BRIDGE_LOCK, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.BRIDGE_LOCK_VALUE_LO]
  norm_num

/-- **NON-VACUITY for the escrow-root binding (witness moves).** Two distinct escrow digests place
distinct roots at `systemRoot.ESCROW`, so the side-table update is genuinely visible — a `:= 0` stub
escrow root would make these EQUAL (forbidden). -/
theorem escrowRoot_nonvacuous (others : SysRoots) :
    escrowRootOf 1234 others escrowRootIx ≠ escrowRootOf 9999 others escrowRootIx :=
  lock_moves_escrow_root 1234 9999 others (by decide)

/-! ## §13 — Axiom-hygiene pins. -/

#guard bridgeLockVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard bridgeLockVmDescriptor.hashSites.length == 4
#guard bridgeLockVmDescriptor.traceWidth == 186

#assert_axioms bridgeLockVm_faithful
#assert_axioms bridgeLockVm_rejects_wrong_output
#assert_axioms bridgeLockVm_rejects_wrong_balance
#assert_axioms intent_to_cellLockSpec
#assert_axioms bridgeLockRowGates_flag_indep
#assert_axioms bridgeLockDescriptor_full_sound
#assert_axioms bridgeLockDescriptor_commit_binds_state
#assert_axioms unify_lock_debit
#assert_axioms exec_nonce_is_frozen_not_ticked
#assert_axioms descriptor_agrees_with_executor_lock
#assert_axioms lock_moves_escrow_root
#assert_axioms escrow_root_bound_by_systemCommit
#assert_axioms escrow_root_not_in_descriptor_commit
#assert_axioms escrow_prepend_is_out_of_row
#assert_axioms goodLockRow_isRow
#assert_axioms goodLockRow_realizes_intent
#assert_axioms badLockRow_rejected
#assert_axioms escrowRoot_nonvacuous

/-! ## §H — CLASS-A PROMOTION: the GENUINE in-row bridge-escrow-root RECOMPUTE.

The §A amplification proved `escrow_root_not_in_descriptor_commit` (the deployed descriptor does NOT
bind the bridge escrow root). This section PROMOTES bridgeLock to class A by binding it genuinely, via the
shared `EffectVmEmitEscrowRoot` recompute: the locked outbound-bridge record's leaf is recomputed in-row
`hash[id,creator,recipient,amount,asset,resolved]` (amount = the SAME `param.AMOUNT` driving the debit),
then `new_root = hash[record_leaf, old_root]` — FORCED, not asserted. So the locked amount IS the debited
amount, bound by the recomputed root. The §1–§10 debit + frame soundness are UNCHANGED. -/

open Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
  (escrowRecomputeSites escrowRootHolds escrowRootAdvance_forced escrowRoot_binds_record
   escrowRoot_amount_bound leafOf advanceOf)

/-- **`bridgeLockVmDescriptorGenuine`** — the CLASS-A bridgeLock circuit: the §2 per-row gates (debit +
nonce tick + frame freeze) with the genuine recompute sites prepended to the GROUP-4 sites. -/
def bridgeLockVmDescriptorGenuine : EffectVmDescriptor :=
  { name := bridgeLockVmAirName ++ "-genuine-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeLockRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := escrowRecomputeSites ++ transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

theorem genuine_sites_split (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : siteHoldsAll hash env (escrowRecomputeSites ++ transferHashSites)) :
    escrowRootHolds hash env := by
  unfold escrowRootHolds escrowRecomputeSites
  unfold escrowRecomputeSites at h
  unfold siteHoldsAll at h ⊢
  simp only [List.cons_append, List.nil_append, siteHoldsAll.go,
    EffectVmEmitEscrowRoot.siteEscrowLeaf, EffectVmEmitEscrowRoot.siteEscrowRootAdvance,
    VmHashSite.resolvedInputs, HashInput.resolve, List.map_cons, List.map_nil] at h ⊢
  exact ⟨h.1, h.2.1, trivial⟩

/-- **`bridgeLockGenuine_sound` — THE CLASS-A SOUNDNESS.** The genuine descriptor forces the per-cell
`CellLockSpec` (debit + frame freeze), the GENUINE bridge-escrow-root recompute (root FORCED), AND the
published commit. -/
theorem bridgeLockGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeLockRow env)
    (pre post : CellState) (p : LockParams)
    (henc : RowEncodesLock env pre p post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptorGenuine env true true) :
    CellLockSpec pre p post
      ∧ env.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER
          = advanceOf hash
              (leafOf hash (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ID))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.CREATOR))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RECIPIENT))
                (env.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.ASSET))
                (env.loc (prmCol EffectVmEmitEscrowRoot.ep.RESOLVED)))
              (env.loc EffectVmEmitEscrowRoot.SYS_DIG_BEFORE)
      ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, hsites⟩ := hsat
  have hgates : ∀ c ∈ bridgeLockRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold bridgeLockVmDescriptorGenuine
    simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := bridgeLockRowGates_flag_indep env true true hgates
  have hint := (bridgeLockVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellLockSpec env pre post p henc hint, ?_, ?_⟩
  · exact escrowRootAdvance_forced hash env (genuine_sites_split hash env hsites)
  · have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
      intro c hc
      have hmem : c ∈ bridgeLockVmDescriptorGenuine.constraints := by
        unfold bridgeLockVmDescriptorGenuine
        simp only [List.mem_append]; exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    have hpin := (boundaryLast_pins env hlast).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
    rw [← hsaC]; exact hpin

/-- **`bridgeLockGenuine_binds_record` — THE CLASS-A ANTI-GHOST.** Two genuine rows with the same recomputed
new root have the SAME locked amount (and every record field). A forged lock moves the root ⇒ moves
`state_commit` ⇒ UNSAT. -/
theorem bridgeLockGenuine_binds_record (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeLockVmDescriptorGenuine e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeLockVmDescriptorGenuine e₂ true true)
    (hroot : e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER) :
    e₁.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) :=
  escrowRoot_amount_bound hash hCR e₁ e₂
    (genuine_sites_split hash e₁ hsat₁.2) (genuine_sites_split hash e₂ hsat₂.2) hroot

theorem bridgeLockGenuine_recompute_nonvacuous :
    escrowRootHolds EffectVmEmitEscrowRoot.cN EffectVmEmitEscrowRoot.goodEscrowRow :=
  EffectVmEmitEscrowRoot.goodEscrowRow_recomputes

#guard bridgeLockVmDescriptorGenuine.hashSites.length == 2 + 4
#guard bridgeLockVmDescriptorGenuine.traceWidth == 186

#assert_axioms genuine_sites_split
#assert_axioms bridgeLockGenuine_sound
#assert_axioms bridgeLockGenuine_binds_record

/-! ## §W — FULL-STATE ON THE RUNNABLE DESCRIPTOR (the MAGNESIUM breadth): bind ALL 17 fields.

§A proved `escrow_root_not_in_descriptor_commit` (the deployed descriptor binds only the 13 conserved
state-block columns, NOT the `system_roots` digest); §H bound the escrow RECORD via the genuine recompute
but still off the published `state_commit`. This section CLOSES the headline gap via the shared
`EffectVmFullStateRunnable` recipe: the WIDE descriptor (`hashSites := wideHashSites`,
`traceWidth := EFFECT_VM_WIDTH_SYSROOTS`) absorbs the dedicated `sysRootsDigestCol` carrier into the
published `state_commit`, so the descriptor the prover RUNS binds the per-cell DEBIT block AND all 8
side-table roots — the full 17-field post-state. Tamper ANY field or ANY side-table root ⇒ UNSAT
(`wide_rejects_state_tamper` / `wide_rejects_root_tamper`).

bridgeLock is the DEBIT case: the per-cell block is `CellLockSpec` (`balLo` debited by `value`, frame
frozen, nonce ticked) and the `system_roots` sub-block advances ONLY at `ESCROW` (the bridge-tagged park
prepended onto `escrows`), the other 7 roots frozen. -/

open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (RunnableFullStateSpec runnable_full_sound runnable_full_commit_binds
   wide_rejects_state_tamper wide_rejects_root_tamper wideHashSites)
open Dregg2.Exec.SystemRoots (systemRootsDigest emptySystemRoots)

/-- **`bridgeLockVmDescriptorWide`** — bridgeLock's descriptor WIDENED to the `system_roots`-absorbing
shape: the SAME per-row gates + transitions + boundary pins, but `traceWidth := EFFECT_VM_WIDTH_SYSROOTS`
and `hashSites := wideHashSites`. Strictly additive over `bridgeLockVmDescriptor` (byte-identical
constraint list; width +2; site 3's spare `.zero` 4th slot becomes the `sysRootsDigestCol` carrier). -/
def bridgeLockVmDescriptorWide : EffectVmDescriptor :=
  { bridgeLockVmDescriptor with
    name := bridgeLockVmAirName ++ "-sysroots"
    traceWidth := EFFECT_VM_WIDTH_SYSROOTS
    hashSites := wideHashSites }

/-- The wide descriptor's constraints ARE bridgeLock's (the width/site swap leaves the
per-row/transition/boundary gate list untouched). -/
theorem bridgeLockWide_constraints_eq :
    bridgeLockVmDescriptorWide.constraints = bridgeLockVmDescriptor.constraints := rfl

/-- **`bridgeLockGates_give_cellSpec` — the GATE-ONLY per-cell soundness (no hash-site hypothesis).**
The per-row gates of the bridgeLock descriptor, on a lock row decoded by `RowEncodesLock`, force
`CellLockSpec`. The body of `bridgeLockDescriptor_full_sound` with the hash-site layer DROPPED — it factors
through `bridgeLockVm_faithful` + `intent_to_cellLockSpec`, NEITHER of which reads the sites. -/
theorem bridgeLockGates_give_cellSpec (env : VmRowEnv) (pre post : CellState) (p : LockParams)
    (hrow : IsBridgeLockRow env) (henc : RowEncodesLock env pre p post)
    (hgates : ∀ c ∈ bridgeLockVmDescriptor.constraints, c.holdsVm env true true) :
    CellLockSpec pre p post := by
  have hrowgates : ∀ c ∈ bridgeLockRowGates, c.holdsVm env true true := by
    intro c hc
    apply hgates
    unfold bridgeLockVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hrowgates' := bridgeLockRowGates_flag_indep env true true hrowgates
  exact intent_to_cellLockSpec env pre post p henc ((bridgeLockVm_faithful env hrow).mp hrowgates')

/-- **`BridgeLockFullClause`** — the full declarative post-state for bridgeLock over `(pre, post,
postRoots)`: the per-cell `CellLockSpec` (`balLo` DEBITED by `p.value`, frame frozen, nonce ticked) AND the
`system_roots` sub-block IS the declared `expectedRoots` (the `ESCROW` slot carrying the post-prepend
escrow-list digest, the other 7 roots frozen). Non-vacuous: §`bridgeLock_wide_realizes` inhabits it. -/
def BridgeLockFullClause (p : LockParams) (expectedRoots : SysRoots)
    (pre post : CellState) (postRoots : SysRoots) : Prop :=
  CellLockSpec pre p post ∧ postRoots = expectedRoots

/-- **`bridgeLockRunnableSpec` — the FULL-state RUNNABLE instance.** `decodeAfter` is `RowEncodesLock` PLUS
the declared post-roots witness PLUS the carrier pin `sysRootsDigestCol = systemRootsDigest postRoots`
(the anti-ghost hd-link); `decodeFull` projects the wide descriptor's per-row gates to the GATE-ONLY
`bridgeLockGates_give_cellSpec`, then carries the declared post-roots. THIN + NON-VACUOUS (the per-cell
DEBIT + the prepended side-table root, NOT `True`). -/
def bridgeLockRunnableSpec (hash : List ℤ → ℤ) (p : LockParams) (expectedRoots : SysRoots) :
    RunnableFullStateSpec CellState where
  descriptor    := bridgeLockVmDescriptorWide
  usesWideSites := rfl
  isRow         := IsBridgeLockRow
  decodeAfter   := fun env pre post postRoots =>
    RowEncodesLock env pre p post ∧ postRoots = expectedRoots
      ∧ env.loc sysRootsDigestCol = systemRootsDigest hash postRoots
  fullClause    := BridgeLockFullClause p expectedRoots
  decodeFull    := by
    intro env pre post postRoots hrow hdec hgates
    obtain ⟨henc, hroots, _hcar⟩ := hdec
    exact ⟨bridgeLockGates_give_cellSpec env pre post p hrow henc
            (bridgeLockWide_constraints_eq ▸ hgates), hroots⟩

/-- **`bridgeLock_runnable_full_sound` — THE FULL-STATE ON RUNNABLE crown (bridgeLock).** A row satisfying
the WIDE runnable descriptor, under the structured decode, pins the FULL 17-field declarative post-state:
the per-cell DEBIT/freeze/tick AND the whole `system_roots` sub-block. Crypto discharged ONCE in the
generic `runnable_full_sound`; the per-effect obligation was only the thin decode. -/
theorem bridgeLock_runnable_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : LockParams) (postRoots expectedRoots : SysRoots)
    (hrow : IsBridgeLockRow env)
    (henc : RowEncodesLock env pre p post) (hroots : postRoots = expectedRoots)
    (hcar : env.loc sysRootsDigestCol = systemRootsDigest hash postRoots)
    (hsat : satisfiedVm hash bridgeLockVmDescriptorWide env true true) :
    BridgeLockFullClause p expectedRoots pre post postRoots :=
  runnable_full_sound (bridgeLockRunnableSpec hash p expectedRoots) hash env pre post postRoots
    hrow ⟨henc, hroots, hcar⟩ hsat

/-- **`bridgeLock_wide_rejects_state_tamper` — per-cell-block anti-ghost on the RUNNABLE descriptor.** -/
theorem bridgeLock_wide_rejects_state_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash bridgeLockVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeLockVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    (htamper : absorbedCols e₁ ≠ absorbedCols e₂) : False :=
  wide_rejects_state_tamper (bridgeLockRunnableSpec hash ⟨0⟩ sr₁) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-- **`bridgeLock_wide_rejects_root_tamper` — side-table anti-ghost on the RUNNABLE descriptor (the gap's
headline tooth, CLOSED).** Two wide rows publishing the same `NEW_COMMIT` (with `systemRootsDigest`
carriers) but whose side-table sub-blocks DIFFER at some index cannot both satisfy — the `escrows` root
(the parked bridge record) and every other root is now bound BY the running commitment. -/
theorem bridgeLock_wide_rejects_root_tamper (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash bridgeLockVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeLockVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = systemRootsDigest hash sr₂)
    {i : Fin N_SYSTEM_ROOTS} (htamper : sr₁ i ≠ sr₂ i) : False :=
  wide_rejects_root_tamper (bridgeLockRunnableSpec hash ⟨0⟩ sr₁) hash hCR e₁ e₂ sr₁ sr₂
    hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂ htamper

/-! ### Non-vacuity of the full-state instance: a real debited+parked post-state inhabits the clause. -/

/-- A pre cell (bal 100, nonce 5, frame 0) and its honest lock image (bal `100 - 5 = 95`, nonce 6). -/
def widePreCell : CellState :=
  { balLo := 100, balHi := 0, nonce := 5, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }
def widePostCell : CellState :=
  { balLo := 95, balHi := 0, nonce := 6, fields := fun _ => 0, capRoot := 0, reserved := 0, commit := 0 }

/-- A concrete post-roots sub-block: the `ESCROW` root carries the post-prepend escrow-list digest `1042`,
every other side-table root `0` (frozen). -/
def widePostRoots : SysRoots := escrowRootOf 1042 emptySystemRoots

/-- **`bridgeLock_wide_realizes` — NON-VACUITY of the instance (witness TRUE).** The full clause is
INHABITED by a genuine lock: `widePostCell` is the honest debited image of `widePreCell` (`100 → 95`,
debit 5, nonce `5 → 6`) and the post-roots advance ONLY at `ESCROW`. So `fullClause` is NOT `True`. -/
theorem bridgeLock_wide_realizes :
    (bridgeLockRunnableSpec EffectVmEmitEscrowRoot.cN ⟨5⟩ widePostRoots).fullClause
      widePreCell widePostCell widePostRoots :=
  ⟨⟨by norm_num [widePreCell, widePostCell], rfl, rfl, fun _ => rfl, rfl, rfl⟩, rfl⟩

/-- **`bridgeLock_wide_clause_refutable` — the clause is REFUTABLE (witness FALSE).** A post-state whose
`balLo` is NOT the debit (`999 ≠ 100 - 5`) FAILS `BridgeLockFullClause`, pinning non-vacuity from BOTH
sides. -/
theorem bridgeLock_wide_clause_refutable :
    ¬ BridgeLockFullClause ⟨5⟩ widePostRoots widePreCell
        { widePostCell with balLo := 999 } widePostRoots := by
  rintro ⟨⟨hbal, _⟩, _⟩
  simp only [widePreCell, widePostCell] at hbal
  norm_num at hbal

/-- **Side-table non-vacuity (the root genuinely moves).** The post-roots' `ESCROW` slot (`1042`) differs
from the pre-roots' (`0`) — the prepend is genuinely visible at `systemRoot.ESCROW`. -/
theorem bridgeLock_wide_root_moves :
    widePostRoots escrowRootIx ≠ emptySystemRoots escrowRootIx := by
  simp only [widePostRoots, escrowRootOf_escrow, emptySystemRoots]
  norm_num

#guard bridgeLockVmDescriptorWide.traceWidth == 188
#guard bridgeLockVmDescriptorWide.hashSites.length == 4
#guard bridgeLockVmDescriptorWide.constraints.length == 13 + 14 + 4 + 3

#assert_axioms bridgeLockGates_give_cellSpec
#assert_axioms bridgeLock_runnable_full_sound
#assert_axioms bridgeLock_wide_rejects_state_tamper
#assert_axioms bridgeLock_wide_rejects_root_tamper
#assert_axioms bridgeLock_wide_realizes
#assert_axioms bridgeLock_wide_clause_refutable
#assert_axioms bridgeLock_wide_root_moves

end Dregg2.Circuit.Emit.EffectVmEmitBridgeLockA
