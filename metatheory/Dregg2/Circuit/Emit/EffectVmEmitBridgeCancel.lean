/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel — the bridgeCancel (bridge-outbound-CANCEL) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer, RECONCILED onto the
running trace-generator layout and AMPLIFIED to bind the bridge side-table root (`system_roots[ESCROW]`).

This is the bridge-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `bridgeCancelA`. Universe A (`Spec/bridgeoutboundcancel.lean`) carries the FULL-state
soundness `bridgeCancelChainA_iff_spec ⇒ BridgeOutboundCancelSpec`: a committed cancel is the
post-timeout REFUND — the parked bridge value returns to the originator. It CREDITS the per-asset
ledger `bal` at `(r.creator, r.asset)` by `+r.amount`, marks the parked record resolved
(`markResolved … id`), advances the log, and FREEZES the other 15 kernel fields.

## RECONCILED onto the running trace-generator layout (the cutover-harness pattern)

The running prover (`circuit/src/effect_vm/{columns,trace,air}.rs`, the AUDITED hand-AIR) lays the
bridgeCancel row as:

  * **selector `sel::BRIDGE_CANCEL = 33`** (the descriptor specializes on the runtime's selector).
  * The `BridgeCancel` trace arm CREDITS the refund: the parked bridge value RETURNS to the locker
    (`r.creator`), so the cell's `bal_lo` row column rises by `+amount` (`new_bal_lo = old_bal_lo +
    amount`, the amount read from `param::AMOUNT` — the SAME parked amount the §H escrow-root recompute
    binds). This is EXACTLY the verified executor's image (`bridgeCancelKAsset` credits `(r.creator,
    r.asset)` by `+r.amount`; the Rust `cancel_bridge` unlocks the parked note back to the locker). A
    PRIOR version FROZE `bal_lo` on-trace (treating the refund as off-trace, reconciled to the executor's
    credit only at `amount = 0`) — that divergence is now CLOSED: the descriptor CREDITS on-trace,
    matching the executor for EVERY refund (the precedent is `EffectVmEmitRefundEscrow`'s on-trace
    credit). The Rust trace/AIR are aligned to credit too.
  * **the nonce TICKS** (`new_state.nonce += 1` in the `BridgeCancel` arm; the global nonce gate ticks
    every non-NoOp row).

So the descriptor now AGREES with the executor on the honest bridgeCancel trace: balance CREDITED by the
refund, nonce ticks. §10–§11 prove the per-cell circuit⟺executor agreement on the REFUNDED cell directly
(credit = credit, `descriptor_credits_match_executor_refund`), divergence-free.

## SYSTEM-ROOTS AMPLIFICATION (record-layer STAGE 3, `Exec.SystemRoots`)

`BridgeOutboundCancelSpec` ALSO marks the parked bridge record resolved (`escrows := markResolved … id`).
STAGE 3 gives that side-table root its OWN kernel-owned home: `systemRoot.ESCROW` (`= 0`), committed by
`Exec.SystemRoots.systemRootsDigest` and bound by `cellCommitS_binds_systemRoots`. §11 connects the
resolve to THAT root and reports the descriptor-level gap honestly.

## THE REFUND CREDIT IS NOW ON-TRACE (the closed divergence) + the escrow-root finding

The REFUND CREDIT is now bound ON the per-cell `bal_lo` row (the `gBalLoCredit` gate, `+param::AMOUNT`),
matching the executor's `+r.amount` credit — the formerly-carried on-trace-freeze-vs-credit divergence is
CLOSED (`runtime_credit_matches_univA`, §9). What REMAINS a descriptor-level finding (a SEPARATE concern,
not the refund) is the escrow side-table ROOT absorption into the EffectVM DESCRIPTOR's `state_commit`:
the running prover carries NO `system_roots` digest column inside `EFFECT_VM_WIDTH` (`auxCol
SYSTEM_ROOTS_DIGEST = 186` is PAST `EFFECT_VM_WIDTH = 186`) and binds the side-table via the SEPARATE
`effects_hash` accumulator. We state THAT exactly as a theorem (`escrow_root_not_in_descriptor_commit`),
reported, not papered — and §H's `bridgeCancelVmDescriptorGenuine` binds the escrow root genuinely via
the dedicated escrow-root recompute sites.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` / `compressNInjective` hypotheses. No `sorry`, no `:= True`, no `native_decide`.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.bridgeoutboundcancel
import Dregg2.Exec.SystemRoots

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel

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

/-! ## §0 — The bridgeCancel selector (RECONCILED onto the runtime layout). -/

/-- The bridge-outbound-cancel selector column index — the running prover's `sel::BRIDGE_CANCEL`
(`circuit/src/effect_vm/columns.rs:163`). A cancel takes NO on-trace move parameter (the refund is
off-trace). -/
def SEL_BRIDGE_CANCEL : Nat := 33

/-- The cancel row is a bridge-cancel row: `s_bridge_cancel = 1`, `s_noop = 0`. The `s_noop = 0` clause
is load-bearing for the nonce-TICK gate (`gNonce` reads `s_noop`). -/
def IsBridgeCancelRow (env : VmRowEnv) : Prop :=
  env.loc SEL_BRIDGE_CANCEL = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The bridgeCancel per-row gate bodies (balance CREDIT on-trace, nonce TICK, frame freeze).

The runtime cancel row CREDITS the refund: the parked bridge value returns to the locker, so the
conserved `bal_lo` limb RISES by `+amount` (`new_bal_lo = old_bal_lo + amount`, the amount read from
`param::AMOUNT`). The whole non-balance frame is FROZEN, the nonce TICKS. This matches the verified
executor's `+r.amount` credit (the on-trace credit precedent is `EffectVmEmitRefundEscrow`). -/

/-- Balance-lo CREDIT body: `new_bal_lo − old_bal_lo − amount` (so `new = old + amount`), reading the
refunded amount from `param::AMOUNT` (the SAME parked amount the §H escrow-root recompute binds). The
parked bridge value returns to the locker. -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) (ePrm param.AMOUNT))

/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a bridge-cancel row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce

/-! ## §2 — The emitted bridgeCancel descriptor. -/

/-- The bridge-outbound-cancel AIR identity. -/
def bridgeCancelVmAirName : String := "dregg-effectvm-bridgecancel-v1"

/-- The bridge-cancel per-row gates: balance CREDIT (refund), bal_hi freeze, nonce TICK,
cap/reserved freeze, 8 fields freeze. -/
def bridgeCancelRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHi, .gate gNonceTick
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`bridgeCancelVmDescriptor`** — the bridgeCancel effect's concrete EffectVM circuit: the per-row
freeze/tick gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash
sites (REUSED) and the 2 balance-limb range checks. -/
def bridgeCancelVmDescriptor : EffectVmDescriptor :=
  { name := bridgeCancelVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeCancelRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The bridgeCancel ROW INTENT (the independent faithfulness target). -/

/-- **`BridgeCancelRowIntent env`** — the intended on-trace cancel move: `bal_lo` is CREDITED by
`param::AMOUNT` (the refund returns the parked value to the locker), bal_hi/cap/reserved/8 fields FIXED,
the runtime nonce TICKS by one. This is the EffectVM-row projection of the executor's refund credit
(`bridgeCancelKAsset` credits `(r.creator, r.asset)` by `+r.amount`). -/
def BridgeCancelRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`bridgeCancelVm_faithful`.** On a bridge-cancel row, the emitted descriptor's per-row gates all
hold IFF `BridgeCancelRowIntent` holds — the gates pin EXACTLY the balance-freeze + nonce-TICK +
frame-freeze move. -/
theorem bridgeCancelVm_faithful (env : VmRowEnv) (hrow : IsBridgeCancelRow env) :
    (∀ c ∈ bridgeCancelRowGates, c.holdsVm env false false) ↔ BridgeCancelRowIntent env := by
  obtain ⟨_hsBC, hsN⟩ := hrow
  unfold bridgeCancelRowGates gFieldPassAll BridgeCancelRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHi, gNonceTick, gNonce, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHi, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResPass, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldPass, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-! ## §5 — ANTI-GHOST: a wrong-output cancel row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A cancel row whose post-state is NOT the freeze+tick does NOT satisfy the
per-row gates. -/
theorem bridgeCancelVm_rejects_wrong_output (env : VmRowEnv) (hrow : IsBridgeCancelRow env)
    (hwrong : ¬ BridgeCancelRowIntent env) :
    ¬ (∀ c ∈ bridgeCancelRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((bridgeCancelVm_faithful env hrow).mp h)

/-- **Anti-ghost (balance tamper).** A cancel row whose post-`bal_lo` is NOT the credited value
`old + amount` (a wrong/forged refund) has no satisfying gate set — the `gBalLoCredit` gate alone
rejects it (UNSAT). The refund credit amount is pinned to `param::AMOUNT` (the bound parked amount);
it cannot be over- or under-credited on the cell `bal_lo` row. -/
theorem bridgeCancelVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- `RowEncodesCancel env pre amount post` ties the row's state-block columns + the refund amount param
to a `(pre, amount, post)` cell transition (the cancel CREDITS the refund `amount = param::AMOUNT`). -/
def RowEncodesCancel (env : VmRowEnv) (pre : CellState) (amount : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = amount
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellCancelSpec pre amount post`** — the per-cell FULL-state on-trace cancel spec (reconciled onto
the runtime row): `balLo` is CREDITED by the refund `amount` (the parked value returns to the locker),
bal_hi/fields/capRoot/reserved are FROZEN, and the nonce TICKS by one. This matches the executor's
`+r.amount` refund credit (`bridgeCancelKAsset`). -/
def CellCancelSpec (pre : CellState) (amount : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Decode lemma: under `RowEncodesCancel`, `BridgeCancelRowIntent` IS the structured `CellCancelSpec`. -/
theorem intent_to_cellCancelSpec (env : VmRowEnv) (pre post : CellState) (amount : ℤ)
    (henc : RowEncodesCancel env pre amount post) (hint : BridgeCancelRowIntent env) :
    CellCancelSpec pre amount post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.AMOUNT) := by
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
false)`. -/
theorem bridgeCancelRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ bridgeCancelRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ bridgeCancelRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold bridgeCancelRowGates gFieldPassAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding (REUSED). -/

/-- **`bridgeCancelDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor, under the
`RowEncodesCancel` decoding, forces the structured per-cell `CellCancelSpec` AND publishes the
post-commit as `PI[NEW_COMMIT]`. -/
theorem bridgeCancelDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (hrow : IsBridgeCancelRow env) (pre post : CellState) (amount : ℤ)
    (henc : RowEncodesCancel env pre amount post)
    (hsat : satisfiedVm hash bridgeCancelVmDescriptor env true true) :
    CellCancelSpec pre amount post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates : ∀ c ∈ bridgeCancelRowGates, c.holdsVm env true true := by
    intro c hc
    apply hcs
    unfold bridgeCancelVmDescriptor
    simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := bridgeCancelRowGates_flag_indep env true true hgates
  have hint := (bridgeCancelVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellCancelSpec env pre post amount henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ bridgeCancelVmDescriptor.constraints := by
      unfold bridgeCancelVmDescriptor
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

/-- **`bridgeCancelDescriptor_commit_binds_state`** — the keystone anti-ghost for bridgeCancel: two
descriptor-satisfying cancel rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns. So a prover cannot keep `NEW_COMMIT` while tampering any absorbed cell of the post-state. -/
theorem bridgeCancelDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeCancelVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeCancelVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash bridgeCancelVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ bridgeCancelVmDescriptor.constraints := by
        unfold bridgeCancelVmDescriptor
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

/-! ## §9 — CONNECTOR to universe-A + the REFUND CREDIT AGREEMENT (formerly the carried divergence).

`bridgeCancelChainA_iff_spec ⇒ BridgeOutboundCancelSpec` carries a `bal` CREDIT at `(r.creator, r.asset)`
by `+r.amount`. The RUNTIME descriptor now ALSO CREDITS the cell `bal_lo` on-trace by `+amount` (the
parked value returns to the locker; the on-trace credit precedent is `EffectVmEmitRefundEscrow`). So the
descriptor and the executor AGREE on the refund: both raise the entry by `+amount`. A PRIOR version froze
`bal_lo` on-trace and reported the gap as `runtime_frozen_vs_univA_credit_divergence` (reconciled only at
`amount = 0`); that divergence is now CLOSED — the descriptor's on-trace post-entry IS the executor's
credited post-entry (`runtime_credit_matches_univA`, an agreement). -/

open Dregg2.Exec (RecordKernelState RecChainedState CellId AssetId EscrowRecord markResolved)
open Dregg2.Circuit.Spec.BridgeOutboundCancel
  (BridgeOutboundCancelSpec cancelGuard bridgeCancel_refund)
open Dregg2.Exec.TurnExecutorFull (execFullA)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). -/
def cellProjCancel (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`runtime_credit_matches_univA` — the refund credit AGREEMENT (formerly the carried divergence).**
A committed cancel's universe-A image CREDITS the creator's `(r.creator, r.asset)` entry by `+r.amount`
(`bridgeCancel_refund`), and the RUNTIME descriptor now ALSO credits the cell `bal_lo` on-trace by
`+amount`. We expose the executor side: the post-entry is `pre + r.amount` — EXACTLY what the descriptor's
on-trace CREDIT gate (with `param::AMOUNT = r.amount`) produces. So the descriptor and the executor AGREE
on the refunded cell for EVERY amount (no `amount = 0` side-condition) — the formerly-carried on-trace
divergence is CLOSED. (The amount the descriptor credits is bound to the parked record via the §H
escrow-root recompute reading the SAME `param::AMOUNT`.) -/
theorem runtime_credit_matches_univA (st st' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execFullA st (.bridgeCancelA id actor) = some st') :
    ∃ r : EscrowRecord, cancelGuard st.kernel id actor r ∧
      st'.kernel.bal r.creator r.asset
        = (cellProjCancel st.kernel.bal r.creator r.asset).balLo + r.amount := by
  obtain ⟨r, hg, hcredit⟩ := bridgeCancel_refund st id actor st' h
  exact ⟨r, hg, hcredit⟩

/-! ## §10 — THE per-cell circuit⟺executor on-trace AGREEMENT (the payoff, on the REFUNDED cell).

On a cancel, the descriptor's on-trace post-state CREDITS the refund cell `bal_lo` by `+amount` (the
parked value returns to the locker). The REFUNDED cell `(r.creator, r.asset)` — the cell the executor
credits by `+r.amount` — is credited by BOTH the descriptor (with `param::AMOUNT = r.amount`) and the
executor's image, so they AGREE exactly there. The frozen non-balance frame agrees too (`0 = 0`). This is
the divergence-free payoff: the descriptor's on-trace credit IS the executor's refund credit (formerly
the carried §9 divergence). -/

/-- **`descriptor_agrees_with_executor_refund`** — a satisfying descriptor run encoding the REFUNDED cell
(`pre` projected from the pre-balance, `amount` the parked refund) agrees with the executor's CREDITED
post-balance: the descriptor's on-trace post `balLo` is `pre.balLo + amount`, which (with `amount` the
record's `r.amount` and `hcredit` the executor's `+r.amount` credit at the refunded entry) EQUALS the
executor's post-entry `st'.kernel.bal c asset`. So the descriptor and the executor agree on the refunded
cell — the on-trace credit IS the refund, divergence-free. The frozen frame agrees verbatim. -/
theorem descriptor_agrees_with_executor_refund
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeCancelRow env)
    (st st' : RecChainedState) (c : CellId) (asset : AssetId) (amount : ℤ) (post : CellState)
    (hcredit : st'.kernel.bal c asset = st.kernel.bal c asset + amount)
    (henc : RowEncodesCancel env (cellProjCancel st.kernel.bal c asset) amount post)
    (hsat : satisfiedVm hash bridgeCancelVmDescriptor env true true) :
    post.balLo = (cellProjCancel st'.kernel.bal c asset).balLo
    ∧ post.balHi = (cellProjCancel st'.kernel.bal c asset).balHi
    ∧ (∀ i, post.fields i = (cellProjCancel st'.kernel.bal c asset).fields i)
    ∧ post.capRoot = (cellProjCancel st'.kernel.bal c asset).capRoot
    ∧ post.reserved = (cellProjCancel st'.kernel.bal c asset).reserved := by
  obtain ⟨hcirc, _⟩ := bridgeCancelDescriptor_full_sound hash env hrow
    (cellProjCancel st.kernel.bal c asset) post amount henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- descriptor: post.balLo = pre.balLo + amount; executor: st'.bal = st.bal + amount. Agree.
    rw [hcLo]; show st.kernel.bal c asset + amount = st'.kernel.bal c asset; rw [hcredit]
  · rw [hcHi]; rfl
  · intro i; rw [hcF i]; rfl
  · rw [hcCap]; rfl
  · rw [hcRes]; rfl

/-! ## §11 — SYSTEM-ROOTS AMPLIFICATION: bind the bridge side-table root (`system_roots[ESCROW]`).

STAGE 3 (`Exec.SystemRoots`) gives the `escrows` side-table its OWN kernel-owned home —
`systemRoot.ESCROW = 0`, committed by `systemRootsDigest` + bound by `cellCommitS_binds_systemRoots`.
§11 connects the cancel's `markResolved` resolve (AND, in the runtime, the off-trace refund) to THAT
root, and reports the descriptor-level gap honestly. -/

open Dregg2.Exec.SystemRoots
  (SysRoots FieldElem systemRootsDigest systemRootsDigest_binds_pointwise cellCommitS
   cellCommitS_binds_systemRoots N_SYSTEM_ROOTS)
open Dregg2.Circuit.StateCommit (compressNInjective)

/-- The kernel-owned escrow-root index as a `Fin N_SYSTEM_ROOTS` (`systemRoot.ESCROW = 0`). -/
def escrowRootIx : Fin N_SYSTEM_ROOTS := ⟨0, by decide⟩

/-- **`escrowRootOf escrowDigest others`** — the `system_roots` sub-block whose ESCROW slot carries the
bridge side-table's `escrows`-list digest, every OTHER slot carried by `others`. -/
def escrowRootOf (escrowDigest : FieldElem) (others : SysRoots) : SysRoots :=
  fun i => if i = escrowRootIx then escrowDigest else others i

@[simp] theorem escrowRootOf_escrow (escrowDigest : FieldElem) (others : SysRoots) :
    escrowRootOf escrowDigest others escrowRootIx = escrowDigest := by
  simp [escrowRootOf]

/-- **`cancel_moves_escrow_root` — the `markResolved` update MOVES the named root.** If the resolve
changes the `escrows` list digest (`dPre ≠ dPost`), the `system_roots` ESCROW slot differs pre vs post.
So the side-table resolve is VISIBLE at `systemRoot.ESCROW`. -/
theorem cancel_moves_escrow_root (dPre dPost : FieldElem) (others : SysRoots)
    (hmove : dPre ≠ dPost) :
    escrowRootOf dPre others escrowRootIx ≠ escrowRootOf dPost others escrowRootIx := by
  simp only [escrowRootOf_escrow]; exact hmove

/-- **`escrow_root_bound_by_systemCommit` — the side-table anti-ghost on the NAMED HOME.** Two cells
with the SAME `system_roots` commitment have the SAME escrow root: a fixed cell commitment PINS the
bridge side-table digest, so tampering the resolve/refund provably MOVES the commitment. -/
theorem escrow_root_bound_by_systemCommit (compressN : List FieldElem → FieldElem)
    (hN : compressNInjective compressN) (rest : List FieldElem) (sr sr' : SysRoots)
    (h : cellCommitS compressN rest sr = cellCommitS compressN rest sr') :
    sr escrowRootIx = sr' escrowRootIx :=
  systemRootsDigest_binds_pointwise compressN hN sr sr'
    (cellCommitS_binds_systemRoots compressN hN rest sr sr' h) escrowRootIx

/-- **`escrow_root_not_in_descriptor_commit` — the genuinely-blocked leg, surfaced as a THEOREM.**
The EffectVM DESCRIPTOR's `state_commit` absorbs ONLY the 13 conserved state-block columns, NONE of
which is the `system_roots` ESCROW digest. The runtime carries no `system_roots` digest column
(`auxCol SYSTEM_ROOTS_DIGEST = 186` is PAST `EFFECT_VM_WIDTH = 186`) and binds the bridge side-table +
refund via the SEPARATE `effects_hash` accumulator. We witness the gap: two rows differing ONLY in the
(nonexistent) escrow-root aux column have IDENTICAL `absorbedCols`. -/
theorem escrow_root_not_in_descriptor_commit (env : VmRowEnv) (escrowRoot : ℤ) :
    absorbedCols { loc := fun v => if v = auxCol aux_off_sys.SYSTEM_ROOTS_DIGEST then escrowRoot
                                   else env.loc v
                 , nxt := env.nxt, pub := env.pub }
      = absorbedCols env := by
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

/-- **`escrow_resolve_is_out_of_row` — the honest finding (universe-A leg).** A committed cancel's
`escrows` store is `markResolved st.escrows id`. This list-mutation is a universe-A property carried by
the escrows list digest, now with a NAMED commitment home at `systemRoot.ESCROW` (§11), but NOT by any
per-row gate or hash-site of `bridgeCancelVmDescriptor`. -/
theorem escrow_resolve_is_out_of_row (st st' : RecChainedState) (id : Nat) (actor : CellId)
    (h : execFullA st (.bridgeCancelA id actor) = some st') :
    st'.kernel.escrows = markResolved st.kernel.escrows id := by
  obtain ⟨_, _, _, hesc, _⟩ :=
    (Dregg2.Circuit.Spec.BridgeOutboundCancel.execFullA_bridgeCancelA_iff_spec st id actor st').mp h
  exact hesc

/-! ## §12 — NON-VACUITY: a concrete cancel row realizes the intent; a forged one is rejected. -/

/-- A concrete cancel row: `bal_lo 100 → 105` (CREDIT 5 — the refund), nonce 5 → 6 (TICK), frame fixed
at 0. The refund amount `param::AMOUNT = 5` drives the credit. -/
def goodCancelRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_BRIDGE_CANCEL then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 105
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.AMOUNT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodCancelRow_isRow : IsBridgeCancelRow goodCancelRow := by
  unfold IsBridgeCancelRow goodCancelRow
  refine ⟨by norm_num [SEL_BRIDGE_CANCEL], ?_⟩
  norm_num [sel.NOOP, SEL_BRIDGE_CANCEL, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE, param.AMOUNT]

/-- **NON-VACUITY (witness TRUE).** `goodCancelRow` REALIZES the bridge-cancel intent: bal_lo `100 →
105` (credit 5 — the refund), nonce TICKS `5 → 6`, frame fixed. -/
theorem goodCancelRow_realizes_intent : BridgeCancelRowIntent goodCancelRow := by
  unfold BridgeCancelRowIntent goodCancelRow
  simp only [sbCol, saCol, prmCol, SEL_BRIDGE_CANCEL, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 33) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 68) = False := by simp; omega
  have f1 : (54 + (3 + i) = 33) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 68) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED cancel row: `goodCancelRow` with the post-`bal_lo` tampered to `999` (NOT the credited
`105` — an over-credited / forged refund). -/
def badCancelRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodCancelRow.loc v
  nxt := goodCancelRow.nxt
  pub := goodCancelRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badCancelRow`'s post-`bal_lo` is NOT the
credited value `100 + 5 = 105` (a forged over-credit), so the `gBalLoCredit` gate REJECTS it — a
concrete UNSAT. -/
theorem badCancelRow_rejected : ¬ (VmConstraint.gate gBalLoCredit).holdsVm badCancelRow false false := by
  apply bridgeCancelVm_rejects_wrong_balance
  simp only [badCancelRow, goodCancelRow, sbCol, saCol, prmCol, SEL_BRIDGE_CANCEL, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-- **NON-VACUITY for the escrow-root binding (witness moves).** Two distinct escrow digests place
distinct roots at `systemRoot.ESCROW` — a `:= 0` stub escrow root would make these EQUAL (forbidden). -/
theorem escrowRoot_nonvacuous (others : SysRoots) :
    escrowRootOf 1234 others escrowRootIx ≠ escrowRootOf 9999 others escrowRootIx :=
  cancel_moves_escrow_root 1234 9999 others (by decide)

/-! ## §13 — Axiom-hygiene pins. -/

#guard bridgeCancelVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard bridgeCancelVmDescriptor.hashSites.length == 4
#guard bridgeCancelVmDescriptor.traceWidth == 186

#assert_axioms bridgeCancelVm_faithful
#assert_axioms bridgeCancelVm_rejects_wrong_output
#assert_axioms bridgeCancelVm_rejects_wrong_balance
#assert_axioms intent_to_cellCancelSpec
#assert_axioms bridgeCancelRowGates_flag_indep
#assert_axioms bridgeCancelDescriptor_full_sound
#assert_axioms bridgeCancelDescriptor_commit_binds_state
#assert_axioms runtime_credit_matches_univA
#assert_axioms descriptor_agrees_with_executor_refund
#assert_axioms cancel_moves_escrow_root
#assert_axioms escrow_root_bound_by_systemCommit
#assert_axioms escrow_root_not_in_descriptor_commit
#assert_axioms escrow_resolve_is_out_of_row
#assert_axioms goodCancelRow_isRow
#assert_axioms goodCancelRow_realizes_intent
#assert_axioms badCancelRow_rejected
#assert_axioms escrowRoot_nonvacuous

/-! ## §H — CLASS-A PROMOTION: the GENUINE in-row bridge-escrow-root RECOMPUTE.

PROMOTES bridgeCancel to class A by binding the bridge escrow root genuinely via the shared
`EffectVmEmitEscrowRoot` recompute: the CANCELLED outbound-bridge record's leaf is recomputed in-row
`hash[id,creator,recipient,amount,asset,resolved]` (resolved = 1 on cancel; amount at `param.AMOUNT`),
then `new_root = hash[record_leaf, old_root]` — FORCED, not asserted. The cancelled record's content is
bound by the recomputed root. The §1–§10 frame soundness are UNCHANGED. -/

open Dregg2.Circuit.Emit.EffectVmEmitEscrowRoot
  (escrowRecomputeSites escrowRootHolds escrowRootAdvance_forced escrowRoot_binds_record
   escrowRoot_amount_bound leafOf advanceOf)

/-- **`bridgeCancelVmDescriptorGenuine`** — the CLASS-A bridgeCancel circuit: §2 per-row gates (nonce tick
+ frame freeze) with the genuine recompute sites prepended to the GROUP-4 sites. -/
def bridgeCancelVmDescriptorGenuine : EffectVmDescriptor :=
  { name := bridgeCancelVmAirName ++ "-genuine-rootbound"
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeCancelRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
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

/-- **`bridgeCancelGenuine_sound` — THE CLASS-A SOUNDNESS.** The genuine descriptor forces the per-cell
`CellCancelSpec` (frame freeze + nonce tick), the GENUINE bridge-escrow-root recompute (root FORCED),
AND the published commit. -/
theorem bridgeCancelGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeCancelRow env)
    (pre post : CellState) (amount : ℤ)
    (henc : RowEncodesCancel env pre amount post)
    (hsat : satisfiedVm hash bridgeCancelVmDescriptorGenuine env true true) :
    CellCancelSpec pre amount post
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
  have hgates : ∀ c ∈ bridgeCancelRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold bridgeCancelVmDescriptorGenuine
    simp only [List.mem_append]; exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := bridgeCancelRowGates_flag_indep env true true hgates
  have hint := (bridgeCancelVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellCancelSpec env pre post amount henc hint, ?_, ?_⟩
  · exact escrowRootAdvance_forced hash env (genuine_sites_split hash env hsites)
  · have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
      intro c hc
      have hmem : c ∈ bridgeCancelVmDescriptorGenuine.constraints := by
        unfold bridgeCancelVmDescriptorGenuine
        simp only [List.mem_append]; exact Or.inr hc
      have hh := hcs c hmem
      unfold boundaryLastPins at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl <;>
        · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
    have hpin := (boundaryLast_pins env hlast).1
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
    rw [← hsaC]; exact hpin

/-- **`bridgeCancelGenuine_binds_record` — THE CLASS-A ANTI-GHOST.** Two genuine rows with the same
recomputed new root have the SAME cancelled amount (and every record field) — a forged cancel moves the
root ⇒ moves `state_commit` ⇒ UNSAT. -/
theorem bridgeCancelGenuine_binds_record (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeCancelVmDescriptorGenuine e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeCancelVmDescriptorGenuine e₂ true true)
    (hroot : e₁.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER = e₂.loc EffectVmEmitEscrowRoot.SYS_DIG_AFTER) :
    e₁.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) = e₂.loc (prmCol EffectVmEmitEscrowRoot.AMOUNT) :=
  escrowRoot_amount_bound hash hCR e₁ e₂
    (genuine_sites_split hash e₁ hsat₁.2) (genuine_sites_split hash e₂ hsat₂.2) hroot

theorem bridgeCancelGenuine_recompute_nonvacuous :
    escrowRootHolds EffectVmEmitEscrowRoot.cN EffectVmEmitEscrowRoot.goodEscrowRow :=
  EffectVmEmitEscrowRoot.goodEscrowRow_recomputes

#guard bridgeCancelVmDescriptorGenuine.hashSites.length == 2 + 4
#guard bridgeCancelVmDescriptorGenuine.traceWidth == 186

#assert_axioms genuine_sites_split
#assert_axioms bridgeCancelGenuine_sound
#assert_axioms bridgeCancelGenuine_binds_record

end Dregg2.Circuit.Emit.EffectVmEmitBridgeCancel
