/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeLock — the bridgeLock (bridge-outbound-LOCK) effect's
concrete EffectVM circuit, EMITTED through the SAME `EffectVmEmit` IR as transfer.

This is the bridge-group analogue of `EffectVmEmitTransfer` + `…TransferSound` + `…TransferUnify`,
built for `bridgeLockA`. Universe A (`Inst/bridgeLockA.lean`, `Spec/bridgeoutboundlock.lean`) carries
the FULL-state soundness `bridgeLockA_full_sound ⇒ BridgeOutboundLockSpec`: a committed lock DEBITS
the per-asset ledger `bal` at `(originator, asset)` by `amount`, PREPENDS an unresolved bridge-tagged
`EscrowRecord` onto `escrows`, advances the log, and FREEZES the other 15 kernel fields.

## What the EffectVM IR (a 14-column state block + GROUP-4 commitment) DOES support for bridgeLock

The conserved `bal` move is a SINGLE-cell single-asset DEBIT (`recBalCreditCell … (-amount)`): on the
EffectVM row this is the originator cell's `state.BALANCE_LO` limb moving DOWN by `amount`. This is
EXACTLY the transfer-row DEBIT leg (`direction = 1`, `signedMove = −amount`), so the IR carries it
totally — and the GROUP-4 commitment chain binds the whole after-state block (balance/nonce/fields/
cap_root) into `state_commit` exactly as for transfer.

The ONE column difference from transfer: bridgeLock's executor does NOT tick the cell's nonce
(`bridgeLockKAsset`/`createBridgeRawAsset` rewrite only `bal` and `escrows`; the cell record's `nonce`
field survives), whereas the transfer EffectVM row ticks `+1`. So the bridgeLock descriptor FREEZES
the nonce (`gNonceFreeze`), matching the executor — the `CellTransferSpecFrozenNonce` shape the
connector already validated as `recKExec`'s genuine per-cell image.

## THE IR-EXTENSION FLAG (the escrows set-membership leg)

`BridgeOutboundLockSpec` ALSO prepends a `parkedBridgeRecord` onto the `escrows` list — a
SET-MEMBERSHIP / list-digest update. The EffectVM 14-column state block (`state.BALANCE_LO/HI`,
`state.NONCE`, the 8 `state.FIELD_BASE+i`, `state.CAP_ROOT`, `state.STATE_COMMIT`, `state.RESERVED`)
has NO escrow-root column, and the GROUP-4 hash-sites absorb NONE of the escrows list. So the IR as it
stands CANNOT bind the escrows update into `state_commit`.

  ⇒ **needs IR extension: an escrows-list-root column in the EffectVM state block (a 15th data column,
     or repurposing one named field as `ESCROW_ROOT`) absorbed by a new hash-site, so the prepended
     bridge record is bound into the published `state_commit`.** Universe A binds it via the
     `escrowsComponent` list digest (`listLeafInjective LE` + `compressNInjective cN`); the EffectVM
     row has no counterpart column. This module proves what the IR DOES support (balance debit + the
     14-column commitment) and reports the escrows binding as out-of-IR — NOT papered.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.bridgeoutboundlock

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeLock

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   site0 site1 site2 site3 transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols commitOf commit_eq_commitOf absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The bridgeLock selector + the debit parameter.

The EffectVM layout names only `sel.NOOP = 0` and `sel.TRANSFER = 1`; the bridge-outbound-lock effect
takes the NEXT selector column (a LAYOUT CHOICE local to this descriptor — the running prover's
`columns.rs` would assign it; we keep the index explicit so the emitted gates are selector-specialized
exactly as the transfer template specializes on `s_transfer`). The lock's balance move is a FIXED
DEBIT by `param.AMOUNT` (no direction param — a lock always debits), so we emit the debit-specialized
balance gate directly. -/

/-- The bridge-outbound-lock selector column index (next after `sel.TRANSFER`). -/
def SEL_BRIDGE_LOCK : Nat := 2

/-- The lock row is a bridge-lock row: `s_bridge_lock = 1`, `s_noop = 0`. -/
def IsBridgeLockRow (env : VmRowEnv) : Prop :=
  env.loc SEL_BRIDGE_LOCK = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The bridgeLock per-row gate bodies (debit + full frame freeze, term-for-term).

* `gBalLoDebit` — `new_bal_lo − old_bal_lo + amount = 0`, i.e. the limb DROPS by `amount` (the
  `recBalCreditCell … (-amount)` debit projected to the row).
* `gNonceFreeze` — `new_nonce − old_nonce = 0` (FROZEN; the executor does NOT tick the nonce on a
  lock — the ONE column difference from the transfer row).
* `gBalHi`/`gCapPass`/`gResPass`/`gFieldPass i` — REUSED from the transfer template (bal_hi, cap_root,
  reserved, and the 8 fields all frozen — identical polynomials). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + amount`. On a lock row this vanishes iff the
limb drops by exactly `amount`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (ePrm param.AMOUNT)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the lock leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted bridgeLock descriptor. -/

/-- The bridge-outbound-lock AIR identity. -/
def bridgeLockVmAirName : String := "dregg-effectvm-bridgelock-v1"

/-- The bridge-lock per-row gates: balance debit, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def bridgeLockRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`bridgeLockVmDescriptor`** — the bridgeLock effect's concrete EffectVM circuit: the per-row
debit/freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4
hash sites (REUSED — the post-state commitment chain is the SAME 14-column binding) and the 2
balance-limb range checks. -/
def bridgeLockVmDescriptor : EffectVmDescriptor :=
  { name := bridgeLockVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeLockRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The bridgeLock ROW INTENT (the independent faithfulness target).

`BridgeLockRowIntent env`: on a lock row, the new balance is the old balance MINUS `amount` (the
debit), the hi limb / nonce / whole frame (cap/reserved/8 fields) are FIXED. This is the EffectVM-row
projection of the conserved `bal` debit (`recBalCreditCell … (-amount)`) + nonce-freeze + frame-freeze
that `BridgeOutboundLockSpec`'s `bal` clause + frame demand on the originator cell. -/

/-- **`BridgeLockRowIntent env`** — the intended bridge-lock move on the row `env.loc`. -/
def BridgeLockRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`bridgeLockVm_faithful`.** On a bridge-lock row, the emitted descriptor's per-row gates all hold
IFF `BridgeLockRowIntent` holds — the gates pin EXACTLY the debit + nonce-freeze + frame-freeze move. -/
theorem bridgeLockVm_faithful (env : VmRowEnv) :
    (∀ c ∈ bridgeLockRowGates, c.holdsVm env false false) ↔ BridgeLockRowIntent env := by
  unfold bridgeLockRowGates gFieldPassAll BridgeLockRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoDebit) (by simp)
    have hHi := h (.gate gBalHi) (by simp)
    have hNon := h (.gate gNonceFreeze) (by simp)
    have hCap := h (.gate gCapPass) (by simp)
    have hRes := h (.gate gResPass) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldPass i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoDebit, gBalHi, gNonceFreeze, gCapPass, gResPass,
      eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
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

/-! ## §5 — ANTI-GHOST: a wrong-output lock row fails the emitted descriptor. -/

/-- **Anti-ghost (general).** A lock row whose post-state is NOT the intent move (wrong debit, ticked
nonce, tampered frame) does NOT satisfy the per-row gates. -/
theorem bridgeLockVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ BridgeLockRowIntent env) :
    ¬ (∀ c ∈ bridgeLockRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((bridgeLockVm_faithful env).mp h)

/-- **Anti-ghost (balance tamper).** A lock row whose post-`bal_lo` is NOT the debit has no satisfying
gate set — the `gBalLoDebit` gate alone rejects it (UNSAT). -/
theorem bridgeLockVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + the keystone soundness (REUSING `CellState`). -/

/-- The transfer parameters carried in the param block (only `amount` matters for a lock). -/
structure LockParams where
  amount : ℤ

/-- `RowEncodesLock env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition (the lock's `RowEncodes` analogue: no `direction` column). -/
def RowEncodesLock (env : VmRowEnv) (pre : CellState) (p : LockParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = p.amount
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellLockSpec pre p post`** — the per-cell FULL-state lock spec: the moved cell's `balLo` drops
by `amount`, the nonce is FROZEN, and the WHOLE frame (balHi, the 8 fields, capRoot, reserved) is
LITERALLY unchanged. This is the EffectVM-row projection of `BridgeOutboundLockSpec`'s `bal` debit +
frame freeze on the originator cell. -/
def CellLockSpec (pre : CellState) (p : LockParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.amount
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
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
  · have : post.balLo = pre.balLo - env.loc (prmCol param.AMOUNT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i
    have := hfld i.val i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-! ## §7 — The full descriptor soundness (gates + boundary) + the commitment binding (REUSED). -/

/-- **`bridgeLockDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor (gates +
transitions + boundaries + hash sites), under the `RowEncodesLock` decoding, forces the structured
per-cell `CellLockSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. -/
theorem bridgeLockDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : LockParams)
    (henc : RowEncodesLock env pre p post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptor env true true) :
    CellLockSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  -- per-row intent from the gates
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ bridgeLockRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ bridgeLockVmDescriptor.constraints := by
      unfold bridgeLockVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold bridgeLockRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (bridgeLockVm_faithful env).mp hgates'
  refine ⟨intent_to_cellLockSpec env pre post p henc hint, ?_⟩
  -- last-row boundary pin: state_after.state_commit = PI[NEW_COMMIT]
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
  -- post.commit = env.loc (saCol STATE_COMMIT) = env.pub NEW_COMMIT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact hpin

/-! ## §8 — The anti-ghost commitment tooth (REUSED from the transfer keystone, hash sites identical).

`bridgeLockVmDescriptor.hashSites = transferHashSites`, so the keystone's
`absorbed_determined_by_commit` applies verbatim: under `Poseidon2SpongeCR hash`, two satisfying lock
rows with the SAME published `NEW_COMMIT` agree on their WHOLE absorbed after-state block. -/

/-- **`bridgeLockDescriptor_commit_binds_state`** — the keystone anti-ghost for bridgeLock: two
descriptor-satisfying lock rows publishing the SAME `NEW_COMMIT` have identical absorbed state-block
columns (balance limbs, nonce, all 8 fields, cap_root). So a prover cannot keep `NEW_COMMIT` while
tampering any absorbed cell of the locked-out post-state. -/
theorem bridgeLockDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash bridgeLockVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash bridgeLockVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  -- each row's published state_commit equals its NEW_COMMIT (last-row boundary pin)
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

`bridgeLockA_full_sound ⇒ BridgeOutboundLockSpec` carries the `bal` debit at `(originator, asset)`.
We project ONE cell of the kernel `bal` ledger into the keystone `CellState` (the conserved `balLo`
limb reads the per-asset entry `bal originator asset`; the EffectVM limbs with no universe-A analogue
— balHi/fields/capRoot/reserved — are `0`, FROZEN), and prove the originator cell's projection
satisfies `CellLockSpec` EXACTLY (the debit + nonce-freeze + frame-freeze).

The DIVERGENCE pattern: the escrows-list prepend is NOT in this per-cell projection (no escrow column
in the EffectVM block — the §IR-extension flag). And `BridgeOutboundLockSpec`'s `bal` clause is a
WHOLE-function equality `bal' = recBalCreditCell …`; the per-cell projection reads the `(originator,
asset)` entry of it. -/

open Dregg2.Exec (RecordKernelState CellId AssetId recBalCreditCell)
open Dregg2.Circuit.Spec.BridgeOutboundLock (createBridgeKAsset_correct)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState` (the conserved
`balLo` limb). The other EffectVM limbs have no universe-A analogue on the conserved ledger entry, so
they are `0` (frozen). -/
def cellProjLock (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_lock_debit`** — the originator cell's projected `(originator, asset)` ledger entry,
across a committed `BridgeOutboundLockSpec` post-state, satisfies the keystone's `CellLockSpec`
EXACTLY: `balLo` drops by `amount`; balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen.
So `CellLockSpec` IS `BridgeOutboundLockSpec`'s per-cell `bal` image — NOT a fourth spec. -/
theorem unify_lock_debit (st st' : RecChainedState) (id : Nat)
    (actor originator destination : CellId) (asset : AssetId) (amount : ℤ)
    (hspec : Dregg2.Circuit.Spec.BridgeOutboundLock.BridgeOutboundLockSpec
      st id actor originator destination asset amount st') :
    CellLockSpec (cellProjLock st.kernel.bal originator asset) ⟨amount⟩
      (cellProjLock st'.kernel.bal originator asset) := by
  obtain ⟨_, hbal, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal originator asset = st.kernel.bal originator asset - amount
  rw [hbal]
  exact (createBridgeKAsset_correct st.kernel id originator destination asset amount).1

/-! ## §10 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_lock`** — a satisfying run of the runnable descriptor encoding
the originator cell of a committed lock agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre − amount) equals the executor's debited `bal originator asset`,
and the frozen frame agrees. The escrows-list update is out-of-IR (reported as the §IR flag). -/
theorem descriptor_agrees_with_executor_lock
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id : Nat) (actor originator destination : CellId)
    (asset : AssetId) (amount : ℤ) (post : CellState)
    (henc : RowEncodesLock env (cellProjLock st.kernel.bal originator asset) ⟨amount⟩ post)
    (hsat : satisfiedVm hash bridgeLockVmDescriptor env true true)
    (hspec : Dregg2.Circuit.Spec.BridgeOutboundLock.BridgeOutboundLockSpec
      st id actor originator destination asset amount st') :
    post.balLo = (cellProjLock st'.kernel.bal originator asset).balLo
    ∧ post.balHi = (cellProjLock st'.kernel.bal originator asset).balHi
    ∧ (∀ i, post.fields i = (cellProjLock st'.kernel.bal originator asset).fields i)
    ∧ post.capRoot = (cellProjLock st'.kernel.bal originator asset).capRoot
    ∧ post.reserved = (cellProjLock st'.kernel.bal originator asset).reserved := by
  obtain ⟨hcirc, _⟩ := bridgeLockDescriptor_full_sound hash env
    (cellProjLock st.kernel.bal originator asset) post ⟨amount⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_lock_debit st st' id actor originator destination asset amount hspec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]; rfl
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §11 — NON-VACUITY: a concrete lock row realizes the intent; a forged one is rejected. -/

/-- A concrete lock row: `bal_lo 100 → 95` (debit 5), nonce 5 → 5 (FROZEN), frame fixed at 0. -/
def goodLockRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_BRIDGE_LOCK then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 95
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.AMOUNT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodLockRow` REALIZES the bridge-lock intent: bal_lo `100 → 95`
(debit 5), nonce frozen `5 → 5`, frame fixed. -/
theorem goodLockRow_realizes_intent : BridgeLockRowIntent goodLockRow := by
  unfold BridgeLockRowIntent goodLockRow
  simp only [sbCol, saCol, prmCol, SEL_BRIDGE_LOCK, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi
    have e1 : (76 + (3 + i) = 2) = False := by simp; omega
    have e2 : (76 + (3 + i) = 54) = False := by simp; omega
    have e3 : (76 + (3 + i) = 76) = False := by simp
    have e4 : (76 + (3 + i) = 56) = False := by simp; omega
    have e5 : (76 + (3 + i) = 78) = False := by simp; omega
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 2) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
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
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §12 — Axiom-hygiene pins. -/

#guard bridgeLockVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard bridgeLockVmDescriptor.hashSites.length == 4
#guard bridgeLockVmDescriptor.traceWidth == 186

#assert_axioms bridgeLockVm_faithful
#assert_axioms bridgeLockVm_rejects_wrong_output
#assert_axioms bridgeLockVm_rejects_wrong_balance
#assert_axioms intent_to_cellLockSpec
#assert_axioms bridgeLockDescriptor_full_sound
#assert_axioms bridgeLockDescriptor_commit_binds_state
#assert_axioms unify_lock_debit
#assert_axioms descriptor_agrees_with_executor_lock
#assert_axioms goodLockRow_realizes_intent
#assert_axioms badLockRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitBridgeLock
