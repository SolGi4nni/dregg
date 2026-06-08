/-
# Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue — the `queueEnqueueA` (FIFO append + refundable deposit
PARK) effect's EffectVM emission, through the SAME `EffectVmEmit` IR as transfer.

Universe A (`Inst/queueEnqueueA.lean`, `Spec/queuefifocore.lean`) carries the FULL-state soundness
`queueEnqueueA_full_sound ⇒ QueueEnqueueSpec`: a committed enqueue APPENDS a message to queue `id`'s
FIFO buffer (`queueEnqueueK`), DEBITS the per-asset ledger `bal` at `(actor, dAsset)` by `deposit`, and
PREPENDS an unresolved deposit `EscrowRecord` onto `escrows` (`createEscrowRawAssetQueue`), advances the
log, and FREEZES the other 14 kernel fields.

## What the EffectVM IR (a 14-column per-cell state block + GROUP-4 commitment) DOES support

The conserved `bal` move is a SINGLE-cell single-asset DEBIT: `createEscrowRawAssetQueue` rewrites
`bal := recBalCreditCell k₁.bal actor dAsset (-deposit)` — the `(actor, dAsset)` ledger entry drops by
`deposit`. On the EffectVM row this is the actor cell's `state.BALANCE_LO` limb moving DOWN by `deposit`
— EXACTLY the bridge-lock / transfer-DEBIT leg (`signedMove = −deposit`). The IR carries it totally, and
the GROUP-4 commitment chain binds the whole after-state block (balance/nonce/fields/cap_root) into
`state_commit` exactly as for transfer. The nonce is FROZEN (the executor does NOT tick it — the deposit
park rewrites only `bal` + `escrows`; the cell record's `nonce` survives), matching the
`CellTransferSpecFrozenNonce` shape the connector already validated as `recKExec`'s per-cell image.

## THE IR-EXTENSION FLAGS (the FIFO append + the escrows-park set-membership legs)

`QueueEnqueueSpec` ALSO (1) APPENDS the message to the FIFO buffer (`queueEnqueueK` — a list-ORDER
update on `queues`, capacity-gated `buffer.length < capacity`), and (2) PREPENDS the deposit record onto
`escrows` (a list-digest update). Both are MERKLE/LIST-ACCUMULATOR MEMBERSHIP+ORDER properties universe A
binds via `listComponent`/`listDigest`. The EffectVM 14-column state block has NO queue-buffer-root and
NO escrows-root column, and the GROUP-4 hash-sites absorb NEITHER list. So the IR CANNOT bind the FIFO
append OR the escrow park into `state_commit`, and CANNOT express the FIFO ORDER / capacity bound.

  ⇒ **needs IR extension: (a) a queue-buffer-root column absorbed by a NEW merkle/list-accumulator
     hash-site (so the appended message + the preserved buffer ORDER + the capacity bound
     `buffer.length < capacity` is bound into `state_commit`); and (b) an escrows-root column absorbed
     by a hash-site (so the prepended deposit record is bound). The current IR has NO list-accumulator
     gate-kind and NO membership-update form — only gate/transition/boundary/piBinding/hashSite
     (fixed-arity-per-row)/range.**

`queueEnqueueA` is therefore **PARTIAL**: the deposit DEBIT (the conserved `bal` move) is FULLY in IR; the
FIFO append and the escrows park are out-of-IR. This module proves what the IR DOES support (the debit +
14-column commitment) and reports both list legs precisely — NOT papered, NOT faked.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.queuefifocore

namespace Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub gBalHi gCapPass gResPass gFieldPass gFieldPassAll
   transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites transferHash_binds boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols absorbed_determined_by_commit)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option linter.unusedVariables false

/-! ## §0 — The queueEnqueue selector + the deposit DEBIT parameter. -/

/-- The queueEnqueue selector column index (a LAYOUT CHOICE local to this descriptor). -/
def SEL_QUEUE_ENQUEUE : Nat := 5

/-- The enqueue row: `s_queue_enqueue = 1`, `s_noop = 0`. -/
def IsQueueEnqueueRow (env : VmRowEnv) : Prop :=
  env.loc SEL_QUEUE_ENQUEUE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §1 — The per-row gate bodies (deposit DEBIT + full frame freeze, nonce freeze). -/

/-- Balance-lo DEBIT body: `new_bal_lo − old_bal_lo + amount`. The deposit (`param.AMOUNT`) leaves the
actor's ledger entry: the limb DROPS by exactly `deposit`. -/
def gBalLoDebit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (ePrm param.AMOUNT)

/-- Nonce-FREEZE body: `new_nonce − old_nonce` (the deposit park leaves the nonce untouched). -/
def gNonceFreeze : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)

/-! ## §2 — The emitted queueEnqueue descriptor. -/

/-- The queueEnqueue AIR identity. -/
def queueEnqueueVmAirName : String := "dregg-effectvm-queueenqueue-v1"

/-- The enqueue per-row gates: balance debit, bal_hi freeze, nonce freeze, cap/reserved freeze,
8 fields freeze. -/
def queueEnqueueRowGates : List VmConstraint :=
  [ .gate gBalLoDebit, .gate gBalHi, .gate gNonceFreeze
  , .gate gCapPass, .gate gResPass ] ++ gFieldPassAll

/-- **`queueEnqueueVmDescriptor`** — the IR-supportable part of queueEnqueue: the per-row deposit-debit
+ freeze gates ++ transition continuity ++ the 7 boundary PI pins, with the 4 ordered GROUP-4 hash sites
and the 2 balance-limb range checks. The FIFO append + escrows park are OUT-OF-IR. -/
def queueEnqueueVmDescriptor : EffectVmDescriptor :=
  { name := queueEnqueueVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := queueEnqueueRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The queueEnqueue ROW INTENT (the IR-supportable faithfulness target: deposit debit). -/

/-- **`QueueEnqueueRowIntent env`** — the IR-supportable enqueue move: the actor cell's `bal_lo` drops
by `deposit` (the park), the hi limb / nonce / whole frame are FIXED. -/
def QueueEnqueueRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the (IR-supportable) intent. -/

/-- **`queueEnqueueVm_faithful`.** On an enqueue row, the emitted descriptor's per-row gates all hold
IFF `QueueEnqueueRowIntent` holds — the gates pin EXACTLY the deposit debit + nonce-freeze + frame-freeze. -/
theorem queueEnqueueVm_faithful (env : VmRowEnv) :
    (∀ c ∈ queueEnqueueRowGates, c.holdsVm env false false) ↔ QueueEnqueueRowIntent env := by
  unfold queueEnqueueRowGates gFieldPassAll QueueEnqueueRowIntent
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

/-! ## §5 — ANTI-GHOST. -/

theorem queueEnqueueVm_rejects_wrong_output (env : VmRowEnv)
    (hwrong : ¬ QueueEnqueueRowIntent env) :
    ¬ (∀ c ∈ queueEnqueueRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((queueEnqueueVm_faithful env).mp h)

theorem queueEnqueueVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) - env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoDebit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith [h]

/-! ## §6 — The structured per-cell spec + descriptor soundness (REUSING `CellState`). -/

/-- The deposit parameter carried in the param block. -/
structure DepositParams where
  deposit : ℤ

/-- `RowEncodesDebit env pre p post` ties the row's state-block + param columns to a `(pre, p, post)`
cell transition (the deposit's `RowEncodes`: a single `deposit` param). -/
def RowEncodesDebit (env : VmRowEnv) (pre : CellState) (p : DepositParams) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = p.deposit
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

/-- **`CellDebitSpec pre p post`** — the per-cell FULL-state deposit-debit spec: the actor cell's `balLo`
drops by `deposit`, the nonce is FROZEN, and the whole frame is LITERALLY unchanged. The EffectVM-row
projection of `QueueEnqueueSpec`'s `bal` debit + frame freeze on the actor cell. -/
def CellDebitSpec (pre : CellState) (p : DepositParams) (post : CellState) : Prop :=
  post.balLo = pre.balLo - p.deposit
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

theorem intent_to_cellDebitSpec (env : VmRowEnv) (pre post : CellState) (p : DepositParams)
    (henc : RowEncodesDebit env pre p post) (hint : QueueEnqueueRowIntent env) :
    CellDebitSpec pre p post := by
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

/-- **`queueEnqueueDescriptor_full_sound`** — satisfying the WHOLE runnable descriptor forces the
per-cell `CellDebitSpec` AND publishes the post-commit as `PI[NEW_COMMIT]`. (FIFO append + escrows park
are out-of-IR.) -/
theorem queueEnqueueDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (p : DepositParams)
    (henc : RowEncodesDebit env pre p post)
    (hsat : satisfiedVm hash queueEnqueueVmDescriptor env true true) :
    CellDebitSpec pre p post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _⟩ := hsat
  have hgates' : ∀ c ∈ queueEnqueueRowGates, c.holdsVm env false false := by
    intro c hc
    have hmem : c ∈ queueEnqueueVmDescriptor.constraints := by
      unfold queueEnqueueVmDescriptor
      simp only [List.mem_append]
      exact Or.inl (Or.inl (Or.inl hc))
    have := hcs c hmem
    unfold queueEnqueueRowGates gFieldPassAll at hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
      simpa only [VmConstraint.holdsVm] using this
  have hint := (queueEnqueueVm_faithful env).mp hgates'
  refine ⟨intent_to_cellDebitSpec env pre post p henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ queueEnqueueVmDescriptor.constraints := by
      unfold queueEnqueueVmDescriptor
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

/-! ## §7 — The anti-ghost commitment tooth (REUSED — hash sites identical to transfer). -/

theorem queueEnqueueDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsat₁ : satisfiedVm hash queueEnqueueVmDescriptor e₁ true true)
    (hsat₂ : satisfiedVm hash queueEnqueueVmDescriptor e₂ true true)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ := by
  have hs₁ : siteHoldsAll hash e₁ transferHashSites := hsat₁.2
  have hs₂ : siteHoldsAll hash e₂ transferHashSites := hsat₂.2
  have hc : ∀ (e : VmRowEnv), satisfiedVm hash queueEnqueueVmDescriptor e true true →
      e.loc (saCol state.STATE_COMMIT) = e.pub pi.NEW_COMMIT := by
    intro e hsat
    obtain ⟨hcs, _⟩ := hsat
    have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm e false true := by
      intro c hc
      have hmem : c ∈ queueEnqueueVmDescriptor.constraints := by
        unfold queueEnqueueVmDescriptor
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

/-! ## §8 — CONNECTOR to universe-A: the deposit DEBIT IS `QueueEnqueueSpec`'s per-cell `bal` image.

`QueueEnqueueSpec` commits `st'.kernel = createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit
id m` off the FIFO-appended intermediate `k₁` (where `queueEnqueueK st.kernel id m = some k₁`). That
helper rewrites `bal := recBalCreditCell k₁.bal actor dAsset (-deposit)` — the `(actor, dAsset)` ledger
entry drops by `deposit`. Since `queueEnqueueK` is balance-NEUTRAL (`k₁.bal = st.kernel.bal`), the
projected actor-cell `balLo` drops `pre − deposit`. We prove the originator cell's projection satisfies
`CellDebitSpec` EXACTLY. The FIFO append + escrows park are out-of-IR. -/

open Dregg2.Circuit.Spec.QueueFifoCore
open Dregg2.Exec

/-- `queueEnqueueK` is balance-preserving on the raw `bal` function (it rewrites only `queues`). -/
theorem queueEnqueueK_bal {k k₁ : RecordKernelState} {id m : Nat}
    (h : queueEnqueueK k id m = some k₁) : k₁.bal = k.bal := by
  unfold queueEnqueueK at h
  cases hf : findQueue k.queues id with
  | none   => simp only [hf] at h; exact absurd h (by simp)
  | some q =>
      simp only [hf] at h
      by_cases hc : q.buffer.length < q.capacity
      · rw [if_pos hc] at h; simp only [Option.some.injEq] at h; subst h; rfl
      · rw [if_neg hc] at h; exact absurd h (by simp)

/-- Project the `(c, asset)` per-asset ledger entry into the keystone `CellState`'s `balLo` limb. -/
def cellProjBal (bal : CellId → AssetId → ℤ) (c : CellId) (asset : AssetId) : CellState where
  balLo    := bal c asset
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_enqueue_debit`** — across a committed `QueueEnqueueSpec` post-state, the actor cell's
projected `(actor, dAsset)` ledger entry satisfies the keystone's `CellDebitSpec` EXACTLY: `balLo` drops
by `deposit`; balHi/fields/capRoot/reserved frozen (`0 = 0`); nonce frozen. So `CellDebitSpec` IS
`QueueEnqueueSpec`'s per-cell `bal` image — NOT a fourth spec. The FIFO append + escrows park are
out-of-IR. -/
theorem unify_enqueue_debit (st st' : RecChainedState) (id m : Nat) (actor cell : CellId)
    (depId : Nat) (dAsset : AssetId) (deposit : ℤ)
    (hspec : QueueEnqueueSpec st id m actor cell depId dAsset deposit st') :
    CellDebitSpec (cellProjBal st.kernel.bal actor dAsset) ⟨deposit⟩
      (cellProjBal st'.kernel.bal actor dAsset) := by
  obtain ⟨k₁, _, _, hk₁, _, _, _, _, hker, _⟩ := hspec
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show st'.kernel.bal actor dAsset = st.kernel.bal actor dAsset - deposit
  rw [hker]
  show (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).bal actor dAsset
      = st.kernel.bal actor dAsset - deposit
  have hbalfn : (createEscrowRawAssetQueue k₁ depId actor cell dAsset deposit id m).bal
      = recBalCreditCell k₁.bal actor dAsset (-deposit) := rfl
  rw [hbalfn]
  unfold recBalCreditCell
  rw [if_pos (And.intro rfl rfl), queueEnqueueK_bal hk₁]
  ring

/-! ## §9 — THE per-cell circuit⟺executor AGREEMENT (the payoff). -/

/-- **`descriptor_agrees_with_executor_enqueue`** — a satisfying run of the runnable descriptor encoding
the actor cell of a committed enqueue agrees with the executor's per-cell conserved post-state: the
descriptor's pinned post-`balLo` (= pre − deposit) equals the executor's debited `bal actor dAsset`, and
the frozen frame agrees. The FIFO append + escrows park are out-of-IR (the §IR flags). -/
theorem descriptor_agrees_with_executor_enqueue
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (st st' : RecChainedState) (id m : Nat) (actor cell : CellId) (depId : Nat)
    (dAsset : AssetId) (deposit : ℤ) (post : CellState)
    (henc : RowEncodesDebit env (cellProjBal st.kernel.bal actor dAsset) ⟨deposit⟩ post)
    (hsat : satisfiedVm hash queueEnqueueVmDescriptor env true true)
    (hspec : QueueEnqueueSpec st id m actor cell depId dAsset deposit st') :
    post.balLo = (cellProjBal st'.kernel.bal actor dAsset).balLo
    ∧ post.balHi = (cellProjBal st'.kernel.bal actor dAsset).balHi
    ∧ (∀ i, post.fields i = (cellProjBal st'.kernel.bal actor dAsset).fields i)
    ∧ post.capRoot = (cellProjBal st'.kernel.bal actor dAsset).capRoot
    ∧ post.reserved = (cellProjBal st'.kernel.bal actor dAsset).reserved := by
  obtain ⟨hcirc, _⟩ := queueEnqueueDescriptor_full_sound hash env
    (cellProjBal st.kernel.bal actor dAsset) post ⟨deposit⟩ henc hsat
  obtain ⟨hcLo, hcHi, _, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _, heF, heCap, heRes⟩ :=
    unify_enqueue_debit st st' id m actor cell depId dAsset deposit hspec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §10 — NON-VACUITY. -/

/-- A concrete enqueue row: `bal_lo 200 → 188` (deposit 12), nonce 9 → 9 (FROZEN), frame fixed at 0. -/
def goodEnqueueRow : VmRowEnv where
  loc := fun v =>
    if v = SEL_QUEUE_ENQUEUE then 1
    else if v = sbCol state.BALANCE_LO then 200
    else if v = saCol state.BALANCE_LO then 188
    else if v = sbCol state.NONCE then 9
    else if v = saCol state.NONCE then 9
    else if v = prmCol param.AMOUNT then 12
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodEnqueueRow` REALIZES the enqueue intent: bal_lo `200 → 188`
(debit 12), nonce frozen `9 → 9`, frame fixed. -/
theorem goodEnqueueRow_realizes_intent : QueueEnqueueRowIntent goodEnqueueRow := by
  unfold QueueEnqueueRowIntent goodEnqueueRow
  simp only [sbCol, saCol, prmCol, SEL_QUEUE_ENQUEUE, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
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
    have e6 : (76 + (3 + i) = 68) = False := by simp; omega
    have f1 : (54 + (3 + i) = 5) = False := by simp; omega
    have f2 : (54 + (3 + i) = 54) = False := by simp
    have f3 : (54 + (3 + i) = 76) = False := by simp; omega
    have f4 : (54 + (3 + i) = 56) = False := by simp; omega
    have f5 : (54 + (3 + i) = 78) = False := by simp; omega
    have f6 : (54 + (3 + i) = 68) = False := by simp; omega
    simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED enqueue row: `goodEnqueueRow` with the post-`bal_lo` tampered to `999` (not the debit `188`). -/
def badEnqueueRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodEnqueueRow.loc v
  nxt := goodEnqueueRow.nxt
  pub := goodEnqueueRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badEnqueueRow`'s post-`bal_lo` is NOT the
debit, so the `gBalLoDebit` gate REJECTS it — a concrete UNSAT. -/
theorem badEnqueueRow_rejected :
    ¬ (VmConstraint.gate gBalLoDebit).holdsVm badEnqueueRow false false := by
  apply queueEnqueueVm_rejects_wrong_balance
  simp only [badEnqueueRow, goodEnqueueRow, sbCol, saCol, prmCol, SEL_QUEUE_ENQUEUE, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §11 — Axiom-hygiene pins. -/

#guard queueEnqueueVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard queueEnqueueVmDescriptor.hashSites.length == 4
#guard queueEnqueueVmDescriptor.traceWidth == 186

#assert_axioms queueEnqueueVm_faithful
#assert_axioms queueEnqueueVm_rejects_wrong_output
#assert_axioms queueEnqueueVm_rejects_wrong_balance
#assert_axioms intent_to_cellDebitSpec
#assert_axioms queueEnqueueDescriptor_full_sound
#assert_axioms queueEnqueueDescriptor_commit_binds_state
#assert_axioms queueEnqueueK_bal
#assert_axioms unify_enqueue_debit
#assert_axioms descriptor_agrees_with_executor_enqueue
#assert_axioms goodEnqueueRow_realizes_intent
#assert_axioms badEnqueueRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitQueueEnqueue
