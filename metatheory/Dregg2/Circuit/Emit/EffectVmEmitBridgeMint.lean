/-
# Dregg2.Circuit.Emit.EffectVmEmitBridgeMint — the INBOUND-BRIDGE-MINT effect `bridgeMintA`, EMITTED
  onto the runnable EffectVM `bal_lo` (balance) column, welded to the validated universe-A spec.

## The "ONE circuit" thesis for `bridgeMintA`

`bridgeMintA` is the §8-portal twin of `mintA`: `execFullA`'s `.bridgeMintA` arm dispatches to the SAME
`recCMintAsset` verbatim (`Spec/supplycreation.lean`, `execFullA_bridgeMintA` / `execBridgeMintA_iff_spec`),
so a committed inbound bridge-mint CREDITS the per-asset ledger `bal` at one `(cell, asset)` by `value`,
prepends a disclosing receipt, and freezes the 16 non-`bal` kernel fields — meeting the SAME `MintASpec`.
The CryptoPortal hypothesis (the bridge proof attesting the inbound value) is carried on the conservation
keystone, not re-checked here.

This module emits the SAME row credit onto the EffectVM layout and welds it through
`execBridgeMintA_iff_spec`. A bridge-mint is a `bal_lo` COLUMN CREDIT (post = pre + `value`, the rest of
the block frozen, the post-state bound into `state_commit` via the GROUP-4 hash chain).

## What is PROVED

  * `bridgeMintVm_faithful` — emitted per-row gates ⟺ `BridgeMintRowIntent` (credit + frame freeze).
  * `bridgeMintDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces
    `CellBridgeMintSpec` AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `bridgeMintDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same chain).
  * `unify_bridgeMint` / `unify_bridgeMint_exec` — a committed `MintASpec` (via the bridge-mint arm
    `execFullA_bridgeMintA` = `recCMintAsset`), projected per `(cell, asset)`, satisfies
    `CellBridgeMintSpec` EXACTLY. The runnable column transition IS universe-A's bridge-mint ledger
    transition.

## HONEST BOUNDARY

  * PER-CELL / PER-ROW. Cross-row composition + the disclosing log receipt = the turn layer, cited.
  * The `(cell, asset)` index + the `mintAdmit` guard + the BRIDGE CryptoPortal proof (the inbound-value
    attestation) have no row column; they live in universe-A's spec / the conservation keystone (cited).
    FLAG: this descriptor does NOT internalize the bridge proof in-circuit — it pins the ledger credit the
    arm commits, conditional on the arm having committed (which carries the portal).
  * NONCE: descriptor FREEZES the nonce; the bridge-mint arm ticks NO nonce — MATCHES (no divergence).
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding).

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.Emit.EffectVmEmitBridgeMint

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub eSelNoop gNonce transitionAll boundaryFirstPins boundaryLastPins
   transferHashSites boundaryLast_pins)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (CellState absorbedCols)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.SupplyCreation

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the bridge-mint effect row. -/

namespace selBM
/-- The `bridgeMintA` effect selector column (`sel::BRIDGE_MINT`). -/
def BRIDGE_MINT : Nat := 40
end selBM

def eSelBridgeMint : EmittedExpr := .var selBM.BRIDGE_MINT

/-! ### Bridge-mint value column (the running trace generator's convention).

`generate_effect_vm_trace`'s `Effect::BridgeMint` arm lays `param0 = mint_hash`, `param1 = value_lo`
(the minted value). The hand-AIR's bridge-mint credit gate reads `prm(1)` (= `bm_val_lo`), NOT
`param.AMOUNT` (column 0, which carries the mint hash on a bridge-mint row). The descriptor MUST read
column 1 or it credits the wrong value (UNSAT on the honest trace). -/
namespace param
/-- Bridge-mint value lives at param column 1. -/
def BRIDGE_MINT_VALUE_LO : Nat := 1
end param

/-- Bridge-mint value as an expression (param column 1). -/
def ePrmMintValue : EmittedExpr := .var (prmCol param.BRIDGE_MINT_VALUE_LO)

/-! ## §1 — The bridge-mint row gates (credit on bal_lo from `param1`, frame freeze, nonce TICK). -/

/-- Balance-lo CREDIT body: `new_bal_lo - old_bal_lo - value` (so `new = old + value`), reading the
value from `param1` (the trace-generator + hand-AIR convention). -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) ePrmMintValue)

def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce TICK body (the running prover's global non-NoOp invariant): reused from the transfer template
(`gNonce`). On a bridge-mint row `s_noop = 0`, so the nonce ticks by one. -/
def gNonceTick : EmittedExpr := gNonce
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

def bridgeMintRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHiFix, .gate gNonceTick, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted BRIDGE-MINT descriptor. -/

def bridgeMintVmAirName : String := "dregg-effectvm-bridgemint-v1"

/-- **`bridgeMintVmDescriptor`** — the `bridgeMintA` effect's full concrete circuit. -/
def bridgeMintVmDescriptor : EffectVmDescriptor :=
  { name := bridgeMintVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := bridgeMintRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
                     ++ selectorGates 40
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The BRIDGE-MINT ROW INTENT. -/

/-- **`BridgeMintRowIntent env`** — `bal_lo` rises by `value` (from `param1`), the rest of the block
fixed, and the runtime nonce TICKS by one (the per-cell sequence counter; the universe-A connector in
§7 reconciles the tick against the FROZEN ledger nonce, exactly as the transfer/burn keystones do). -/
def BridgeMintRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO)
      = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.BRIDGE_MINT_VALUE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE) + 1
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

def IsBridgeMintRow (env : VmRowEnv) : Prop :=
  env.loc selBM.BRIDGE_MINT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

theorem bridgeMintVm_faithful (env : VmRowEnv) (hrow : IsBridgeMintRow env) :
    (∀ c ∈ bridgeMintRowGates, c.holdsVm env false false) ↔ BridgeMintRowIntent env := by
  obtain ⟨_hsBM, hsN⟩ := hrow
  unfold bridgeMintRowGates gFieldFixAll BridgeMintRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceTick) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi; apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHiFix, gNonceTick, gNonce, gCapFix, gResFix,
      ePrmMintValue, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval] at hLo hHi hNon hCap hRes
    rw [hsN] at hNon
    refine ⟨by linarith [hLo], by linarith [hHi], by linarith [hNon], by linarith [hCap],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gBalLoCredit, ePrmMintValue, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceTick, gNonce, eSA, eSB, eSub, eSelNoop, EmittedExpr.eval]
      rw [hsN, hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

theorem bridgeMintVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.BRIDGE_MINT_VALUE_LO)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, ePrmMintValue, eSA, eSB, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellBridgeMintSpec` + `RowEncodes` → structured per-cell soundness. -/

def CellBridgeMintSpec (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce + 1
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

def RowEncodes (env : VmRowEnv) (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.BRIDGE_MINT_VALUE_LO) = value
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (value : ℤ)
    (henc : RowEncodes env pre value post) (hint : BridgeMintRowIntent env) :
    CellBridgeMintSpec pre value post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.BRIDGE_MINT_VALUE_LO) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; have := hfld i.val i.isLt; rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem bridgeMintRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ bridgeMintRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ bridgeMintRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold bridgeMintRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

theorem bridgeMintDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeMintRow env)
    (pre post : CellState) (value : ℤ)
    (henc : RowEncodes env pre value post)
    (hsat : satisfiedVm hash bridgeMintVmDescriptor env true true) :
    CellBridgeMintSpec pre value post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ bridgeMintRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold bridgeMintVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hc)))
  have hgates' := bridgeMintRowGates_flag_indep env true true hgates
  have hint := (bridgeMintVm_faithful env hrow).mp hgates'
  refine ⟨intent_to_cellSpec env pre post value henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ bridgeMintVmDescriptor.constraints := by
      unfold bridgeMintVmDescriptor; simp only [List.mem_append]; exact Or.inl (Or.inr hc)
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone). -/

theorem bridgeMint_sites_eq : bridgeMintVmDescriptor.hashSites = transferHashSites := rfl

theorem bridgeMintDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjA` to the bridge-mint arm (`execFullA_bridgeMintA` = `recCMintAsset`). -/

def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- The executor's genuine per-entry image: `CellBridgeMintSpec` with the nonce-TICK replaced by
nonce-FREEZE (the runtime row ticks the per-cell sequence counter; the bridge-mint arm freezes the
ledger entry's nonce). Every other clause (balLo credit + frame freeze) is identical. -/
def CellBridgeMintSpecFrozenNonce (pre : CellState) (value : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + value
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce          -- FROZEN (executor ledger image) — keystone instead demands `+ 1`
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- **`unify_bridgeMint` — THE UNIFICATION (frozen-nonce variant).** A committed `MintASpec` (the spec
the bridge-mint arm meets, `execBridgeMintA_iff_spec`), projected onto the `(cell, asset)` entry under
`cellProjA`, satisfies `CellBridgeMintSpecFrozenNonce` EXACTLY: the conserved `bal cell a` rises by
`value`; balHi/nonce/frame `0 = 0`. -/
theorem unify_bridgeMint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (hspec : MintASpec s actor cell a value s') :
    CellBridgeMintSpecFrozenNonce (cellProjA s.kernel cell a) value (cellProjA s'.kernel cell a) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal cell a = s.kernel.bal cell a + value
  rw [hspec.2.1]
  exact (recBalCredit_correct s.kernel.bal cell a value).1

/-- **`unify_bridgeMint_exec` — same, against the executor's `.bridgeMintA` arm directly.** Reading
through `execBridgeMintA_iff_spec`, a committed `execFullA s (.bridgeMintA actor cell a value) = some s'`
projects per-entry to `CellBridgeMintSpecFrozenNonce`. -/
theorem unify_bridgeMint_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ)
    (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    CellBridgeMintSpecFrozenNonce (cellProjA s.kernel cell a) value (cellProjA s'.kernel cell a) :=
  unify_bridgeMint s s' actor cell a value ((execBridgeMintA_iff_spec s actor cell a value s').mp h)

/-- **`exec_nonce_is_frozen_not_ticked` — the nonce-tick gap, named precisely.** The bridge-mint arm's
projected entry nonce is FROZEN (`0 = 0`), whereas the EffectVM row's `CellBridgeMintSpec` TICKS it
(`pre.nonce + 1`). The gap is pinned to exactly the nonce column (the runtime sequence counter vs. the
ledger nonce), exactly as in the transfer/burn keystones. -/
theorem exec_nonce_is_frozen_not_ticked (s s' : RecChainedState) (actor cell : CellId) (a : AssetId)
    (value : ℤ) (h : execFullA s (.bridgeMintA actor cell a value) = some s') :
    (cellProjA s'.kernel cell a).nonce = (cellProjA s.kernel cell a).nonce :=
  (unify_bridgeMint_exec s s' actor cell a value h).2.2.1

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement** for the bridge-mint arm
(modulo the nonce-tick gap). The descriptor's pinned post-state agrees with the arm's post-entry state on
EVERY conserved/frame clause (credit + frozen frame). The ONE divergence is the nonce (descriptor ticks
the runtime counter; arm freezes the ledger entry — `exec_nonce_is_frozen_not_ticked`), reported. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv) (hrow : IsBridgeMintRow env)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (value : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) value post)
    (hsat : satisfiedVm hash bridgeMintVmDescriptor env true true)
    (hexec : execFullA s (.bridgeMintA actor cell a value) = some s') :
    post.balLo = (cellProjA s'.kernel cell a).balLo
    ∧ post.balHi = (cellProjA s'.kernel cell a).balHi
    ∧ (∀ i, post.fields i = (cellProjA s'.kernel cell a).fields i)
    ∧ post.capRoot = (cellProjA s'.kernel cell a).capRoot
    ∧ post.reserved = (cellProjA s'.kernel cell a).reserved := by
  obtain ⟨hcirc, _⟩ :=
    bridgeMintDescriptor_full_sound hash env hrow (cellProjA s.kernel cell a) post value henc hsat
  obtain ⟨hcLo, hcHi, _hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, _heN, heF, heCap, heRes⟩ := unify_bridgeMint_exec s s' actor cell a value hexec
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY. -/

def goodBridgeMintRow : VmRowEnv where
  loc := fun v =>
    if v = selBM.BRIDGE_MINT then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 130
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 6
    else if v = prmCol param.BRIDGE_MINT_VALUE_LO then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem goodBridgeMintRow_isRow : IsBridgeMintRow goodBridgeMintRow := by
  unfold IsBridgeMintRow goodBridgeMintRow
  refine ⟨by norm_num [selBM.BRIDGE_MINT], ?_⟩
  norm_num [sel.NOOP, selBM.BRIDGE_MINT, sbCol, saCol, prmCol, STATE_BEFORE_BASE, STATE_AFTER_BASE,
    PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.NONCE,
    param.BRIDGE_MINT_VALUE_LO]

theorem goodBridgeMintRow_realizes_intent : BridgeMintRowIntent goodBridgeMintRow := by
  unfold BridgeMintRowIntent goodBridgeMintRow
  simp only [sbCol, saCol, prmCol, selBM.BRIDGE_MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.BRIDGE_MINT_VALUE_LO]
  refine ⟨by norm_num, rfl, by norm_num, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 40) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 69) = False := by simp; omega
  have f1 : (54 + (3 + i) = 40) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 69) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

def badBridgeMintRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodBridgeMintRow.loc v
  nxt := goodBridgeMintRow.nxt
  pub := goodBridgeMintRow.pub

theorem badBridgeMintRow_rejected :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm badBridgeMintRow false false := by
  apply bridgeMintVm_rejects_wrong_balance
  simp only [badBridgeMintRow, goodBridgeMintRow, sbCol, saCol, prmCol, selBM.BRIDGE_MINT,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.BALANCE_LO, state.NONCE, param.BRIDGE_MINT_VALUE_LO]
  norm_num

/-! ## §9 — Axiom-hygiene tripwires. -/

#guard bridgeMintVmDescriptor.constraints.length == 13 + 14 + 4 + 3 + 1
#guard bridgeMintVmDescriptor.hashSites.length == 4
#guard bridgeMintVmDescriptor.traceWidth == 186

#assert_axioms bridgeMintVm_faithful
#assert_axioms bridgeMintVm_rejects_wrong_balance
#assert_axioms intent_to_cellSpec
#assert_axioms bridgeMintRowGates_flag_indep
#assert_axioms bridgeMintDescriptor_full_sound
#assert_axioms bridgeMintDescriptor_commit_binds_state
#assert_axioms unify_bridgeMint
#assert_axioms unify_bridgeMint_exec
#assert_axioms exec_nonce_is_frozen_not_ticked
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodBridgeMintRow_isRow
#assert_axioms goodBridgeMintRow_realizes_intent
#assert_axioms badBridgeMintRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitBridgeMint
