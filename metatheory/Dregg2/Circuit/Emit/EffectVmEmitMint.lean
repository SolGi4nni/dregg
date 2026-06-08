/-
# Dregg2.Circuit.Emit.EffectVmEmitMint — the SUPPLY-MINT effect `mintA`, EMITTED onto the runnable
  EffectVM `bal_lo` (balance) column, with its full-state per-cell soundness, the anti-ghost commitment
  tooth, and the connector to the validated universe-A `MintASpec` / `recCMintAsset`.

## The "ONE circuit" thesis for `mintA` (the credit twin of burn)

`mintA` is the per-asset privileged-supply MINT (`Spec/supplycreation.lean`): the executor CREDITS the
per-asset ledger `bal` at one `(cell, asset)` by `amt` (`recBalCredit … amt`), prepends a disclosing
receipt, and freezes the 16 non-`bal` kernel fields. Its validation `execMintA_iff_spec` is DONE; this
module emits the SAME effect onto the EffectVM row and welds the two.

The EffectVM block carries the conserved balance as the `bal_lo` limb. A mint is a `bal_lo` COLUMN
CREDIT: post-`bal_lo` = pre PLUS `amount`, the rest of the block frozen, the post-state bound into
`state_commit` via the GROUP-4 hash chain. `mintVmDescriptor` emits exactly that (credit gate
`new_bal_lo - old_bal_lo - amount = 0`, the rest frozen).

## What is PROVED

  * `mintVm_faithful` — emitted per-row gates ⟺ `MintRowIntent` (credit + frame freeze).
  * `mintDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces `CellMintSpec`
    AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `mintDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same hash chain).
  * `unify_mint` / `unify_mint_exec` — a committed `MintASpec` (= `recCMintAsset`), projected per
    `(cell, asset)`, satisfies `CellMintSpec` EXACTLY (the conserved `bal cell a` rises by `amt`; frame
    `0 = 0`). The runnable column transition IS universe-A's `bal`-ledger transition.

## HONEST BOUNDARY

  * PER-CELL / PER-ROW (single ledger entry's credit + commitment binding). Cross-row composition + the
    disclosing log receipt = the turn layer, cited.
  * The `(cell, asset)` index + the `mintAdmit` authority/non-negativity/liveness GUARD have no row
    column; they live in universe-A's spec (cited).
  * NONCE: the descriptor FREEZES the nonce column; universe-A's mint ticks NO nonce — MATCHES (no
    divergence, unlike transfer).
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding).

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.supplycreation

namespace Dregg2.Circuit.Emit.EffectVmEmitMint

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub transitionAll boundaryFirstPins boundaryLastPins
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

/-! ## §0 — Selector for the mint effect row. -/

namespace selM
/-- The `mintA` effect selector column. -/
def MINT : Nat := 4
end selM

def eSelMint : EmittedExpr := .var selM.MINT

/-! ## §1 — The mint row gates (credit on bal_lo, frame freeze). -/

/-- Balance-lo CREDIT body: `new_bal_lo - old_bal_lo - amount` (so `new = old + amount`). -/
def gBalLoCredit : EmittedExpr :=
  .add (eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)) (.mul (.const (-1)) (ePrm param.AMOUNT))

def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-- The mint-specialized per-row gates (balance credit + frame freeze). -/
def mintRowGates : List VmConstraint :=
  [ .gate gBalLoCredit, .gate gBalHiFix, .gate gNonceFix, .gate gCapFix, .gate gResFix ]
  ++ gFieldFixAll

/-! ## §2 — The emitted MINT descriptor. -/

def mintVmAirName : String := "dregg-effectvm-mint-v1"

/-- **`mintVmDescriptor`** — the `mintA` effect's full concrete circuit (credit/freeze gates ++
transitions ++ boundary PI pins, GROUP-4 hash sites, balance range checks). -/
def mintVmDescriptor : EffectVmDescriptor :=
  { name := mintVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := mintRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The MINT ROW INTENT. -/

/-- **`MintRowIntent env`** — `bal_lo` rises by `amount`, the rest of the block fixed. -/
def MintRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

def IsMintRow (env : VmRowEnv) : Prop :=
  env.loc selM.MINT = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

/-- **`mintVm_faithful`.** On a mint row the emitted gates hold IFF the mint intent holds. -/
theorem mintVm_faithful (env : VmRowEnv) :
    (∀ c ∈ mintRowGates, c.holdsVm env false false) ↔ MintRowIntent env := by
  unfold mintRowGates gFieldFixAll MintRowIntent
  constructor
  · intro h
    have hLo := h (.gate gBalLoCredit) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi; apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gBalLoCredit, gBalHiFix, gNonceFix, gCapFix, gResFix,
      eSA, eSB, ePrm, eSub, EmittedExpr.eval] at hLo hHi hNon hCap hRes
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
    · simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **Anti-ghost (balance tamper).** A mint row whose post-`bal_lo` is NOT `old + amount` fails the
`gBalLoCredit` gate (UNSAT). -/
theorem mintVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO)
      ≠ env.loc (sbCol state.BALANCE_LO) + env.loc (prmCol param.AMOUNT)) :
    ¬ (VmConstraint.gate gBalLoCredit).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoCredit, eSA, eSB, ePrm, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellMintSpec` + `RowEncodes` → structured per-cell soundness. -/

/-- The per-cell mint spec: balLo rises by `amt`, the whole rest of the block frozen. -/
def CellMintSpec (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  post.balLo = pre.balLo + amt
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

def RowEncodes (env : VmRowEnv) (pre : CellState) (amt : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol param.AMOUNT) = amt
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post) (hint : MintRowIntent env) :
    CellMintSpec pre amt post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpAmt,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : post.balLo = pre.balLo + env.loc (prmCol param.AMOUNT) := by
      rw [← hsaLo, ← hsbLo]; exact hbal
    rw [this, hpAmt]
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; have := hfld i.val i.isLt; rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem mintRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ mintRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ mintRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold mintRowGates gFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

/-- **`mintDescriptor_full_sound`.** Satisfying the WHOLE descriptor under `RowEncodes` forces the
structured per-cell `CellMintSpec` AND publishes `post.commit = PI[NEW_COMMIT]`. -/
theorem mintDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (amt : ℤ)
    (henc : RowEncodes env pre amt post)
    (hsat : satisfiedVm hash mintVmDescriptor env true true) :
    CellMintSpec pre amt post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ mintRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold mintVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := mintRowGates_flag_indep env true true hgates
  have hint := (mintVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post amt henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ mintVmDescriptor.constraints := by
      unfold mintVmDescriptor; simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone, same hash chain). -/

theorem mint_sites_eq : mintVmDescriptor.hashSites = transferHashSites := rfl

/-- **`mintDescriptor_commit_binds_state` — the anti-ghost tooth for mint.** Two rows satisfying the
mint descriptor's hash-sites and publishing the SAME `NEW_COMMIT` have IDENTICAL absorbed after-state. -/
theorem mintDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjA` to universe-A's `MintASpec` / `recCMintAsset`. -/

/-- Project ledger entry `(c, a)` of `k` into the keystone's `CellState` (balLo = `bal c a`; rest `0`). -/
def cellProjA (k : RecordKernelState) (c : CellId) (a : AssetId) : CellState where
  balLo    := k.bal c a
  balHi    := 0
  nonce    := 0
  fields   := fun _ => 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_mint` — THE UNIFICATION.** A committed universe-A mint (`MintASpec`), projected onto the
minted `(cell, asset)` entry under `cellProjA`, satisfies `CellMintSpec` EXACTLY: the conserved
`bal cell a` rises by `amt`; frame `0 = 0`. So `CellMintSpec` IS `recCMintAsset`'s per-entry effect. -/
theorem unify_mint (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (hspec : MintASpec s actor cell a amt s') :
    CellMintSpec (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) := by
  refine ⟨?_, rfl, rfl, fun _ => rfl, rfl, rfl⟩
  show s'.kernel.bal cell a = s.kernel.bal cell a + amt
  rw [hspec.2.1]
  exact (recBalCredit_correct s.kernel.bal cell a amt).1

/-- **`unify_mint_exec` — same, against the executor.** -/
theorem unify_mint_exec (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ)
    (h : recCMintAsset s actor cell a amt = some s') :
    CellMintSpec (cellProjA s.kernel cell a) amt (cellProjA s'.kernel cell a) :=
  unify_mint s s' actor cell a amt ((recCMintAsset_iff_spec s actor cell a amt s').mp h)

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement.** The descriptor's
pinned post-state agrees with the executor's minted-entry post-state on EVERY clause (the conserved
credit + the frozen frame). No divergence — the nonce-freeze matches (mint ticks nothing). -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hsat : satisfiedVm hash mintVmDescriptor env true true)
    (hexec : recCMintAsset s actor cell a amt = some s') :
    post.balLo = (cellProjA s'.kernel cell a).balLo
    ∧ post.balHi = (cellProjA s'.kernel cell a).balHi
    ∧ post.nonce = (cellProjA s'.kernel cell a).nonce
    ∧ (∀ i, post.fields i = (cellProjA s'.kernel cell a).fields i)
    ∧ post.capRoot = (cellProjA s'.kernel cell a).capRoot
    ∧ post.reserved = (cellProjA s'.kernel cell a).reserved := by
  obtain ⟨hcirc, _⟩ := mintDescriptor_full_sound hash env (cellProjA s.kernel cell a) post amt henc hsat
  obtain ⟨hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heLo, heHi, heN, heF, heCap, heRes⟩ := unify_mint_exec s s' actor cell a amt hexec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · rw [hcN, heN]
  · intro i; rw [hcF i, heF i]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY. -/

/-- A concrete mint row: `bal_lo 100 → 130`, `amount = 30`, frame fixed, nonce 5 → 5 (frozen). -/
def goodMintRow : VmRowEnv where
  loc := fun v =>
    if v = selM.MINT then 1
    else if v = sbCol state.BALANCE_LO then 100
    else if v = saCol state.BALANCE_LO then 130
    else if v = sbCol state.NONCE then 5
    else if v = saCol state.NONCE then 5
    else if v = prmCol param.AMOUNT then 30
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodMintRow` REALIZES the mint intent (`100 → 130 = 100 + 30`). -/
theorem goodMintRow_realizes_intent : MintRowIntent goodMintRow := by
  unfold MintRowIntent goodMintRow
  simp only [sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, param.AMOUNT]
  refine ⟨by norm_num, rfl, rfl, rfl, rfl, ?_⟩
  intro i hi
  have e1 : (76 + (3 + i) = 4) = False := by simp; omega
  have e2 : (76 + (3 + i) = 54) = False := by simp; omega
  have e3 : (76 + (3 + i) = 76) = False := by simp
  have e4 : (76 + (3 + i) = 56) = False := by simp; omega
  have e5 : (76 + (3 + i) = 78) = False := by simp; omega
  have e6 : (76 + (3 + i) = 68) = False := by simp; omega
  have f1 : (54 + (3 + i) = 4) = False := by simp; omega
  have f2 : (54 + (3 + i) = 54) = False := by simp
  have f3 : (54 + (3 + i) = 76) = False := by simp; omega
  have f4 : (54 + (3 + i) = 56) = False := by simp; omega
  have f5 : (54 + (3 + i) = 78) = False := by simp; omega
  have f6 : (54 + (3 + i) = 68) = False := by simp; omega
  simp only [e1, e2, e3, e4, e5, e6, f1, f2, f3, f4, f5, f6, if_false]

/-- A FORGED mint row: `goodMintRow` with post-`bal_lo` tampered to `999 ≠ 130`. -/
def badMintRow : VmRowEnv where
  loc := fun v => if v = saCol state.BALANCE_LO then 999 else goodMintRow.loc v
  nxt := goodMintRow.nxt
  pub := goodMintRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badMintRow`'s post-`bal_lo` is NOT the
credit, so `gBalLoCredit` REJECTS it. -/
theorem badMintRow_rejected : ¬ (VmConstraint.gate gBalLoCredit).holdsVm badMintRow false false := by
  apply mintVm_rejects_wrong_balance
  simp only [badMintRow, goodMintRow, sbCol, saCol, prmCol, selM.MINT, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO,
    state.NONCE, param.AMOUNT]
  norm_num

/-! ## §8½ — THE CLASS-A CAPSTONE (per-cell, the transfer bar exactly).

mint's whole per-cell transition is the `bal_lo` CREDIT + the frozen frame — every state-block column
moved-or-frozen, ALL 13 absorbed into `state_commit` (anti-ghosted via the transfer keystone), and
unified to the verified executor (`recCMintAsset`). This capstone bundles the three corners into ONE
class-A statement (full per-cell post-state from the descriptor + anti-ghost on all of it + executor
agreement), exactly the shape `transferDescriptor_full_sound` + `…_commit_binds_state` +
`unify_*_exec` give for transfer.

The ONE residual — the *global supply total* — is NOT a per-cell state-block column; it is a
CROSS-CELL / TURN-LEVEL accumulator (mint by definition changes the total supply, which no single cell
carries). This is the EXACT analogue of transfer's two-sided conservation (sender-debit ⟺
receiver-credit), which the keystone's HONEST BOUNDARY assigns to the turn-composition layer, NOT the
per-row theorem. So mint meets the per-cell class-A bar transfer set; the supply-total invariant is a
turn property (cited, not papered), not a per-cell gap. -/

/-- **`mintDescriptor_classA` — the per-cell class-A capstone.** Satisfying the runnable descriptor under
`RowEncodes`, for the minted `(cell, asset)` entry of a committed `recCMintAsset`, forces: (a) the FULL
per-cell `CellMintSpec` (bal_lo credited by `amt`, the WHOLE frame frozen); (b) the post-state published
as `PI[NEW_COMMIT]`; and (c) AGREEMENT with the executor's per-cell post-state on every clause. The
anti-ghost (`mintDescriptor_commit_binds_state`) covers all 13 absorbed columns. This is the transfer
class-A bar, per cell. -/
theorem mintDescriptor_classA (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell : CellId) (a : AssetId) (amt : ℤ) (post : CellState)
    (henc : RowEncodes env (cellProjA s.kernel cell a) amt post)
    (hsat : satisfiedVm hash mintVmDescriptor env true true)
    (hexec : recCMintAsset s actor cell a amt = some s') :
    CellMintSpec (cellProjA s.kernel cell a) amt post
    ∧ post.commit = env.pub pi.NEW_COMMIT
    ∧ post.balLo = (cellProjA s'.kernel cell a).balLo
    ∧ post.balHi = (cellProjA s'.kernel cell a).balHi
    ∧ post.nonce = (cellProjA s'.kernel cell a).nonce
    ∧ (∀ i, post.fields i = (cellProjA s'.kernel cell a).fields i)
    ∧ post.capRoot = (cellProjA s'.kernel cell a).capRoot
    ∧ post.reserved = (cellProjA s'.kernel cell a).reserved := by
  obtain ⟨hspec, hcommit⟩ := mintDescriptor_full_sound hash env (cellProjA s.kernel cell a) post amt henc hsat
  obtain ⟨hLo, hHi, hN, hF, hCap, hRes⟩ :=
    descriptor_agrees_with_executor hash env s s' actor cell a amt post henc hsat hexec
  exact ⟨hspec, hcommit, hLo, hHi, hN, hF, hCap, hRes⟩

/-! ## §9 — Axiom-hygiene tripwires. -/

#assert_axioms mintDescriptor_classA

#guard mintVmDescriptor.constraints.length == 13 + 14 + 4 + 3
#guard mintVmDescriptor.hashSites.length == 4
#guard mintVmDescriptor.traceWidth == 186

#assert_axioms mintVm_faithful
#assert_axioms mintVm_rejects_wrong_balance
#assert_axioms intent_to_cellSpec
#assert_axioms mintRowGates_flag_indep
#assert_axioms mintDescriptor_full_sound
#assert_axioms mintDescriptor_commit_binds_state
#assert_axioms unify_mint
#assert_axioms unify_mint_exec
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodMintRow_realizes_intent
#assert_axioms badMintRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitMint
