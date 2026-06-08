/-
# Dregg2.Circuit.Emit.EffectVmEmitSetVK — the VERIFICATION-KEY effect `setVKA`, EMITTED onto a runnable
  EffectVM field column, welded to universe-A's `SetVKSpec`.

## The "ONE circuit" thesis for `setVKA` (a single-field write)

`setVKA` writes the protocol-managed `verification_key` slot of a cell (`Spec/cellstatevk.lean`): the
executor's `.setVKA` arm runs `stateStep s vkField actor cell (.int vk)`, which sets the cell's
`verification_key` field to exactly `vk` (`execFullA_setVK_vkWritten`), freezes the conserved `bal`
ledger, the `caps` graph, and every other cell. NO balance move, NO nonce tick, NO cap edit.

The EffectVM state block carries 8 generic content `field` columns (`state.FIELD_BASE + i`). We bind the
`verification_key` slot to field column 0 (`state.FIELD_BASE + 0`): at the row level a VK write is a
`field[0]` COLUMN MOVE to the new VK value, with EVERY other state column (balance limbs, nonce, the other
7 fields, cap_root, reserved) FROZEN, and the post-state bound into `state_commit` via the GROUP-4 chain.
`field[0]` is an ABSORBED column (`site0`), so the commitment tooth bites a tampered VK.

`setVKVmDescriptor` emits exactly that: the field[0] MOVE gate `new_field0 - vkNew = 0`, the rest of the
block frozen.

## What is PROVED

  * `setVKVm_faithful` — emitted per-row gates ⟺ `SetVKRowIntent` (field[0] := vkNew, rest frozen).
  * `setVKDescriptor_full_sound` — satisfying the descriptor under `RowEncodes` forces `CellSetVKSpec`
    (field[0] = vkNew, every other component frozen) AND publishes `post.commit = PI[NEW_COMMIT]`.
  * `setVKDescriptor_commit_binds_state` — anti-ghost (reuses the transfer keystone; same chain). A
    tampered post-field[0] that claims the published `NEW_COMMIT` is UNSAT (field[0] is absorbed).
  * `unify_setVK` / `unify_setVK_exec` — a committed `SetVKSpec` (= the `.setVKA` arm), projected per cell
    under `cellProjV` (whose `field 0` reads the cell's `verification_key`), satisfies `CellSetVKSpec`
    EXACTLY with `field[0] = vk` (`execFullA_setVK_vkWritten`) and the conserved `bal` frozen
    (`execFullA_setVK_balFrame`). The runnable field column transition IS universe-A's VK-field write.

## HONEST BOUNDARY

  * PER-CELL / PER-ROW. The VK write on ONE cell + its binding into `state_commit`. Cross-row composition
    + the disclosing log receipt = the turn layer, cited.
  * The `cell` index + the `setVKGuard` (authority/membership/liveness) GUARD have no row column; in
    universe-A's spec (cited).
  * The mapping `verification_key ↦ field[0]` is an ENCODING CHOICE: the EffectVM block has no dedicated VK
    column, so we bind it to a generic content field. The other 7 field columns + the cell's OTHER record
    fields (beyond `balance`/`nonce`/`verification_key`) have no separate row column — the projection
    carries only `balLo`/`field 0`; the rest (incl. `nonce`) is `0`-frozen. So the descriptor pins the VK
    write + the conserved-balance freeze, NOT the full record (which universe-A's `SetVKSpec` does
    enumerate — cited). The `nonce` is projected to `0` (frozen trivially) rather than read, since the row
    carries no separate nonce obligation for this effect.
  * `state.RESERVED` not absorbed by any hash-site (inherited transfer-keystone finding).

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR = NAMED hypothesis. No sorry /
:= True / native_decide / rfl-bridge. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatevk

namespace Dregg2.Circuit.Emit.EffectVmEmitSetVK

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
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.CellStateVK

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param + the VK field column. -/

namespace selV
/-- The `setVKA` effect selector column. -/
def SET_VK : Nat := 8
end selV

namespace paramV
/-- The new-VK parameter: the value the witness fills with the supplied `vk`. -/
def VK_NEW : Nat := 2
end paramV

/-- The state-block field offset the `verification_key` slot binds to (field 0). -/
def VK_FIELD_OFF : Nat := state.FIELD_BASE + 0

def eSelSetVK : EmittedExpr := .var selV.SET_VK
def eVkNew : EmittedExpr := .var (prmCol paramV.VK_NEW)

/-! ## §1 — The setVK row gates (field[0] MOVE to the param, everything else frozen). -/

/-- VK MOVE body: `new_field0 - vkNew` (the post field[0] IS the param VK value). -/
def gVkMove : EmittedExpr := eSub (eSA VK_FIELD_OFF) eVkNew

def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)
/-- Freeze gate for the OTHER 7 field columns (i ∈ 1..7). -/
def gFieldFix (i : Nat) : EmittedExpr := eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The 7 other-field-passthrough gates (fields 1..7; field 0 is the moved VK column). -/
def gOtherFieldFixAll : List VmConstraint :=
  (List.range 7).map (fun i => VmConstraint.gate (gFieldFix (i + 1)))

/-- The setVK per-row gates (VK move on field[0] + everything else frozen). -/
def setVKRowGates : List VmConstraint :=
  [ .gate gVkMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix, .gate gCapFix, .gate gResFix ]
  ++ gOtherFieldFixAll

/-! ## §2 — The emitted SET-VK descriptor. -/

def setVKVmAirName : String := "dregg-effectvm-setVK-v1"

/-- **`setVKVmDescriptor`** — the `setVKA` effect's full concrete circuit. -/
def setVKVmDescriptor : EffectVmDescriptor :=
  { name := setVKVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := setVKRowGates ++ transitionAll ++ boundaryFirstPins ++ boundaryLastPins
  , hashSites := transferHashSites
  , ranges := [ ⟨saCol state.BALANCE_LO, 30⟩, ⟨saCol state.BALANCE_HI, 30⟩ ] }

/-! ## §3 — The SET-VK ROW INTENT. -/

/-- **`SetVKRowIntent env`** — field[0] is set to the param `vkNew`, the rest of the block fixed. -/
def SetVKRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol VK_FIELD_OFF) = env.loc (prmCol paramV.VK_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i, 1 ≤ i → i < 8 →
      env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

def IsSetVKRow (env : VmRowEnv) : Prop :=
  env.loc selV.SET_VK = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS. -/

theorem setVKVm_faithful (env : VmRowEnv) :
    (∀ c ∈ setVKRowGates, c.holdsVm env false false) ↔ SetVKRowIntent env := by
  unfold setVKRowGates gOtherFieldFixAll SetVKRowIntent
  constructor
  · intro h
    have hVk := h (.gate gVkMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 7 → VmConstraint.holdsVm env false false (.gate (gFieldFix (i + 1))) := by
      intro i hi; apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gVkMove, gBalLoFix, gBalHiFix, gNonceFix, gCapFix, gResFix,
      eSA, eSB, ePrm, eVkNew, eSub, EmittedExpr.eval] at hVk hLo hHi hNon hCap hRes
    refine ⟨by linarith [hVk], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi1 hi8
    -- i ∈ [1,8); write i = (i-1)+1, apply hFld (i-1)
    have hk : i - 1 < 7 := by omega
    have := hFld (i - 1) hk
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    have heq : i - 1 + 1 = i := by omega
    rw [heq] at this
    linarith
  · rintro ⟨hVk, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gVkMove, eSA, eSB, ePrm, eVkNew, eSub, EmittedExpr.eval]
      rw [hVk]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]; rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld (i + 1) (by omega) (by omega)]; ring

/-- **Anti-ghost (VK tamper).** A row whose post-`field[0]` is NOT the param `vkNew` fails the
`gVkMove` gate (UNSAT). -/
theorem setVKVm_rejects_wrong_vk (env : VmRowEnv)
    (hwrong : env.loc (saCol VK_FIELD_OFF) ≠ env.loc (prmCol paramV.VK_NEW)) :
    ¬ (VmConstraint.gate gVkMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gVkMove, eSA, eSB, ePrm, eVkNew, eSub, EmittedExpr.eval]
  intro h; apply hwrong; linarith [h]

/-! ## §5 — `CellSetVKSpec` + `RowEncodes` → structured per-cell soundness. -/

/-- The per-cell setVK spec: field[0] := `vkNew`, every other block component frozen. -/
def CellSetVKSpec (pre : CellState) (vkNew : ℤ) (post : CellState) : Prop :=
  post.fields 0 = vkNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, i ≠ 0 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

def RowEncodes (env : VmRowEnv) (pre : CellState) (vkNew : ℤ) (post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (sbCol state.STATE_COMMIT) = pre.commit
  ∧ env.loc (prmCol paramV.VK_NEW) = vkNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved
  ∧ env.loc (saCol state.STATE_COMMIT) = post.commit
  ∧ env.pub pi.OLD_COMMIT = pre.commit
  ∧ env.pub pi.NEW_COMMIT = post.commit

theorem intent_to_cellSpec (env : VmRowEnv) (pre post : CellState) (vkNew : ℤ)
    (henc : RowEncodes env pre vkNew post) (hint : SetVKRowIntent env) :
    CellSetVKSpec pre vkNew post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hsbC, hpVk,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes, hsaC, hOld, hNew⟩ := henc
  obtain ⟨hvk, hbal, hbhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.fields 0 = vkNew. hsaF 0 : env.loc (saCol (FIELD_BASE + 0)) = post.fields 0
    have h0 : env.loc (saCol (state.FIELD_BASE + (0 : Fin 8).val)) = post.fields 0 := hsaF 0
    show post.fields 0 = vkNew
    rw [← h0]
    -- VK_FIELD_OFF = FIELD_BASE + 0, and hvk : saCol VK_FIELD_OFF = prmCol VK_NEW
    have : (state.FIELD_BASE + (0 : Fin 8).val) = VK_FIELD_OFF := rfl
    rw [this, hvk, hpVk]
  · rw [← hsaLo, ← hsbLo]; exact hbal
  · rw [← hsaHi, ← hsbHi]; exact hbhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i hi
    have hival : 1 ≤ i.val := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · exact absurd (Fin.ext h) hi
      · exact h
    have := hfld i.val hival i.isLt
    rw [← hsaF i, ← hsbF i]; exact this
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

theorem setVKRowGates_flag_indep (env : VmRowEnv) (b1 b2 : Bool)
    (h : ∀ c ∈ setVKRowGates, c.holdsVm env b1 b2) :
    ∀ c ∈ setVKRowGates, c.holdsVm env false false := by
  intro c hc
  have := h c hc
  unfold setVKRowGates gOtherFieldFixAll at hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
    List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩ <;>
    simpa only [VmConstraint.holdsVm] using this

theorem setVKDescriptor_full_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (vkNew : ℤ)
    (henc : RowEncodes env pre vkNew post)
    (hsat : satisfiedVm hash setVKVmDescriptor env true true) :
    CellSetVKSpec pre vkNew post ∧ post.commit = env.pub pi.NEW_COMMIT := by
  obtain ⟨hcs, _hsites⟩ := hsat
  have hgates : ∀ c ∈ setVKRowGates, c.holdsVm env true true := by
    intro c hc; apply hcs
    unfold setVKVmDescriptor; simp only [List.mem_append]
    exact Or.inl (Or.inl (Or.inl hc))
  have hgates' := setVKRowGates_flag_indep env true true hgates
  have hint := (setVKVm_faithful env).mp hgates'
  refine ⟨intent_to_cellSpec env pre post vkNew henc hint, ?_⟩
  have hlast : ∀ c ∈ boundaryLastPins, c.holdsVm env false true := by
    intro c hc
    have hmem : c ∈ setVKVmDescriptor.constraints := by
      unfold setVKVmDescriptor; simp only [List.mem_append]; exact Or.inr hc
    have hh := hcs c hmem
    unfold boundaryLastPins at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;>
      · simp only [VmConstraint.holdsVm] at hh ⊢; exact hh
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hsaC, _, _⟩ := henc
  rw [← hsaC]; exact (boundaryLast_pins env hlast).1

/-! ## §6 — ANTI-GHOST COMMITMENT TOOTH (reused from the transfer keystone; field[0] is absorbed). -/

theorem setVK_sites_eq : setVKVmDescriptor.hashSites = transferHashSites := rfl

theorem setVKDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ transferHashSites)
    (hs₂ : siteHoldsAll hash e₂ transferHashSites)
    (hpubLo₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpubLo₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT) :
    absorbedCols e₁ = absorbedCols e₂ :=
  Dregg2.Circuit.Emit.EffectVmEmitTransferSound.absorbed_determined_by_commit
    hash hCR e₁ e₂ hs₁ hs₂ (by rw [hpubLo₁, hpubLo₂, hpub])

/-! ## §7 — THE CONNECTOR — `cellProjV` to universe-A's `SetVKSpec`.

`cellProjV k c` reads cell `c`'s `balLo` (`balOf`), `nonce` (`fieldOf nonceField`), and `field 0` =
the cell's `verification_key` (`fieldOf vkField`); the EffectVM columns with no record analogue are `0`. -/

def cellProjV (k : RecordKernelState) (c : CellId) : CellState where
  balLo    := balOf (k.cell c)
  balHi    := 0
  nonce    := 0
  fields   := fun i => if i = 0 then fieldOf vkField (k.cell c) else 0
  capRoot  := 0
  reserved := 0
  commit   := 0

/-- **`unify_setVK` — THE UNIFICATION.** A committed universe-A VK write (`SetVKSpec`), projected onto
`cell` under `cellProjV` with the new-VK param `= vk`, satisfies the keystone's per-cell `CellSetVKSpec`
EXACTLY: `field 0` IS the written `vk` (`setVK_cellWrite_correct`); the conserved `balLo` is frozen
(`setVK_cellWrite_correct` balance-frame); nonce / other fields / capRoot / reserved are frozen. The
runnable field column move IS the executor's VK write. -/
theorem unify_setVK (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (hspec : SetVKSpec s actor cell vk s') :
    CellSetVKSpec (cellProjV s.kernel cell) (vk : ℤ) (cellProjV s'.kernel cell) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, rfl, rfl⟩
  · -- field 0 of the post-projection IS the written vk
    show (cellProjV s'.kernel cell).fields 0 = (vk : ℤ)
    unfold cellProjV
    simp only [if_pos rfl]
    rw [hspec.2.1]
    exact (setVK_cellWrite_correct s.kernel cell vk).1
  · -- balLo frozen: balOf unchanged across the VK write
    show balOf (s'.kernel.cell cell) = balOf (s.kernel.cell cell)
    rw [hspec.2.1]
    exact (setVK_cellWrite_correct s.kernel cell vk).2.1
  · -- other fields (i ≠ 0) frozen: the projection's `fields i` is `0` for i ≠ 0 (both 0)
    intro i hi
    show (if i = 0 then fieldOf vkField (s'.kernel.cell cell) else 0)
        = (if i = 0 then fieldOf vkField (s.kernel.cell cell) else 0)
    rw [if_neg hi, if_neg hi]

/-- **`unify_setVK_exec` — same, against the executor directly.** A committed
`execFullA s (.setVKA actor cell vk) = some s'` projects per-cell to `CellSetVKSpec` with `field 0 = vk`. -/
theorem unify_setVK_exec (s s' : RecChainedState) (actor cell : CellId) (vk : Int)
    (h : execFullA s (.setVKA actor cell vk) = some s') :
    CellSetVKSpec (cellProjV s.kernel cell) (vk : ℤ) (cellProjV s'.kernel cell) :=
  unify_setVK s s' actor cell vk ((execFullA_setVK_iff_spec s actor cell vk s').mp h)

/-- **`descriptor_agrees_with_executor` — per-cell circuit⟺executor agreement.** With the new-VK param
encoded as the executor's written `vk`, the descriptor's pinned post-state agrees with the executor's
post-cell projection on the VK field (the move MATCHES) and the conserved/nonce/frame freeze. -/
theorem descriptor_agrees_with_executor
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (s s' : RecChainedState) (actor cell : CellId) (vk : Int) (post : CellState)
    (henc : RowEncodes env (cellProjV s.kernel cell) (vk : ℤ) post)
    (hsat : satisfiedVm hash setVKVmDescriptor env true true)
    (hexec : execFullA s (.setVKA actor cell vk) = some s') :
    post.fields 0 = (cellProjV s'.kernel cell).fields 0
    ∧ post.balLo = (cellProjV s'.kernel cell).balLo
    ∧ post.balHi = (cellProjV s'.kernel cell).balHi
    ∧ post.nonce = (cellProjV s'.kernel cell).nonce
    ∧ post.capRoot = (cellProjV s'.kernel cell).capRoot
    ∧ post.reserved = (cellProjV s'.kernel cell).reserved := by
  obtain ⟨hcirc, _⟩ := setVKDescriptor_full_sound hash env (cellProjV s.kernel cell) post (vk : ℤ)
    henc hsat
  obtain ⟨hcVk, hcLo, hcHi, hcN, hcF, hcCap, hcRes⟩ := hcirc
  obtain ⟨heVk, heLo, heHi, heN, heF, heCap, heRes⟩ := unify_setVK_exec s s' actor cell vk hexec
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.fields 0 = vk (circuit) ; (cellProjV s' cell).fields 0 = vk (executor) — VK MOVE MATCHES
    rw [hcVk, heVk]
  · rw [hcLo, heLo]
  · rw [hcHi, heHi]
  · rw [hcN, heN]
  · rw [hcCap, heCap]
  · rw [hcRes, heRes]

/-! ## §8 — NON-VACUITY. -/

/-- A concrete setVK row: `field[0] (col 79) → 42`, `vkNew = 42`, balance/nonce/other-fields fixed. -/
def goodSetVKRow : VmRowEnv where
  loc := fun v =>
    if v = selV.SET_VK then 1
    else if v = saCol VK_FIELD_OFF then 42
    else if v = prmCol paramV.VK_NEW then 42
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **NON-VACUITY (witness TRUE).** `goodSetVKRow` REALIZES the intent (`field[0] → 42 = vkNew`,
everything else `0`-frozen). -/
theorem goodSetVKRow_realizes_intent : SetVKRowIntent goodSetVKRow := by
  unfold SetVKRowIntent goodSetVKRow VK_FIELD_OFF
  simp only [sbCol, saCol, prmCol, selV.SET_VK, STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.BALANCE_LO, state.BALANCE_HI, state.NONCE,
    state.CAP_ROOT, state.RESERVED, state.FIELD_BASE, paramV.VK_NEW]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i hi1 hi8
    have e1 : (76 + (3 + i) = 8) = False := by simp; omega
    have e2 : (76 + (3 + i) = 79) = False := by simp; omega
    have e3 : (76 + (3 + i) = 70) = False := by simp; omega
    have f1 : (54 + (3 + i) = 8) = False := by simp; omega
    have f2 : (54 + (3 + i) = 79) = False := by simp; omega
    have f3 : (54 + (3 + i) = 70) = False := by simp; omega
    simp only [e1, e2, e3, f1, f2, f3, if_false]

/-- A FORGED setVK row: `goodSetVKRow` with post-`field[0]` tampered to `999 ≠ 42`. -/
def badSetVKRow : VmRowEnv where
  loc := fun v => if v = saCol VK_FIELD_OFF then 999 else goodSetVKRow.loc v
  nxt := goodSetVKRow.nxt
  pub := goodSetVKRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `badSetVKRow`'s post-`field[0]` is NOT the
param, so `gVkMove` REJECTS it. -/
theorem badSetVKRow_rejected :
    ¬ (VmConstraint.gate gVkMove).holdsVm badSetVKRow false false := by
  apply setVKVm_rejects_wrong_vk
  simp only [badSetVKRow, goodSetVKRow, VK_FIELD_OFF, sbCol, saCol, prmCol, selV.SET_VK,
    STATE_BEFORE_BASE, STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS,
    state.FIELD_BASE, paramV.VK_NEW]
  norm_num

/-! ## §9 — Axiom-hygiene tripwires. -/

#guard setVKVmDescriptor.constraints.length == 13 + 14 + 4 + 3  -- gates(6+7) + transitions + 4 + 3
#guard setVKVmDescriptor.hashSites.length == 4
#guard setVKVmDescriptor.traceWidth == 186

#assert_axioms setVKVm_faithful
#assert_axioms setVKVm_rejects_wrong_vk
#assert_axioms intent_to_cellSpec
#assert_axioms setVKRowGates_flag_indep
#assert_axioms setVKDescriptor_full_sound
#assert_axioms setVKDescriptor_commit_binds_state
#assert_axioms unify_setVK
#assert_axioms unify_setVK_exec
#assert_axioms descriptor_agrees_with_executor
#assert_axioms goodSetVKRow_realizes_intent
#assert_axioms badSetVKRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSetVK
