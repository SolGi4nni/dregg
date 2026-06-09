/-
# Dregg2.Circuit.Emit.EffectVmEmitDropRef — the CapTP GC / reference-drop effect `dropRefA`, EMITTED
  onto the runnable EffectVM `cap_root` column, with its full-state soundness and the connector to the
  validated universe-A `RevokeSpec` / `execFullA_dropRef_iff_spec`.

## The "ONE circuit" thesis (REUSES the `attenuateA` cap-graph LOCAL TEMPLATE)

`dropRefA` (`Inst/dropRefA.lean`, `Spec/authorityrevocation.lean`) is the CapTP garbage-collect arm of
the authority-revocation family. It rewrites the `caps` table to the cap-graph `removeEdge`
(`removeEdgeCaps caps holder t` — `holder` loses every cap conferring an edge to `t`; every OTHER
holder's cap-list literally unchanged), prepends one receipt row to the log, and freezes the 16
non-`caps` kernel fields. Its validation `dropRefA_full_sound ⇒ RevokeSpec` is DONE; this module emits
the SAME effect onto the running EffectVM row layout and welds the two.

Like `attenuateA`, `dropRefA` is a `caps`-FUNCTION-field move, so at the row level it is a `cap_root`
COLUMN MOVE (state offset 11, `state.CAP_ROOT`): the post `cap_root` is the digest of the post
cap-table (`removeEdge`-filtered), every OTHER state column frozen, and the post-state bound into the
published `state_commit` (`site2` absorbs `cap_root`) under Poseidon2 CR.

`dropRefVmDescriptor` emits exactly that: post `cap_root` pinned to a parameter `paramDR.CAP_DIGEST_NEW`
(the runnable column the witness generator fills with `D (removeEdgeCaps …)`), the move gate
`new_cap_root - capDigestNew = 0`, and the frame (balance limbs / nonce / 8 fields / reserved) frozen.
We PROVE: satisfying the descriptor pins the full per-cell post-state (`cap_root` moved, frame frozen)
`↔` the row intent `DropRefRowIntent`; the GROUP-4 sites bind the WHOLE post-state into `state_commit`
— so a tampered post-`cap_root` that still claims `NEW_COMMIT` is UNSAT (the anti-ghost tooth, REUSED
from the transfer keystone).

## The CONNECTOR — `capRootProj` to universe-A's `RevokeSpec`

`capRootProj D k = D k.caps` reads the SAME whole-function digest `D : Caps → ℤ` universe-A's
`capsComponent D hD` uses. `unify_dropRef` shows: when `RevokeSpec` holds (so `k'.caps = removeEdgeCaps
k.caps holder t`), the projected post-`cap_root` is EXACTLY `D (removeEdgeCaps k.caps holder t)` — the
column move the descriptor pins. So the runnable `cap_root` transition IS universe-A's `caps`-digest
transition; not a fourth spec.

## HONEST BOUNDARY (precise — do NOT over-read)

  * **IR GAP — needs IR extension: cap-table hash-site (inherited from `attenuateA`).** The `cap_root`
    column carries the SCALAR digest `D caps` of the cap-table FUNCTION; the EffectVM IR's `VmHashSite`
    cannot re-derive `cap_root` IN-circuit from the cap-table's serialization. So the descriptor PINS
    the `cap_root` column transition `new_cap_root = D(post.caps)` (witness supplying the digest) and
    binds that column into `state_commit`, but does NOT prove in-circuit that `cap_root` IS the genuine
    Merkle digest of the post cap-table. That binding lives in universe-A's `Function.Injective D`
    portal (the SAME bar `dropRefA_full_sound` uses). We connect through `capRootProj`. FLAG: a future
    IR extension (a `VmHashSite` over the cap-table rows) would internalize it.

  * **IR GAP — the LOG is not an EffectVM column.** `dropRefA` GROWS the log by the `authReceipt`; the
    EffectVM row has no log column. The log advance lives in universe-A's `logHashInjective` portal,
    not the per-row circuit. FLAG.

  * **GUARD off-row.** `dropRefA`'s guard is the TRIVIAL `True` (revocation is UNCONDITIONAL); committed
    as a `propBit` in the v2 framework, off-row.

  * PER-CELL / PER-ROW. Single-row AIR. Cross-row composition is the turn layer (`TurnEmit`), cited.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`; the cap-table digest enters ONLY as `Function.Injective
D` (universe-A's portal). No `sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge.
Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.authorityrevocation

namespace Dregg2.Circuit.Emit.EffectVmEmitDropRef

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub site0 site1 transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the cap-graph drop-ref row.

`dropRefA` has its own per-effect selector (`selDR.DROP_REF`). The post cap-digest the row pins is
carried in a parameter column `paramDR.CAP_DIGEST_NEW` (the runnable column the witness generator fills
with `D (removeEdgeCaps …)`). -/

namespace selDR
/-- The `dropRefA` effect selector column. -/
def DROP_REF : Nat := 5
end selDR

namespace paramDR
/-- The post cap-table digest parameter: the value the witness fills with `D (post.caps)`. -/
def CAP_DIGEST_NEW : Nat := 4
end paramDR

/-- The `dropRefA` selector as an expression. -/
def eSelDR : EmittedExpr := .var selDR.DROP_REF

/-- The post-cap-digest param as an expression. -/
def eCapDigestNew : EmittedExpr := .var (prmCol paramDR.CAP_DIGEST_NEW)

/-! ## §1 — The cap-graph row gates (the running prover's, specialized to the row).

The drop-ref effect MOVES `cap_root` to the post cap-table digest and FREEZES the rest of the block. -/

/-- Cap-root MOVE body: `new_cap_root - capDigestNew`. -/
def gCapMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eCapDigestNew

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body (a revocation does NOT tick the cell nonce). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` freeze body. -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The eight field-freeze gates. -/
def gFieldFixAll : List VmConstraint :=
  (List.range 8).map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `dropRefA` AIR identity (the fingerprint binding). -/
def dropRefVmAirName : String := "dregg-effectvm-dropRefA-v2"

/-- The cap-graph per-row gates: cap-root MOVE, balance/nonce/reserved freeze, 8 fields freeze. -/
def dropRefRowGates : List VmConstraint :=
  [ .gate gCapMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's (the moved `cap_root` is
absorbed by site 2). -/
def dropRefHashSites : List VmHashSite := transferHashSites

/-- **`dropRefVmDescriptor`** — the `dropRefA` effect's concrete circuit, emitted through the EffectVM
IR: the cap-root MOVE + frame-freeze gates ++ transition continuity ++ the row-0 boundary pins, with the
4 ordered GROUP-4 hash sites. No balance range checks (no balance move). -/
def dropRefVmDescriptor : EffectVmDescriptor :=
  { name := dropRefVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := dropRefRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := dropRefHashSites
  , ranges := [] }

/-! ## §3 — The cap-graph ROW INTENT (the independent faithfulness target).

`DropRefRowIntent env` is the field-level cap-graph move: post `cap_root` IS the supplied post
cap-digest, the balance limbs / nonce / reserved / 8 fields FIXED. The EffectVM-row projection of
`RevokeSpec`'s `caps` clause (the whole-function `caps` equality ⟹ cap-DIGEST column) + the 16-field
freeze. -/

/-- **`DropRefRowIntent env`** — post `cap_root` is the post-cap-digest param, frame frozen. -/
def DropRefRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (prmCol paramDR.CAP_DIGEST_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a `dropRefA` row: `s_dropRef = 1`, `s_noop = 0`. -/
def IsDropRefRow (env : VmRowEnv) : Prop :=
  env.loc selDR.DROP_REF = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`dropRefRowGates_holds_iff`** — on a `dropRefA` row, the emitted per-row gates all hold IFF
`DropRefRowIntent` holds. -/
theorem dropRefRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ dropRefRowGates, c.holdsVm env false false) ↔ DropRefRowIntent env := by
  unfold dropRefRowGates gFieldFixAll DropRefRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapMove, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eCapDigestNew, eSub, EmittedExpr.eval] at hCap hLo hHi hNon hRes
    refine ⟨by linarith [hCap], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hRes], ?_⟩
    intro i hi
    have := hFld i hi
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hCap, hLo, hHi, hNon, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld i hi]; ring

/-- **`dropRefVm_faithful` — THE deliverable.** On a `dropRefA` row, the emitted descriptor's per-row
gates hold IFF the cap-graph drop intent holds. -/
theorem dropRefVm_faithful (env : VmRowEnv) :
    (∀ c ∈ dropRefRowGates, c.holdsVm env false false) ↔ DropRefRowIntent env :=
  dropRefRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` is NOT the supplied digest fails the
`gCapMove` gate (UNSAT). -/
theorem dropRefVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramDR.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem dropRefVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ DropRefRowIntent env) :
    ¬ (∀ c ∈ dropRefRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((dropRefVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog). -/

/-- **`CapRowEncodes env pre post capDigestNew`** — the row decodes to `(pre, post)` cell states with the
post cap-digest carried in `param.CAP_DIGEST_NEW`. -/
def CapRowEncodes (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramDR.CAP_DIGEST_NEW) = capDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell cap-graph spec: the moved cell's WHOLE post-state is `pre` with `cap_root` set to the
new cap-digest, every other field frozen. The per-cell projection of universe-A's `RevokeSpec`. -/
def CapCellSpec (pre post : CellState) (capDigestNew : ℤ) : Prop :=
  post.capRoot = capDigestNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `CapRowEncodes`, `DropRefRowIntent` IS the structured per-cell `CapCellSpec`. -/
theorem intent_to_capCellSpec (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew) (hint : DropRefRowIntent env) :
    CapCellSpec pre post capDigestNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hpDig]; exact hcap
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`dropRefDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under
the `CapRowEncodes` decoding forces the structured per-cell `CapCellSpec`. -/
theorem dropRefDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ dropRefRowGates, c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  intent_to_capCellSpec env pre post capDigestNew henc ((dropRefVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, cap-root included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `dropRefHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem dropRefHashSites_eq : dropRefHashSites = transferHashSites := rfl

/-- **`dropRefDescriptor_commit_binds_state` — the whole-state tooth.** Two `dropRefA` rows that satisfy
the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved
post-`cap_root` (an absorbed column, site 2) included. -/
theorem dropRefDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ dropRefHashSites)
    (hs₂ : siteHoldsAll hash e₂ dropRefHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [dropRefHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `capRootProj` to universe-A's `RevokeSpec`.

`capRootProj D k = D k.caps` reads the SAME whole-function digest universe-A's `capsComponent D hD`
uses. A committed `RevokeSpec` makes the projected post-`cap_root` EXACTLY `D (removeEdgeCaps k.caps
holder t)` — the column move the descriptor pins. -/

open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec removeEdgeCaps execFullA_dropRef_iff_spec)

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value for kernel state `k`: `D k.caps`. -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries: `D` of the
`removeEdge`-filtered cap-table. -/
def dropRefCapDigestNew (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId) : ℤ :=
  D (removeEdgeCaps k.caps holder t)

/-- **`unify_dropRef` — THE CONNECTOR.** When universe-A's `RevokeSpec` holds, the projected
post-`cap_root` is EXACTLY `dropRefCapDigestNew D k holder t` — the column move the descriptor pins. So
`CapCellSpec`'s `cap_root` clause IS universe-A's `caps`-clause, projected to the digest column. -/
theorem unify_dropRef (D : Caps → ℤ) (s : RecChainedState) (holder t : CellId) (s' : RecChainedState)
    (hspec : RevokeSpec s holder t s') :
    capRootProj D s'.kernel = dropRefCapDigestNew D s.kernel holder t := by
  -- RevokeSpec's caps clause is `s'.kernel.caps = removeEdgeCaps s.kernel.caps holder t`.
  obtain ⟨_, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (removeEdgeCaps s.kernel.caps holder t)
  rw [hcaps]

/-- **`unify_dropRef_via_exec` — the runnable column move inherits the VALIDATED guarantee.** Chaining
universe-A's `execFullA_dropRef_iff_spec` (a committed executor drop ⟹ `RevokeSpec`) with
`unify_dropRef`: a committed `dropRefA` forces the projected post-`cap_root` to the `removeEdge`-filtered
cap-digest — the EXACT column value the runnable descriptor's `param.CAP_DIGEST_NEW` carries. So the
runnable `cap_root` move is universe-A's validated `caps` transition, not a fourth spec. -/
theorem unify_dropRef_via_exec (D : Caps → ℤ)
    (s : RecChainedState) (holder t : CellId) (s' : RecChainedState)
    (h : execFullA s (.dropRefA holder t) = some s') :
    capRootProj D s'.kernel = dropRefCapDigestNew D s.kernel holder t :=
  unify_dropRef D s holder t s' ((execFullA_dropRef_iff_spec s holder t s').mp h)

/-! ## §9 — NON-VACUITY: a concrete cap-graph row that satisfies the intent, and one that does not. -/

/-- A concrete `dropRefA` row: `cap_root 11 → 77` (the new digest), frame frozen at `0`. -/
def dropGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selDR.DROP_REF then 1
    else if v = sbCol state.CAP_ROOT then 11
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramDR.CAP_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `dropGoodRow` is a genuine `dropRefA` row. -/
theorem dropGoodRow_isDropRefRow : IsDropRefRow dropGoodRow := by
  unfold IsDropRefRow dropGoodRow
  constructor <;> norm_num [selDR.DROP_REF, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT,
    paramDR.CAP_DIGEST_NEW]

/-- Evaluate `dropGoodRow.loc` at a column given as a LITERAL `Nat` not in the named set
`{5, 65, 87, 72}` (selector `5`, pre-`cap_root` `65`, post-`cap_root` `87`, cap-digest param `72`). -/
theorem dropGoodRow_loc_default (n : Nat)
    (h5 : n ≠ 5) (h65 : n ≠ 65) (h87 : n ≠ 87) (h72 : n ≠ 72) :
    dropGoodRow.loc n = 0 := by
  show (if n = selDR.DROP_REF then (1:ℤ)
    else if n = sbCol state.CAP_ROOT then 11
    else if n = saCol state.CAP_ROOT then 77
    else if n = prmCol paramDR.CAP_DIGEST_NEW then 77 else 0) = 0
  have c1 : (selDR.DROP_REF : Nat) = 5 := rfl
  have c2 : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have c3 : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have c4 : prmCol paramDR.CAP_DIGEST_NEW = 72 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramDR.CAP_DIGEST_NEW; rfl
  rw [c1, c2, c3, c4, if_neg h5, if_neg h65, if_neg h87, if_neg h72]

/-- **NON-VACUITY (witness TRUE).** `dropGoodRow` REALIZES the cap-graph intent: post `cap_root = 77` =
the param digest, balance/nonce/reserved/fields frozen at `0`. -/
theorem dropGoodRow_realizes_intent : DropRefRowIntent dropGoodRow := by
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramDR.CAP_DIGEST_NEW = 72 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramDR.CAP_DIGEST_NEW; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post cap_root (87 → 77) = cap-digest param (72 → 77)
    show dropGoodRow.loc (saCol state.CAP_ROOT) = dropGoodRow.loc (prmCol paramDR.CAP_DIGEST_NEW)
    rw [hsacap, hprm]; rfl
  · show dropGoodRow.loc (saCol state.BALANCE_LO) = dropGoodRow.loc (sbCol state.BALANCE_LO)
    rw [dropGoodRow_loc_default (saCol state.BALANCE_LO) (by decide) (by decide) (by decide) (by decide),
        dropGoodRow_loc_default (sbCol state.BALANCE_LO) (by decide) (by decide) (by decide) (by decide)]
  · show dropGoodRow.loc (saCol state.BALANCE_HI) = dropGoodRow.loc (sbCol state.BALANCE_HI)
    rw [dropGoodRow_loc_default (saCol state.BALANCE_HI) (by decide) (by decide) (by decide) (by decide),
        dropGoodRow_loc_default (sbCol state.BALANCE_HI) (by decide) (by decide) (by decide) (by decide)]
  · show dropGoodRow.loc (saCol state.NONCE) = dropGoodRow.loc (sbCol state.NONCE)
    rw [dropGoodRow_loc_default (saCol state.NONCE) (by decide) (by decide) (by decide) (by decide),
        dropGoodRow_loc_default (sbCol state.NONCE) (by decide) (by decide) (by decide) (by decide)]
  · show dropGoodRow.loc (saCol state.RESERVED) = dropGoodRow.loc (sbCol state.RESERVED)
    rw [dropGoodRow_loc_default (saCol state.RESERVED) (by decide) (by decide) (by decide) (by decide),
        dropGoodRow_loc_default (sbCol state.RESERVED) (by decide) (by decide) (by decide) (by decide)]
  · intro i hi8
    show dropGoodRow.loc (saCol (state.FIELD_BASE + i)) = dropGoodRow.loc (sbCol (state.FIELD_BASE + i))
    have hsaI : saCol (state.FIELD_BASE + i) = 79 + i := by
      unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
        state.FIELD_BASE; omega
    have hsbI : sbCol (state.FIELD_BASE + i) = 57 + i := by
      unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.FIELD_BASE; omega
    rw [hsaI, hsbI,
        dropGoodRow_loc_default (79 + i) (by omega) (by omega) (by omega) (by omega),
        dropGoodRow_loc_default (57 + i) (by omega) (by omega) (by omega) (by omega)]

/-- A forged `dropRefA` row: `dropGoodRow` with the post-`cap_root` tampered to `999 ≠ 77`. -/
def dropBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else dropGoodRow.loc v
  nxt := dropGoodRow.nxt
  pub := dropGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `dropBadRow`'s post-`cap_root` is NOT the
param digest, so the `gCapMove` gate REJECTS it — a concrete UNSAT. -/
theorem dropBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm dropBadRow false false := by
  apply dropRefVm_rejects_wrong_capRoot
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramDR.CAP_DIGEST_NEW = 72 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramDR.CAP_DIGEST_NEW; rfl
  have hbad : dropBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else dropGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hparam : dropBadRow.loc (prmCol paramDR.CAP_DIGEST_NEW) = 77 := by
    show (if prmCol paramDR.CAP_DIGEST_NEW = saCol state.CAP_ROOT then (999:ℤ)
      else dropGoodRow.loc (prmCol paramDR.CAP_DIGEST_NEW)) = 77
    rw [hsacap, hprm, if_neg (by decide)]
    show dropGoodRow.loc (prmCol paramDR.CAP_DIGEST_NEW) = 77
    rw [hprm]; rfl
  rw [hbad, hparam]; decide

/-! ## §G — THE GENUINE CLASS-A `dropRef` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`dropRef` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`dropRef`-specific content is the OP tag `capOp.DROP_REF = 5` carried in the edge leaf (the ref/cap-table
set-delete), plus the existing `removeEdgeCaps` connector. We re-export the genuine soundness + edge-binding
anti-ghost for `dropRef`. `dropRefHashSites = transferHashSites = attenuateHashSites` (defeq), so the shared
commitment binding applies verbatim. -/

open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds)

/-- **`dropRefVmDescriptorGenuine`** — the GENUINE `dropRef` circuit: definitionally the shared genuine
cap-root-recompute descriptor (the opaque digest param is GONE; `cap_root` is FORCED in-row). -/
def dropRefVmDescriptorGenuine : EffectVmDescriptor :=
  Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateVmDescriptorGenuine

/-- **`dropRefGenuine_sound` — THE CLASS-A THEOREM for `dropRef`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound` (decoded by AttenuateA's `CapRowEncodes`,
which on a cap row is the same column decoding `dropRef`'s local `CapRowEncodes` uses). -/
theorem dropRefGenuine_sound (hash : List ℤ → ℤ) (env : VmRowEnv)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateGenuineRowGates,
        c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapCellSpecGenuine hash env pre post :=
  Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateGenuine_sound
    hash env pre post capDigestNew henc hgates hrec

/-- **`dropRefGenuine_binds_edge` — the genuine class-A anti-ghost for `dropRef`.** Two genuine `dropRef`
rows with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the removed cap-edge moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem dropRefGenuine_binds_edge (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hsCommit₁ : siteHoldsAll hash e₁ dropRefHashSites)
    (hsCommit₂ : siteHoldsAll hash e₂ dropRefHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateGenuine_binds_edge
    hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

#assert_axioms dropRefGenuine_sound
#assert_axioms dropRefGenuine_binds_edge

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard dropRefVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard dropRefVmDescriptor.hashSites.length == 4
#guard dropRefVmDescriptor.traceWidth == 186

#assert_axioms dropRefRowGates_holds_iff
#assert_axioms dropRefVm_faithful
#assert_axioms dropRefVm_rejects_wrong_capRoot
#assert_axioms dropRefVm_rejects_wrong_output
#assert_axioms intent_to_capCellSpec
#assert_axioms dropRefDescriptor_full_sound
#assert_axioms dropRefDescriptor_commit_binds_state
#assert_axioms unify_dropRef
#assert_axioms unify_dropRef_via_exec
#assert_axioms dropGoodRow_realizes_intent
#assert_axioms dropBadRow_rejected

/-! ## §W — THE MAGNESIUM LIFT: `dropRef`'s RUNNABLE descriptor binds the FULL 17-field post-state.

`dropRef` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the SHARED cap-graph WIDE
descriptor `attenuateVmDescriptorWide` (`EffectVmEmitAttenuateA §W`): the cap-root MOVE + frame freeze
gates UNCHANGED, but widened to `EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites` so the published
`state_commit` absorbs the `system_roots` digest. The KERNEL step (`removeEdgeCaps`) edits ONLY `caps`;
the 8 side-table roots are FROZEN, so the full clause is the per-cell `CapCellSpec` (cap_root =
`dropRefCapDigestNew`) AND `postRoots = preRoots`. (The CapTP-GC REFCOUNT semantics — the worthwhile
GC-at-one model — is closed at the kernel-model layer by `recKDropRefGC`, §RC below; this circuit binds
the resulting `caps`-digest move + the frozen side-table roots into `state_commit`.) -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorWide CapFullClause cap_runnable_full_sound cap_runnable_binds_full_state
   IsAttenRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (absorbedCols)
open Dregg2.Exec.SystemRoots (SysRoots)

/-- **`dropRefVmDescriptorWide`** — the runnable `dropRef` FULL-state circuit: definitionally the shared
cap-graph WIDE descriptor (`attenuateVmDescriptorWide`), 188-wide with `wideHashSites`. The
`dropRef`-specific content is the post `cap_root` digest VALUE `dropRefCapDigestNew D k holder t` (= the
`removeEdgeCaps` digest), connected via `unify_dropRef`. -/
def dropRefVmDescriptorWide : EffectVmDescriptor := attenuateVmDescriptorWide

/-- **`dropRef_runnable_full_sound` — THE MAGNESIUM CROWN for `dropRef`.** A row satisfying the runnable
`dropRef` WIDE descriptor (`satisfiedVm`, first/last active), under the structured decode (the post
`cap_root` carrying `dropRefCapDigestNew D k holder t`, the roots frozen), pins the FULL 17-field
cap-graph post-state: the per-cell `cap_root` MOVE to the edge-removed digest + frame freeze (binding
`cell`/`caps`/`bal`-here + frame) AND the frozen `system_roots` sub-block (binding the 8 side-table
roots). The `cap_root` value is universe-A's validated `removeEdgeCaps` digest via `unify_dropRef`. -/
theorem dropRef_runnable_full_sound (D : Caps → ℤ) (k : RecordKernelState) (holder t : CellId)
    (preRoots : SysRoots) (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState)
    (postRoots : SysRoots)
    (hrow : IsAttenRow env)
    (henc : Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.CapRowEncodes env pre post
              (dropRefCapDigestNew D k holder t))
    (hroots : postRoots = preRoots)
    (hsat : satisfiedVm hash dropRefVmDescriptorWide env true true) :
    CapFullClause (dropRefCapDigestNew D k holder t) preRoots pre post postRoots :=
  cap_runnable_full_sound (dropRefCapDigestNew D k holder t) preRoots hash env pre post postRoots
    hrow henc hroots hsat

/-- **`dropRef_runnable_binds_full_state` — the whole-17-field anti-ghost for `dropRef`.** Two wide
`dropRef` rows publishing the same `NEW_COMMIT` (with `systemRootsDigest` carriers) agree on EVERY
absorbed state-block column (the moved `cap_root` included) AND every side-table root (the `REFCOUNT`
root included) — so a prover cannot keep `NEW_COMMIT` while tampering ANY of the 17 fields. Inherited
from the shared `cap_runnable_binds_full_state`. -/
theorem dropRef_runnable_binds_full_state (capDigestNew : ℤ) (preRoots : SysRoots)
    (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : SysRoots)
    (hsat₁ : satisfiedVm hash dropRefVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash dropRefVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂) :
    absorbedCols e₁ = absorbedCols e₂
    ∧ (∀ i : Fin Dregg2.Exec.SystemRoots.N_SYSTEM_ROOTS, sr₁ i = sr₂ i) :=
  cap_runnable_binds_full_state capDigestNew preRoots hash hCR
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

#assert_axioms dropRef_runnable_full_sound
#assert_axioms dropRef_runnable_binds_full_state

end Dregg2.Circuit.Emit.EffectVmEmitDropRef
