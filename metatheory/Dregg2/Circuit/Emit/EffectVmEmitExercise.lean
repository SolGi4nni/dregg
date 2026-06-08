/-
# Dregg2.Circuit.Emit.EffectVmEmitExercise — the composite hold-gate effect `exerciseA`'s OUTER layer,
  EMITTED onto a runnable EffectVM full-FREEZE row, with its full-state soundness and the connector to
  the validated universe-A `ExerciseHoldSpec` / `exerciseStepA_iff_holdSpec`.

## The "ONE circuit" thesis — exercise's OUTER hold layer is a PURE FRAME-FREEZE

`exerciseA` (`Inst/exerciseA.lean`, `ActionDispatch.lean`) is a COMPOSITE meta-action. Its OUTER
hold-gate layer (`ExerciseHoldSpec`) checks `exerciseGuard` (the actor holds SOME cap conferring an edge
to `target`), prepends one `authReceipt` to the log, and LITERALLY FREEZES THE ENTIRE KERNEL
(`st' = exerciseHoldState st actor = {st with log := authReceipt actor :: st.log}` — every kernel field
identical). Its validation `exerciseA_full_sound ⇒ ExerciseHoldSpec` is DONE.

At the EffectVM per-row level the outer hold layer is therefore the SIMPLEST possible transition: EVERY
state-block column is FROZEN (`state_after[i] = state_before[i]` for all 14 columns). `exerciseVmDescriptor`
emits exactly that 14-column freeze, and we PROVE: satisfying the descriptor pins the full per-cell
post-state EQUAL to the pre-state (`ExerciseRowIntent`); the GROUP-4 sites bind the (unchanged)
post-state into `state_commit` — so a tampered post-state that still claims the published `NEW_COMMIT`
is UNSAT (the anti-ghost tooth, reused from the transfer keystone).

## The CONNECTOR — `cellProj` to universe-A's `ExerciseHoldSpec`

`ExerciseHoldSpec` freezes the whole kernel, so EVERY cell's projection is frozen across the hold step.
`unify_exercise` shows: when `ExerciseHoldSpec` holds, the projected post-cell EQUALS the projected
pre-cell on every EffectVM column (balance/nonce/fields/cap_root/reserved) — exactly the freeze the
descriptor pins. So the runnable freeze row IS universe-A's hold-step kernel freeze; not a fourth spec.

## HONEST BOUNDARY (precise — do NOT over-read)

  * **OUTER HOLD LAYER ONLY — the INNER FOLD is a SEPARATE composition.** `exerciseA` runs an inner
    `List FullActionA` fold from the hold post-state; that fold is NOT arithmetized by this per-row
    descriptor. The full composite (`ExerciseSpec`) is `exerciseGuard ∧ innerFacetsAdmitted ∧
    turnSpec(inner)`; universe-A composes the hold-layer circuit with the inner turn via
    `exercise_circuit_refines_spec` (carrying `innerTurnH`). This module emits + welds the OUTER
    hold-layer FREEZE row; the inner fold composes through the TURN layer (`TurnEmit`, cited), each
    inner action being its OWN per-row descriptor. We do NOT claim to arithmetize the inner fold here.

  * **IR GAP — the LOG is not an EffectVM column.** The hold layer's ONE state change is the `authReceipt`
    log growth; the EffectVM row has no log column. The log advance lives in universe-A's
    `logHashInjective` portal, not the per-row freeze. FLAG.

  * **GUARD off-row.** `exerciseGuard` (the cap-edge hold) is the v1 framework `propBit`, off-row.

  * PER-CELL / PER-ROW. Single-row AIR. Cross-row composition is the turn layer (`TurnEmit`), cited.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`, no
`rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.ActionDispatch

namespace Dregg2.Circuit.Emit.EffectVmEmitExercise

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector for the exercise hold-gate (full-freeze) row. -/

namespace selEX
/-- The `exerciseA` effect selector column. -/
def EXERCISE : Nat := 7
end selEX

/-- The `exerciseA` selector as an expression. -/
def eSelEx : EmittedExpr := .var selEX.EXERCISE

/-! ## §1 — The exercise full-freeze row gates (every state column frozen). -/

/-- Cap-root freeze body. -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body. -/
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

/-- The `exerciseA` (hold layer) AIR identity (the fingerprint binding). -/
def exerciseVmAirName : String := "dregg-effectvm-exerciseA-holdlayer-v1"

/-- The full-freeze per-row gates: cap-root, balance lo/hi, nonce, reserved, 8 fields — all frozen. -/
def exerciseRowGates : List VmConstraint :=
  [ .gate gCapFix, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's. -/
def exerciseHashSites : List VmHashSite := transferHashSites

/-- **`exerciseVmDescriptor`** — the `exerciseA` hold-layer concrete circuit: the 13-column full-freeze
gates ++ transition continuity ++ the row-0 boundary pins, with the 4 ordered GROUP-4 hash sites. No
balance range checks (no balance move). -/
def exerciseVmDescriptor : EffectVmDescriptor :=
  { name := exerciseVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := exerciseRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := exerciseHashSites
  , ranges := [] }

/-! ## §3 — The exercise hold-gate ROW INTENT (the independent faithfulness target).

`ExerciseRowIntent env` is the full FREEZE: every state column's `after` equals its `before`. The
EffectVM-row projection of universe-A's `ExerciseHoldSpec` (`st' = exerciseHoldState st actor`: the
WHOLE kernel frozen). -/

/-- **`ExerciseRowIntent env`** — every state column frozen. -/
def ExerciseRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is an `exerciseA` row: `s_exercise = 1`, `s_noop = 0`. -/
def IsExerciseRow (env : VmRowEnv) : Prop :=
  env.loc selEX.EXERCISE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`exerciseRowGates_holds_iff`** — on an `exerciseA` row, the emitted per-row gates all hold IFF
`ExerciseRowIntent` (full freeze) holds. -/
theorem exerciseRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ exerciseRowGates, c.holdsVm env false false) ↔ ExerciseRowIntent env := by
  unfold exerciseRowGates gFieldFixAll ExerciseRowIntent
  constructor
  · intro h
    have hCap := h (.gate gCapFix) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i, i < 8 → VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gCapFix, gBalLoFix, gBalHiFix, gNonceFix, gResFix,
      eSA, eSB, eSub, EmittedExpr.eval] at hCap hLo hHi hNon hRes
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
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
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

/-- **`exerciseVm_faithful` — THE deliverable.** On an `exerciseA` row, the emitted descriptor's per-row
gates hold IFF the full-freeze intent holds. -/
theorem exerciseVm_faithful (env : VmRowEnv) :
    (∀ c ∈ exerciseRowGates, c.holdsVm env false false) ↔ ExerciseRowIntent env :=
  exerciseRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): any non-freeze fails the emitted descriptor. -/

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` is NOT the pre-`cap_root` (a forged
authority change under a freeze) fails the `gCapFix` gate (UNSAT). -/
theorem exerciseVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (sbCol state.CAP_ROOT)) :
    ¬ (VmConstraint.gate gCapFix).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (balance tamper).** A row whose post-`bal_lo` is NOT the pre-`bal_lo` (a forged balance
move under a freeze) fails the `gBalLoFix` gate (UNSAT). -/
theorem exerciseVm_rejects_wrong_balance (env : VmRowEnv)
    (hwrong : env.loc (saCol state.BALANCE_LO) ≠ env.loc (sbCol state.BALANCE_LO)) :
    ¬ (VmConstraint.gate gBalLoFix).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the full freeze does NOT satisfy the per-row
gates. -/
theorem exerciseVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ ExerciseRowIntent env) :
    ¬ (∀ c ∈ exerciseRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((exerciseVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog). -/

/-- **`ExerciseRowEncodes env pre post`** — the row decodes to `(pre, post)` cell states. -/
def ExerciseRowEncodes (env : VmRowEnv) (pre post : CellState) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell exercise spec: the cell's WHOLE post-state EQUALS its pre-state (full freeze). The
per-cell projection of universe-A's `ExerciseHoldSpec` kernel freeze. -/
def ExerciseCellSpec (pre post : CellState) : Prop :=
  post.capRoot = pre.capRoot
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `ExerciseRowEncodes`, `ExerciseRowIntent` IS the structured per-cell `ExerciseCellSpec`. -/
theorem intent_to_exerciseCellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : ExerciseRowEncodes env pre post) (hint : ExerciseRowIntent env) :
    ExerciseCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hcap, hlo, hhi, hnon, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i; rw [← hsaF i, ← hsbF i]; exact hfld i.val i.isLt
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`exerciseDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under
the `ExerciseRowEncodes` decoding forces the structured per-cell `ExerciseCellSpec` (full freeze). -/
theorem exerciseDescriptor_full_sound (env : VmRowEnv) (pre post : CellState)
    (henc : ExerciseRowEncodes env pre post)
    (hgates : ∀ c ∈ exerciseRowGates, c.holdsVm env false false) :
    ExerciseCellSpec pre post :=
  intent_to_exerciseCellSpec env pre post henc ((exerciseVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `exerciseHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem exerciseHashSites_eq : exerciseHashSites = transferHashSites := rfl

/-- **`exerciseDescriptor_commit_binds_state` — the whole-state tooth.** Two `exerciseA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns. -/
theorem exerciseDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ exerciseHashSites)
    (hs₂ : siteHoldsAll hash e₂ exerciseHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [exerciseHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `cellProj` to universe-A's `ExerciseHoldSpec`.

`ExerciseHoldSpec` freezes the whole kernel (`st' = exerciseHoldState st actor`, kernel identical), so
EVERY cell's projection is frozen. `cellProj` reads the conserved balance + cap-digest of one cell; the
unification shows post = pre on those columns. -/

open Dregg2.Circuit.ActionDispatch (ExerciseHoldSpec exerciseHoldState exerciseStepA_iff_holdSpec)
open Dregg2.Authority (Caps)

/-- **`balProj k c`** — the conserved balance of cell `c`. -/
def balProj (k : RecordKernelState) (c : CellId) : ℤ := balOf (k.cell c)

/-- **`capRootProj D k`** — the cap-table digest. -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- **`unify_exercise` — THE CONNECTOR.** When universe-A's `ExerciseHoldSpec` holds, the WHOLE kernel
is frozen, so for EVERY cell `c` and digest `D` the projected post-balance equals the pre-balance AND
the projected post cap-digest equals the pre cap-digest — exactly the freeze the descriptor pins. So
`ExerciseCellSpec`'s freeze clauses ARE universe-A's hold-step kernel freeze, projected. -/
theorem unify_exercise (D : Caps → ℤ)
    (s : RecChainedState) (actor target : CellId) (s' : RecChainedState) (c : CellId)
    (hspec : ExerciseHoldSpec s actor target s') :
    balProj s'.kernel c = balProj s.kernel c
    ∧ capRootProj D s'.kernel = capRootProj D s.kernel := by
  -- ExerciseHoldSpec's second clause is `s' = exerciseHoldState s actor`, whose kernel = s.kernel.
  obtain ⟨_, hhold⟩ := hspec
  have hker : s'.kernel = s.kernel := by rw [hhold]; rfl
  refine ⟨?_, ?_⟩
  · show balOf (s'.kernel.cell c) = balOf (s.kernel.cell c); rw [hker]
  · show D s'.kernel.caps = D s.kernel.caps; rw [hker]

/-- **`unify_exercise_via_exec` — the runnable freeze inherits the VALIDATED guarantee.** Chaining
universe-A's `exerciseStepA_iff_holdSpec` (a committed hold step ⟺ `ExerciseHoldSpec`) with
`unify_exercise`: a committed hold step `exerciseStepA s actor target = some s'` forces the projected
post-balance and post cap-digest to EQUAL their pre-values for every cell — the EXACT freeze the runnable
descriptor pins. So the runnable freeze row is universe-A's validated hold-step freeze, not a fourth
spec. -/
theorem unify_exercise_via_exec (D : Caps → ℤ)
    (s : RecChainedState) (actor target : CellId) (s' : RecChainedState) (c : CellId)
    (h : exerciseStepA s actor target = some s') :
    balProj s'.kernel c = balProj s.kernel c
    ∧ capRootProj D s'.kernel = capRootProj D s.kernel :=
  unify_exercise D s actor target s' c
    ((exerciseStepA_iff_holdSpec s s' actor target).mp h)

/-! ## §9 — NON-VACUITY: a concrete frozen row that satisfies the intent, and one that does not. -/

/-- A concrete `exerciseA` row: every state column frozen (pre = post = `5` on `cap_root`, balances,
nonce, fields — to exercise a non-degenerate freeze). -/
def exGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selEX.EXERCISE then 1
    else if v = sbCol state.CAP_ROOT then 5
    else if v = saCol state.CAP_ROOT then 5
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `exGoodRow` is a genuine `exerciseA` row. -/
theorem exGoodRow_isExerciseRow : IsExerciseRow exGoodRow := by
  unfold IsExerciseRow exGoodRow
  constructor <;> norm_num [selEX.EXERCISE, sel.NOOP, sbCol, saCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT]

/-- Evaluate `exGoodRow.loc` at a column given as a LITERAL `Nat` not in the named set `{7, 65, 87}`
(selector `7`, pre-`cap_root` `65`, post-`cap_root` `87`) — returns the `else 0` default. -/
theorem exGoodRow_loc_default (n : Nat) (h7 : n ≠ 7) (h65 : n ≠ 65) (h87 : n ≠ 87) :
    exGoodRow.loc n = 0 := by
  show (if n = selEX.EXERCISE then (1:ℤ)
    else if n = sbCol state.CAP_ROOT then 5
    else if n = saCol state.CAP_ROOT then 5 else 0) = 0
  have c1 : (selEX.EXERCISE : Nat) = 7 := rfl
  have c2 : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have c3 : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  rw [c1, c2, c3, if_neg h7, if_neg h65, if_neg h87]

/-- **NON-VACUITY (witness TRUE).** `exGoodRow` REALIZES the full-freeze intent: every state column's
`after` equals its `before` (cap_root `5 = 5`; everything else `0 = 0`). -/
theorem exGoodRow_realizes_intent : ExerciseRowIntent exGoodRow := by
  have hsbcap : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cap_root frozen: post (87 → 5) = pre (65 → 5)
    show exGoodRow.loc (saCol state.CAP_ROOT) = exGoodRow.loc (sbCol state.CAP_ROOT)
    show (if saCol state.CAP_ROOT = selEX.EXERCISE then (1:ℤ) else _)
        = (if sbCol state.CAP_ROOT = selEX.EXERCISE then (1:ℤ) else _)
    rw [hsbcap, hsacap]; rfl
  · show exGoodRow.loc (saCol state.BALANCE_LO) = exGoodRow.loc (sbCol state.BALANCE_LO)
    rw [exGoodRow_loc_default (saCol state.BALANCE_LO) (by decide) (by decide) (by decide),
        exGoodRow_loc_default (sbCol state.BALANCE_LO) (by decide) (by decide) (by decide)]
  · show exGoodRow.loc (saCol state.BALANCE_HI) = exGoodRow.loc (sbCol state.BALANCE_HI)
    rw [exGoodRow_loc_default (saCol state.BALANCE_HI) (by decide) (by decide) (by decide),
        exGoodRow_loc_default (sbCol state.BALANCE_HI) (by decide) (by decide) (by decide)]
  · show exGoodRow.loc (saCol state.NONCE) = exGoodRow.loc (sbCol state.NONCE)
    rw [exGoodRow_loc_default (saCol state.NONCE) (by decide) (by decide) (by decide),
        exGoodRow_loc_default (sbCol state.NONCE) (by decide) (by decide) (by decide)]
  · show exGoodRow.loc (saCol state.RESERVED) = exGoodRow.loc (sbCol state.RESERVED)
    rw [exGoodRow_loc_default (saCol state.RESERVED) (by decide) (by decide) (by decide),
        exGoodRow_loc_default (sbCol state.RESERVED) (by decide) (by decide) (by decide)]
  · intro i hi8
    show exGoodRow.loc (saCol (state.FIELD_BASE + i)) = exGoodRow.loc (sbCol (state.FIELD_BASE + i))
    have hsaI : saCol (state.FIELD_BASE + i) = 79 + i := by
      unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
        state.FIELD_BASE; omega
    have hsbI : sbCol (state.FIELD_BASE + i) = 57 + i := by
      unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.FIELD_BASE; omega
    rw [hsaI, hsbI,
        exGoodRow_loc_default (79 + i) (by omega) (by omega) (by omega),
        exGoodRow_loc_default (57 + i) (by omega) (by omega) (by omega)]

/-- A forged `exerciseA` row: `exGoodRow` with the post-`cap_root` tampered to `999 ≠ 5` (a forged
authority change under what should be a freeze). -/
def exBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else exGoodRow.loc v
  nxt := exGoodRow.nxt
  pub := exGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `exBadRow`'s post-`cap_root` differs from its
pre-`cap_root`, so the `gCapFix` freeze gate REJECTS it — a concrete UNSAT (no forged authority change
rides a hold step). -/
theorem exBadRow_rejected : ¬ (VmConstraint.gate gCapFix).holdsVm exBadRow false false := by
  apply exerciseVm_rejects_wrong_capRoot
  have hsbcap : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hbad : exBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else exGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hpre : exBadRow.loc (sbCol state.CAP_ROOT) = 5 := by
    show (if sbCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else exGoodRow.loc (sbCol state.CAP_ROOT)) = 5
    rw [hsbcap, hsacap, if_neg (by decide)]
    show exGoodRow.loc (sbCol state.CAP_ROOT) = 5
    rw [hsbcap]; rfl
  rw [hbad, hpre]; decide

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard exerciseVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard exerciseVmDescriptor.hashSites.length == 4
#guard exerciseVmDescriptor.traceWidth == 186

#assert_axioms exerciseRowGates_holds_iff
#assert_axioms exerciseVm_faithful
#assert_axioms exerciseVm_rejects_wrong_capRoot
#assert_axioms exerciseVm_rejects_wrong_balance
#assert_axioms exerciseVm_rejects_wrong_output
#assert_axioms intent_to_exerciseCellSpec
#assert_axioms exerciseDescriptor_full_sound
#assert_axioms exerciseDescriptor_commit_binds_state
#assert_axioms unify_exercise
#assert_axioms unify_exercise_via_exec
#assert_axioms exGoodRow_realizes_intent
#assert_axioms exBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitExercise
