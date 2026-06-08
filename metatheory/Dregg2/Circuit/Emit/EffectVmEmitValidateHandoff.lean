/-
# Dregg2.Circuit.Emit.EffectVmEmitValidateHandoff — the AUTHORITY validate-handoff effect
  `validateHandoffA`, EMITTED onto the runnable EffectVM `cap_root` column, with its full-state
  soundness and the connector to the validated universe-A `DelegateSpec` /
  `execFullA_validateHandoff_iff_spec`.

## The "ONE circuit" thesis (REUSES the `attenuateA` / `dropRefA` cap-graph LOCAL TEMPLATE)

`validateHandoffA` (`Inst/validateHandoffA.lean`, `Spec/authorityunattenuated.lean`) is the Granovetter
introduce skeleton of the authority-unattenuated family. It rewrites the `caps` table to the
NON-amplifying held-cap copy (`recDelegateCaps caps intro recip tgt = grant caps recip (heldCapTo caps
intro tgt)` — `recip` gains exactly the cap `intro` already holds to `tgt`, no amplification), prepends
one authority receipt to the log, and freezes the 16 non-`caps` kernel fields. Its validation
`validateHandoffA_full_sound ⇒ DelegateSpec` is DONE; this module emits the SAME effect onto the running
EffectVM row layout and welds the two.

Like `attenuateA`/`dropRefA`, `validateHandoffA` is a `caps`-FUNCTION-field move, so at the row level it
is a `cap_root` COLUMN MOVE (state offset 11): the post `cap_root` is the digest of the post cap-table
(`recDelegateCaps`-granted), every OTHER state column frozen, and the post-state bound into the published
`state_commit` (`site2` absorbs `cap_root`) under Poseidon2 CR.

`validateHandoffVmDescriptor` emits exactly that: post `cap_root` pinned to a parameter
`paramVH.CAP_DIGEST_NEW` (the runnable column the witness generator fills with `D (recDelegateCaps …)`),
the move gate `new_cap_root - capDigestNew = 0`, and the frame (balance limbs / nonce / 8 fields /
reserved) frozen. We PROVE: satisfying the descriptor pins the full per-cell post-state `↔` the row
intent `HandoffRowIntent`; the GROUP-4 sites bind the WHOLE post-state into `state_commit` — so a
tampered post-`cap_root` that still claims `NEW_COMMIT` is UNSAT (the anti-ghost tooth, REUSED from the
transfer keystone).

## The CONNECTOR — `capRootProj` to universe-A's `DelegateSpec`

`capRootProj D k = D k.caps` reads the SAME whole-function digest universe-A's `capsComponent D hD`
uses. `unify_handoff` shows: when `DelegateSpec` holds (so `k'.caps = recDelegateCaps k.caps intro recip
tgt`), the projected post-`cap_root` is EXACTLY `D (recDelegateCaps k.caps intro recip tgt)` — the column
move the descriptor pins. So the runnable `cap_root` transition IS universe-A's `caps`-digest
transition; not a fourth spec.

## HONEST BOUNDARY (precise — do NOT over-read)

  * **IR GAP — needs IR extension: cap-table hash-site (inherited from `attenuateA`).** `cap_root` is the
    SCALAR digest `D caps`, not re-derived in-circuit. The descriptor PINS the `cap_root` column
    transition `new_cap_root = D(post.caps)` and binds that column into `state_commit`, but does NOT
    prove in-circuit that `cap_root` IS the genuine Merkle digest of the post cap-table. That binding
    lives in universe-A's `Function.Injective D` portal (the SAME bar `validateHandoffA_full_sound`
    uses). We connect through `capRootProj`. FLAG: a future IR extension would internalize it.

  * **NON-AMPLIFICATION is a property of `recDelegateCaps`, NOT a per-row gate.** The Granovetter
    no-amplification guarantee (`recip` gains only `intro`'s held cap, attenuated, never more) lives in
    the DEFINITION of `recDelegateCaps` (universe-A's `delegate`-family algebra), which the witness
    digest `D (recDelegateCaps …)` is a function of. The per-row circuit pins `cap_root` to THAT digest;
    it does NOT re-derive the grant-algebra in-circuit. Reported, not papered.

  * **IR GAP — the LOG is not an EffectVM column.** The `authReceipt` log growth has no EffectVM column;
    it lives in universe-A's `logHashInjective` portal, not the per-row circuit. FLAG.

  * **GUARD off-row.** `delegateGuard` (the Granovetter connectivity premise — `intro` already holds a
    `tgt`-conferring cap) is the v2 framework `propBit`, off-row.

  * PER-CELL / PER-ROW. Single-row AIR. Cross-row composition is the turn layer (`TurnEmit`), cited.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`; the cap-table digest ONLY as `Function.Injective D`. No
`sorry`, no `:= True`, no `native_decide`, no `rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.authorityunattenuated

namespace Dregg2.Circuit.Emit.EffectVmEmitValidateHandoff

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

/-! ## §0 — Selector + param offsets for the cap-graph handoff row.

`validateHandoffA` has its own per-effect selector (`selVH.VALIDATE_HANDOFF`). The post cap-digest the
row pins is carried in a parameter column `paramVH.CAP_DIGEST_NEW`. -/

namespace selVH
/-- The `validateHandoffA` effect selector column. -/
def VALIDATE_HANDOFF : Nat := 8
end selVH

namespace paramVH
/-- The post cap-table digest parameter: the value the witness fills with `D (post.caps)`. -/
def CAP_DIGEST_NEW : Nat := 6
end paramVH

/-- The `validateHandoffA` selector as an expression. -/
def eSelVH : EmittedExpr := .var selVH.VALIDATE_HANDOFF

/-- The post-cap-digest param as an expression. -/
def eCapDigestNew : EmittedExpr := .var (prmCol paramVH.CAP_DIGEST_NEW)

/-! ## §1 — The cap-graph row gates (the running prover's, specialized to the row).

The handoff effect MOVES `cap_root` to the post cap-table digest and FREEZES the rest of the block. -/

/-- Cap-root MOVE body: `new_cap_root - capDigestNew`. -/
def gCapMove : EmittedExpr := eSub (eSA state.CAP_ROOT) eCapDigestNew

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body (a handoff does NOT tick the cell nonce). -/
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

/-- The `validateHandoffA` AIR identity (the fingerprint binding). -/
def validateHandoffVmAirName : String := "dregg-effectvm-validateHandoffA-v2"

/-- The cap-graph per-row gates: cap-root MOVE, balance/nonce/reserved freeze, 8 fields freeze. -/
def handoffRowGates : List VmConstraint :=
  [ .gate gCapMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gResFix ] ++ gFieldFixAll

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's (the moved `cap_root` is
absorbed by site 2). -/
def handoffHashSites : List VmHashSite := transferHashSites

/-- **`validateHandoffVmDescriptor`** — the `validateHandoffA` effect's concrete circuit, emitted through
the EffectVM IR: the cap-root MOVE + frame-freeze gates ++ transition continuity ++ the row-0 boundary
pins, with the 4 ordered GROUP-4 hash sites. No balance range checks (no balance move). -/
def validateHandoffVmDescriptor : EffectVmDescriptor :=
  { name := validateHandoffVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := handoffRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := handoffHashSites
  , ranges := [] }

/-! ## §3 — The cap-graph ROW INTENT (the independent faithfulness target).

`HandoffRowIntent env` is the field-level cap-graph move: post `cap_root` IS the supplied post
cap-digest, the balance limbs / nonce / reserved / 8 fields FIXED. The EffectVM-row projection of
`DelegateSpec`'s `caps` clause (the whole-function `caps` equality ⟹ cap-DIGEST column) + the 16-field
freeze. -/

/-- **`HandoffRowIntent env`** — post `cap_root` is the post-cap-digest param, frame frozen. -/
def HandoffRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol state.CAP_ROOT) = env.loc (prmCol paramVH.CAP_DIGEST_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i < 8, env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a `validateHandoffA` row: `s_validateHandoff = 1`, `s_noop = 0`. -/
def IsHandoffRow (env : VmRowEnv) : Prop :=
  env.loc selVH.VALIDATE_HANDOFF = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`handoffRowGates_holds_iff`** — on a `validateHandoffA` row, the emitted per-row gates all hold IFF
`HandoffRowIntent` holds. -/
theorem handoffRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ handoffRowGates, c.holdsVm env false false) ↔ HandoffRowIntent env := by
  unfold handoffRowGates gFieldFixAll HandoffRowIntent
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

/-- **`handoffVm_faithful` — THE deliverable.** On a `validateHandoffA` row, the emitted descriptor's
per-row gates hold IFF the cap-graph handoff intent holds. -/
theorem handoffVm_faithful (env : VmRowEnv) :
    (∀ c ∈ handoffRowGates, c.holdsVm env false false) ↔ HandoffRowIntent env :=
  handoffRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row). -/

/-- **Anti-ghost (cap-root tamper).** A row whose post-`cap_root` is NOT the supplied digest fails the
`gCapMove` gate (UNSAT). -/
theorem handoffVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT) ≠ env.loc (prmCol paramVH.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gCapMove, eSA, eCapDigestNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem handoffVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ HandoffRowIntent env) :
    ¬ (∀ c ∈ handoffRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((handoffVm_faithful env).mp h)

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
  ∧ env.loc (prmCol paramVH.CAP_DIGEST_NEW) = capDigestNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell cap-graph spec: the moved cell's WHOLE post-state is `pre` with `cap_root` set to the
new cap-digest, every other field frozen. The per-cell projection of universe-A's `DelegateSpec`. -/
def CapCellSpec (pre post : CellState) (capDigestNew : ℤ) : Prop :=
  post.capRoot = capDigestNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, post.fields i = pre.fields i)
  ∧ post.reserved = pre.reserved

/-- Under `CapRowEncodes`, `HandoffRowIntent` IS the structured per-cell `CapCellSpec`. -/
theorem intent_to_capCellSpec (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew) (hint : HandoffRowIntent env) :
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

/-- **`handoffDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under the
`CapRowEncodes` decoding forces the structured per-cell `CapCellSpec`. -/
theorem handoffDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ handoffRowGates, c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  intent_to_capCellSpec env pre post capDigestNew henc ((handoffVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, cap-root included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `handoffHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem handoffHashSites_eq : handoffHashSites = transferHashSites := rfl

/-- **`handoffDescriptor_commit_binds_state` — the whole-state tooth.** Two `validateHandoffA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved
post-`cap_root` (an absorbed column, site 2) included. -/
theorem handoffDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ handoffHashSites)
    (hs₂ : siteHoldsAll hash e₂ handoffHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [handoffHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `capRootProj` to universe-A's `DelegateSpec`.

`capRootProj D k = D k.caps` reads the SAME whole-function digest universe-A's `capsComponent D hD`
uses. A committed `DelegateSpec` makes the projected post-`cap_root` EXACTLY `D (recDelegateCaps k.caps
intro recip tgt)` — the column move the descriptor pins. -/

open Dregg2.Circuit.Spec.AuthorityUnattenuated
  (DelegateSpec recDelegateCaps execFullA_validateHandoff_iff_spec)

/-- **`capRootProj D k`** — the EffectVM `cap_root` column value for kernel state `k`: `D k.caps`. -/
def capRootProj (D : Caps → ℤ) (k : RecordKernelState) : ℤ := D k.caps

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries: `D` of the
`recDelegateCaps`-granted cap-table. -/
def handoffCapDigestNew (D : Caps → ℤ) (k : RecordKernelState) (intro recip tgt : CellId) : ℤ :=
  D (recDelegateCaps k.caps intro recip tgt)

/-- **`unify_handoff` — THE CONNECTOR.** When universe-A's `DelegateSpec` holds, the projected
post-`cap_root` is EXACTLY `handoffCapDigestNew D k intro recip tgt` — the column move the descriptor
pins. So `CapCellSpec`'s `cap_root` clause IS universe-A's `caps`-clause, projected to the digest column.
(The non-amplification guarantee lives in `recDelegateCaps`'s definition, which the digest is a function
of — see the honest boundary.) -/
theorem unify_handoff (D : Caps → ℤ)
    (s : RecChainedState) (intro recip tgt : CellId) (s' : RecChainedState)
    (hspec : DelegateSpec s intro recip tgt s') :
    capRootProj D s'.kernel = handoffCapDigestNew D s.kernel intro recip tgt := by
  -- DelegateSpec's caps clause is `s'.kernel.caps = recDelegateCaps s.kernel.caps intro recip tgt`.
  obtain ⟨_, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (recDelegateCaps s.kernel.caps intro recip tgt)
  rw [hcaps]

/-- **`unify_handoff_via_exec` — the runnable column move inherits the VALIDATED guarantee.** Chaining
universe-A's `execFullA_validateHandoff_iff_spec` (a committed executor handoff ⟹ `DelegateSpec`) with
`unify_handoff`: a committed `validateHandoffA` forces the projected post-`cap_root` to the
`recDelegateCaps`-granted cap-digest — the EXACT column value the runnable descriptor's
`param.CAP_DIGEST_NEW` carries. So the runnable `cap_root` move is universe-A's validated `caps`
transition, not a fourth spec. -/
theorem unify_handoff_via_exec (D : Caps → ℤ)
    (s : RecChainedState) (intro recip tgt : CellId) (s' : RecChainedState)
    (h : execFullA s (.validateHandoffA intro recip tgt) = some s') :
    capRootProj D s'.kernel = handoffCapDigestNew D s.kernel intro recip tgt :=
  unify_handoff D s intro recip tgt s' ((execFullA_validateHandoff_iff_spec s intro recip tgt s').mp h)

/-! ## §9 — NON-VACUITY: a concrete cap-graph row that satisfies the intent, and one that does not. -/

/-- A concrete `validateHandoffA` row: `cap_root 11 → 77` (the new digest), frame frozen at `0`. -/
def handoffGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selVH.VALIDATE_HANDOFF then 1
    else if v = sbCol state.CAP_ROOT then 11
    else if v = saCol state.CAP_ROOT then 77
    else if v = prmCol paramVH.CAP_DIGEST_NEW then 77
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `handoffGoodRow` is a genuine `validateHandoffA` row. -/
theorem handoffGoodRow_isHandoffRow : IsHandoffRow handoffGoodRow := by
  unfold IsHandoffRow handoffGoodRow
  constructor <;> norm_num [selVH.VALIDATE_HANDOFF, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.CAP_ROOT,
    paramVH.CAP_DIGEST_NEW]

/-- Evaluate `handoffGoodRow.loc` at a column given as a LITERAL `Nat` not in the named set
`{8, 65, 87, 74}` (selector `8`, pre-`cap_root` `65`, post-`cap_root` `87`, cap-digest param `74`). -/
theorem handoffGoodRow_loc_default (n : Nat)
    (h8 : n ≠ 8) (h65 : n ≠ 65) (h87 : n ≠ 87) (h74 : n ≠ 74) :
    handoffGoodRow.loc n = 0 := by
  show (if n = selVH.VALIDATE_HANDOFF then (1:ℤ)
    else if n = sbCol state.CAP_ROOT then 11
    else if n = saCol state.CAP_ROOT then 77
    else if n = prmCol paramVH.CAP_DIGEST_NEW then 77 else 0) = 0
  have c1 : (selVH.VALIDATE_HANDOFF : Nat) = 8 := rfl
  have c2 : sbCol state.CAP_ROOT = 65 := by
    unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.CAP_ROOT; rfl
  have c3 : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have c4 : prmCol paramVH.CAP_DIGEST_NEW = 74 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramVH.CAP_DIGEST_NEW; rfl
  rw [c1, c2, c3, c4, if_neg h8, if_neg h65, if_neg h87, if_neg h74]

/-- **NON-VACUITY (witness TRUE).** `handoffGoodRow` REALIZES the cap-graph intent: post `cap_root = 77`
= the param digest, balance/nonce/reserved/fields frozen at `0`. -/
theorem handoffGoodRow_realizes_intent : HandoffRowIntent handoffGoodRow := by
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramVH.CAP_DIGEST_NEW = 74 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramVH.CAP_DIGEST_NEW; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post cap_root (87 → 77) = cap-digest param (74 → 77)
    show handoffGoodRow.loc (saCol state.CAP_ROOT) = handoffGoodRow.loc (prmCol paramVH.CAP_DIGEST_NEW)
    rw [hsacap, hprm]; rfl
  · show handoffGoodRow.loc (saCol state.BALANCE_LO) = handoffGoodRow.loc (sbCol state.BALANCE_LO)
    rw [handoffGoodRow_loc_default (saCol state.BALANCE_LO) (by decide) (by decide) (by decide) (by decide),
        handoffGoodRow_loc_default (sbCol state.BALANCE_LO) (by decide) (by decide) (by decide) (by decide)]
  · show handoffGoodRow.loc (saCol state.BALANCE_HI) = handoffGoodRow.loc (sbCol state.BALANCE_HI)
    rw [handoffGoodRow_loc_default (saCol state.BALANCE_HI) (by decide) (by decide) (by decide) (by decide),
        handoffGoodRow_loc_default (sbCol state.BALANCE_HI) (by decide) (by decide) (by decide) (by decide)]
  · show handoffGoodRow.loc (saCol state.NONCE) = handoffGoodRow.loc (sbCol state.NONCE)
    rw [handoffGoodRow_loc_default (saCol state.NONCE) (by decide) (by decide) (by decide) (by decide),
        handoffGoodRow_loc_default (sbCol state.NONCE) (by decide) (by decide) (by decide) (by decide)]
  · show handoffGoodRow.loc (saCol state.RESERVED) = handoffGoodRow.loc (sbCol state.RESERVED)
    rw [handoffGoodRow_loc_default (saCol state.RESERVED) (by decide) (by decide) (by decide) (by decide),
        handoffGoodRow_loc_default (sbCol state.RESERVED) (by decide) (by decide) (by decide) (by decide)]
  · intro i hi8
    show handoffGoodRow.loc (saCol (state.FIELD_BASE + i)) = handoffGoodRow.loc (sbCol (state.FIELD_BASE + i))
    have hsaI : saCol (state.FIELD_BASE + i) = 79 + i := by
      unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
        state.FIELD_BASE; omega
    have hsbI : sbCol (state.FIELD_BASE + i) = 57 + i := by
      unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.FIELD_BASE; omega
    rw [hsaI, hsbI,
        handoffGoodRow_loc_default (79 + i) (by omega) (by omega) (by omega) (by omega),
        handoffGoodRow_loc_default (57 + i) (by omega) (by omega) (by omega) (by omega)]

/-- A forged `validateHandoffA` row: `handoffGoodRow` with the post-`cap_root` tampered to `999 ≠ 77`. -/
def handoffBadRow : VmRowEnv where
  loc := fun v => if v = saCol state.CAP_ROOT then 999 else handoffGoodRow.loc v
  nxt := handoffGoodRow.nxt
  pub := handoffGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `handoffBadRow`'s post-`cap_root` is NOT the
param digest, so the `gCapMove` gate REJECTS it — a concrete UNSAT (no forged authority grant rides a
handoff). -/
theorem handoffBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm handoffBadRow false false := by
  apply handoffVm_rejects_wrong_capRoot
  have hsacap : saCol state.CAP_ROOT = 87 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.CAP_ROOT; rfl
  have hprm : prmCol paramVH.CAP_DIGEST_NEW = 74 := by
    unfold prmCol PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE paramVH.CAP_DIGEST_NEW; rfl
  have hbad : handoffBadRow.loc (saCol state.CAP_ROOT) = 999 := by
    show (if saCol state.CAP_ROOT = saCol state.CAP_ROOT then (999:ℤ)
      else handoffGoodRow.loc (saCol state.CAP_ROOT)) = 999
    rw [if_pos rfl]
  have hparam : handoffBadRow.loc (prmCol paramVH.CAP_DIGEST_NEW) = 77 := by
    show (if prmCol paramVH.CAP_DIGEST_NEW = saCol state.CAP_ROOT then (999:ℤ)
      else handoffGoodRow.loc (prmCol paramVH.CAP_DIGEST_NEW)) = 77
    rw [hsacap, hprm, if_neg (by decide)]
    show handoffGoodRow.loc (prmCol paramVH.CAP_DIGEST_NEW) = 77
    rw [hprm]; rfl
  rw [hbad, hparam]; decide

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard validateHandoffVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard validateHandoffVmDescriptor.hashSites.length == 4
#guard validateHandoffVmDescriptor.traceWidth == 186

#assert_axioms handoffRowGates_holds_iff
#assert_axioms handoffVm_faithful
#assert_axioms handoffVm_rejects_wrong_capRoot
#assert_axioms handoffVm_rejects_wrong_output
#assert_axioms intent_to_capCellSpec
#assert_axioms handoffDescriptor_full_sound
#assert_axioms handoffDescriptor_commit_binds_state
#assert_axioms unify_handoff
#assert_axioms unify_handoff_via_exec
#assert_axioms handoffGoodRow_realizes_intent
#assert_axioms handoffBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitValidateHandoff
