/-
# Dregg2.Circuit.Emit.EffectVmEmitSetPermissions — the CELL-STATE-PERMISSIONS effect `setPermissionsA`,
  EMITTED onto a runnable EffectVM `field` column, with its full-state soundness and the connector to
  the validated universe-A `SetPermissionsSpec` / `execFullA_setPermissions_iff_spec`.

## The "ONE circuit" thesis for the field-write effects (this follows the `attenuateA` LOCAL TEMPLATE)

`setPermissionsA` (`Inst/setPermissionsA.lean`, `Spec/cellstatepermissions.lean`) writes ONE cell's
`permissions` record-slot to a value `p`, prepends one self-targeted receipt row to the log, and freezes
the 16 non-`cell` kernel fields. Its validation `setPermissionsA_full_sound ⇒ SetPermissionsSpec` is
DONE. This module emits the SAME effect onto the running EffectVM row layout and welds the two.

The EffectVM state block carries an 8-wide `field` array (`state.FIELD_BASE .. +7`), absorbed into the
GROUP-4 state-commitment chain (sites 0/1/2 read the field columns). A protocol-managed metadata write
is therefore a `field`-COLUMN MOVE: the post `field[k]` is the written value, every OTHER state column
frozen, and the post-state bound into the published `state_commit` under Poseidon2 CR. We designate
`field[0]` (`state.FIELD_BASE + 0`) as the EffectVM column that carries the cell's `permissions` scalar
— the SAME `fieldOf permsField` measure universe-A's `setPermsCellMap` writes. (`fieldOf` reads a record
field as `ℤ`, exactly like `balOf`/`nonceOf`.)

`setPermsVmDescriptor` emits exactly that: post `field[0]` pinned to a parameter `param.PERMS_NEW` (the
runnable column the witness generator fills with `p`), the move gate `new_field0 - permsNew = 0`, and
the frame (balance limbs / nonce / cap_root / reserved / field[1..7]) frozen. We PROVE: satisfying the
descriptor pins the full per-cell post-state (`field[0]` moved to `p`, frame frozen) `↔` the row intent
`SetPermsRowIntent`; the GROUP-4 sites bind the WHOLE post-state (the moved `field[0]` included) into
`state_commit` — so a tampered post-`field[0]` that still claims `NEW_COMMIT` is UNSAT (the anti-ghost
tooth, REUSED from the transfer keystone since `field[0]` IS an absorbed column, site 0).

## The CONNECTOR — `permProj` to universe-A's `SetPermissionsSpec`

`permProj k c = fieldOf permsField (k.cell c)` reads the SAME `permissions` scalar universe-A's
`setPermsCellMap` writes. `unify_setPerms` shows: when `SetPermissionsSpec` holds, the projected
post-`permissions` of the touched `cell` is EXACTLY `p` — i.e. the column move the descriptor pins. So
the runnable `field[0]` column transition IS universe-A's `permissions`-write transition; not a fourth
spec.

## HONEST BOUNDARY (precise — do NOT over-read)

  * **IR GAP — the LOG is not an EffectVM column.** `setPermissionsA` GROWS the receipt log by one
    self-targeted row; the EffectVM row layout (186 cols) has NO log column / no log-hash site. So the
    runnable descriptor pins the cell's `permissions` field-column move + frame freeze + the
    commitment binding, but it does NOT pin the log extension. That receipt-chain growth lives in
    universe-A's `logHashInjective` portal (`setPermissionsA_full_sound`'s `hLog`), the SAME bar the
    validated soundness uses. We connect to the FIELD move; we do NOT claim a log-hash site the IR
    cannot express. FLAG: a future IR extension (a `VmHashSite` over a log column) would internalize it.

  * **FIELD-COLUMN designation.** Universe-A's `permissions` is a record slot read by `fieldOf
    permsField`; we map it to EffectVM `field[0]`. This is a NAMED column choice (the witness generator
    must place `permissions` at `field[0]`); the soundness is about THAT column. The other 7 field
    columns are frozen and carry no universe-A analogue on this effect (projected `0`).

  * **GUARD off-row.** The three-leg admissibility gate (authority ∧ membership ∧ liveness) is
    universe-A's `setPermsGuard`, committed as a `propBit` in the v1 framework — NOT an EffectVM per-row
    arithmetic gate here. The runnable row descriptor pins the STATE TRANSITION; the guard is the v1
    framework's separate obligation (cited, `setPermissionsA_full_sound`). The connector fires under a
    committed `execFullA`, which already carries the guard.

  * PER-CELL / PER-ROW. Single-row AIR. Cross-row composition is the turn layer (`TurnEmit`), cited.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone);
    pinned only by its per-row passthrough gate.

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`, no
`rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstatepermissions

namespace Dregg2.Circuit.Emit.EffectVmEmitSetPermissions

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA ePrm eSub site0 site1 site2 site3 transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + param offsets for the field-write effect row.

The running EffectVM lays one selector per effect; `setPermissionsA` has its own selector index. We name
it `selSP.SET_PERMS` abstractly (the exact index is the running prover's; we keep transfer's gating
discipline: on a genuine row that selector is `1` and `s_noop = 0`). The written value is carried in a
parameter column `paramSP.PERMS_NEW`. -/

namespace selSP
/-- The `setPermissionsA` effect selector column. -/
def SET_PERMS : Nat := 3
end selSP

namespace paramSP
/-- The new permissions value parameter (the witness fills it with `p`). -/
def PERMS_NEW : Nat := 3
end paramSP

/-- The designated EffectVM `field` offset that carries the cell's `permissions` scalar. -/
def PERMS_FIELD : Nat := 0

/-- The `setPermissionsA` selector as an expression. -/
def eSelSP : EmittedExpr := .var selSP.SET_PERMS

/-- The new-permissions param as an expression. -/
def ePermsNew : EmittedExpr := .var (prmCol paramSP.PERMS_NEW)

/-! ## §1 — The field-write row gates (the running prover's, specialized to the row).

The effect MOVES `field[0]` (the permissions column) to the supplied param and FREEZES the rest of the
block. Mirror of the `attenuateA` gate set, with the cap-root move replaced by a `field[0]` move and the
cap-root frozen. -/

/-- Field[0] (permissions) MOVE body: `new_field0 - permsNew`. -/
def gPermMove : EmittedExpr := eSub (eSA (state.FIELD_BASE + PERMS_FIELD)) ePermsNew

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body (a metadata write does NOT tick the nonce — matches the executor, which rewrites
only the `permissions` slot). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Cap-root freeze body (a permissions write edits NO capability). -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` freeze body (for the 7 NON-permissions field columns, `i = 1..7`). -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The seven field-freeze gates (field[1..7]; field[0] MOVES). -/
def gFieldFixRest : List VmConstraint :=
  (List.range 7).map (fun a => VmConstraint.gate (gFieldFix (a + 1)))

/-! ## §2 — The emitted descriptor. -/

/-- The `setPermissionsA` AIR identity (the fingerprint binding). -/
def setPermsVmAirName : String := "dregg-effectvm-setPermissionsA-v1"

/-- The per-row gates: field[0] MOVE, balance/nonce/cap/reserved freeze, field[1..7] freeze. -/
def setPermsRowGates : List VmConstraint :=
  [ .gate gPermMove, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gCapFix, .gate gResFix ] ++ gFieldFixRest

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's (field[0] is absorbed by
site 0, so the moved permissions column is bound into `state_commit` exactly as transfer binds it). -/
def setPermsHashSites : List VmHashSite := transferHashSites

/-- **`setPermsVmDescriptor`** — the `setPermissionsA` effect's concrete circuit, emitted through the
EffectVM IR: the permissions field MOVE + frame-freeze gates ++ transition continuity ++ the row-0
boundary pins, with the 4 ordered GROUP-4 hash sites. No balance range checks (no balance move). -/
def setPermsVmDescriptor : EffectVmDescriptor :=
  { name := setPermsVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := setPermsRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := setPermsHashSites
  , ranges := [] }

/-! ## §3 — The field-write ROW INTENT (the independent faithfulness target).

`SetPermsRowIntent env` is the field-level metadata move: post `field[0]` IS the supplied param, and the
balance limbs / nonce / cap_root / reserved / field[1..7] are FIXED. This is the EffectVM-row projection
of universe-A's `SetPermissionsSpec` (`permissions`-slot write ⟹ the permissions field-column move; the
16-field/balance freeze ⟹ the row's frozen columns). -/

/-- **`SetPermsRowIntent env`** — the intended metadata move on the row `env.loc`: post `field[0]` is the
param value, frame frozen. -/
def SetPermsRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol (state.FIELD_BASE + PERMS_FIELD)) = env.loc (prmCol paramSP.PERMS_NEW)
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i, 1 ≤ i → i < 8 →
      env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a `setPermissionsA` row: `s_setPerms = 1`, `s_noop = 0`. -/
def IsSetPermsRow (env : VmRowEnv) : Prop :=
  env.loc selSP.SET_PERMS = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`setPermsRowGates_holds_iff`** — on a `setPermissionsA` row, the emitted per-row gates all hold IFF
`SetPermsRowIntent` holds. The gate bodies are the running prover's polynomials (field move + frame
freeze); they pin EXACTLY the intent move. -/
theorem setPermsRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ setPermsRowGates, c.holdsVm env false false) ↔ SetPermsRowIntent env := by
  unfold setPermsRowGates gFieldFixRest SetPermsRowIntent
  constructor
  · intro h
    have hPerm := h (.gate gPermMove) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ a, a < 7 →
        VmConstraint.holdsVm env false false (.gate (gFieldFix (a + 1))) := by
      intro a ha
      apply h
      simp only [List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨a, ha, rfl⟩
    simp only [VmConstraint.holdsVm, gPermMove, gBalLoFix, gBalHiFix, gNonceFix, gCapFix, gResFix,
      eSA, eSB, ePermsNew, eSub, EmittedExpr.eval] at hPerm hLo hHi hNon hCap hRes
    refine ⟨by linarith [hPerm], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi1 hi8
    have := hFld (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi1] at this
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hPerm, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
      List.mem_range] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨a, ha, rfl⟩
    · simp only [VmConstraint.holdsVm, gPermMove, eSA, ePermsNew, eSub, EmittedExpr.eval]
      rw [hPerm]; ring
    · simp only [VmConstraint.holdsVm, gBalLoFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hLo]; ring
    · simp only [VmConstraint.holdsVm, gBalHiFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hHi]; ring
    · simp only [VmConstraint.holdsVm, gNonceFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hNon]; ring
    · simp only [VmConstraint.holdsVm, gCapFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hCap]; ring
    · simp only [VmConstraint.holdsVm, gResFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hRes]; ring
    · simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval]
      rw [hFld (a + 1) (by omega) (by omega)]; ring

/-- **`setPermsVm_faithful` — THE deliverable.** On a `setPermissionsA` row, the emitted descriptor's
per-row gates hold IFF the metadata move intent holds. -/
theorem setPermsVm_faithful (env : VmRowEnv) :
    (∀ c ∈ setPermsRowGates, c.holdsVm env false false) ↔ SetPermsRowIntent env :=
  setPermsRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): a wrong field move fails the emitted descriptor. -/

/-- **Anti-ghost (permissions tamper).** A row whose post-`field[0]` is NOT the supplied param fails the
`gPermMove` gate (UNSAT). -/
theorem setPermsVm_rejects_wrong_perm (env : VmRowEnv)
    (hwrong : env.loc (saCol (state.FIELD_BASE + PERMS_FIELD)) ≠ env.loc (prmCol paramSP.PERMS_NEW)) :
    ¬ (VmConstraint.gate gPermMove).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gPermMove, eSA, ePermsNew, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem setPermsVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ SetPermsRowIntent env) :
    ¬ (∀ c ∈ setPermsRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((setPermsVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog).

Decode the row into a concrete `(pre, post)` `CellState` via a field-write `RowEncodes`, mapping `field[0]`
to a designated `CellState` field-component. The descriptor's satisfaction forces the post-state's
`field[0]` = the param, every other column frozen. We record `field[0]` in `CellState.fields 0`. -/

/-- **`PermRowEncodes env pre post permsNew`** — the row decodes to `(pre, post)` cell states with the new
permissions value carried in `param.PERMS_NEW`. The `permissions` scalar lives in `fields 0`. -/
def PermRowEncodes (env : VmRowEnv) (pre post : CellState) (permsNew : ℤ) : Prop :=
  env.loc (sbCol state.BALANCE_LO) = pre.balLo
  ∧ env.loc (sbCol state.BALANCE_HI) = pre.balHi
  ∧ env.loc (sbCol state.NONCE) = pre.nonce
  ∧ (∀ i : Fin 8, env.loc (sbCol (state.FIELD_BASE + i.val)) = pre.fields i)
  ∧ env.loc (sbCol state.CAP_ROOT) = pre.capRoot
  ∧ env.loc (sbCol state.RESERVED) = pre.reserved
  ∧ env.loc (prmCol paramSP.PERMS_NEW) = permsNew
  ∧ env.loc (saCol state.BALANCE_LO) = post.balLo
  ∧ env.loc (saCol state.BALANCE_HI) = post.balHi
  ∧ env.loc (saCol state.NONCE) = post.nonce
  ∧ (∀ i : Fin 8, env.loc (saCol (state.FIELD_BASE + i.val)) = post.fields i)
  ∧ env.loc (saCol state.CAP_ROOT) = post.capRoot
  ∧ env.loc (saCol state.RESERVED) = post.reserved

/-- The per-cell field-write spec: the moved cell's WHOLE post-state is `pre` with `fields 0` set to the
new permissions value, every other field frozen. The per-cell projection of universe-A's
`SetPermissionsSpec` (`permissions`-slot write ⟹ `fields 0` move; 16-field/balance freeze ⟹ frame
freeze). -/
def PermCellSpec (pre post : CellState) (permsNew : ℤ) : Prop :=
  post.fields 0 = permsNew
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, i ≠ 0 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Under `PermRowEncodes`, `SetPermsRowIntent` IS the structured per-cell `PermCellSpec`. -/
theorem intent_to_permCellSpec (env : VmRowEnv) (pre post : CellState) (permsNew : ℤ)
    (henc : PermRowEncodes env pre post permsNew) (hint : SetPermsRowIntent env) :
    PermCellSpec pre post permsNew := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes, hpDig,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hperm, hlo, hhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.fields 0 = permsNew : field[0] after = param
    have h0 : env.loc (saCol (state.FIELD_BASE + (0 : Fin 8).val)) = post.fields 0 := hsaF 0
    rw [← h0, ← hpDig]
    show env.loc (saCol (state.FIELD_BASE + PERMS_FIELD)) = env.loc (prmCol paramSP.PERMS_NEW)
    exact hperm
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i hi
    have hi1 : 1 ≤ i.val := by
      rcases Nat.lt_or_ge 0 i.val with h | h
      · exact h
      · exact absurd (Fin.ext (Nat.le_zero.mp h)) hi
    rw [← hsaF i, ← hsbF i]; exact hfld i.val hi1 i.isLt
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`setPermsDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under
the `PermRowEncodes` decoding forces the structured per-cell `PermCellSpec` (post `field[0]` = the
written permissions value, frame frozen). -/
theorem setPermsDescriptor_full_sound (env : VmRowEnv)
    (pre post : CellState) (permsNew : ℤ)
    (henc : PermRowEncodes env pre post permsNew)
    (hgates : ∀ c ∈ setPermsRowGates, c.holdsVm env false false) :
    PermCellSpec pre post permsNew :=
  intent_to_permCellSpec env pre post permsNew henc ((setPermsVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, field[0] included).

`setPermsHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites` (the moved `field[0]`
is absorbed by site 0). So all the keystone's commitment-binding lemmas apply verbatim: two satisfying
rows with the same published `NEW_COMMIT` have identical absorbed columns — a tampered post-`field[0]`
that claims the published commitment is impossible. -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `setPermsHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem setPermsHashSites_eq : setPermsHashSites = transferHashSites := rfl

/-- **`setPermsDescriptor_commit_binds_state` — the whole-state tooth.** Two `setPermissionsA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the moved
post-`field[0]` (an absorbed column, site 0) included. So a prover CANNOT tamper the post-`field[0]` (or
any absorbed cell) while keeping the published commitment. -/
theorem setPermsDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ setPermsHashSites)
    (hs₂ : siteHoldsAll hash e₂ setPermsHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [setPermsHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `permProj` to universe-A's `SetPermissionsSpec`.

`permProj k c = fieldOf permsField (k.cell c)` reads the SAME `permissions` scalar universe-A's
`setPermsCellMap` writes. The unification: a committed universe-A `SetPermissionsSpec` makes the projected
post-`permissions` of the touched `cell` EXACTLY `p` — the value the descriptor's `param.PERMS_NEW`
carries. So the runnable `field[0]` column transition IS universe-A's `permissions`-write transition. -/

open Dregg2.Circuit.Spec.CellStatePermissions
  (SetPermissionsSpec setPermsCellMap setPermissions_cellWrite_correct execFullA_setPermissions_iff_spec)

/-- **`permProj k c`** — the EffectVM `field[0]` column value for cell `c` of kernel state `k`: the
`permissions` scalar (the SAME `fieldOf permsField` measure universe-A writes). -/
def permProj (k : RecordKernelState) (c : CellId) : ℤ := fieldOf permsField (k.cell c)

/-- **`unify_setPerms` — THE CONNECTOR.** When universe-A's `SetPermissionsSpec` holds, the projected
post-`permissions` of the touched `cell` is EXACTLY the written value `p` — the column move the descriptor
pins (`param.PERMS_NEW = p`). So `PermCellSpec`'s `field[0]` clause IS universe-A's `permissions`-clause,
projected to the field column. -/
theorem unify_setPerms (s : RecChainedState) (actor cell : CellId) (p : Int) (s' : RecChainedState)
    (hspec : SetPermissionsSpec s actor cell p s') :
    permProj s'.kernel cell = p := by
  -- SetPermissionsSpec's cell clause is `s'.kernel.cell = setPermsCellMap s.kernel cell p`.
  obtain ⟨_, hcell, _⟩ := hspec
  show fieldOf permsField (s'.kernel.cell cell) = p
  rw [hcell]
  exact (setPermissions_cellWrite_correct s.kernel cell p).1

/-- **`unify_setPerms_via_exec` — the runnable column move inherits the VALIDATED guarantee.** Chaining
universe-A's `execFullA_setPermissions_iff_spec` (a committed executor write ⟹ `SetPermissionsSpec`) with
`unify_setPerms`: a committed `setPermissionsA` forces the projected post-`permissions` to the written
value `p` — the EXACT column value the runnable descriptor's `param.PERMS_NEW` carries. So the runnable
`field[0]` move is universe-A's validated `permissions` write, not a fourth spec. -/
theorem unify_setPerms_via_exec (s : RecChainedState) (actor cell : CellId) (p : Int)
    (s' : RecChainedState)
    (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    permProj s'.kernel cell = p :=
  unify_setPerms s actor cell p s' ((execFullA_setPermissions_iff_spec s actor cell p s').mp h)

/-! ## §9 — NON-VACUITY: a concrete field-write row that satisfies the intent, and one that does not. -/

/-- A concrete `setPermissionsA` row: `field[0]` moves to the param value `3`, frame frozen at `0`. -/
def permGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selSP.SET_PERMS then 1
    else if v = sbCol (state.FIELD_BASE + PERMS_FIELD) then 1
    else if v = saCol (state.FIELD_BASE + PERMS_FIELD) then 3
    else if v = prmCol paramSP.PERMS_NEW then 3
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `permGoodRow` is a genuine `setPermissionsA` row. -/
theorem permGoodRow_isSetPermsRow : IsSetPermsRow permGoodRow := by
  unfold IsSetPermsRow permGoodRow
  constructor <;> norm_num [selSP.SET_PERMS, sel.NOOP, sbCol, saCol, prmCol, STATE_BEFORE_BASE,
    STATE_AFTER_BASE, PARAM_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, PERMS_FIELD,
    paramSP.PERMS_NEW]

/-- **NON-VACUITY (witness TRUE).** `permGoodRow` REALIZES the metadata intent: post `field[0] = 3` = the
param value, balance/nonce/cap/reserved/field[1..7] frozen at `0`. -/
theorem permGoodRow_realizes_intent : SetPermsRowIntent permGoodRow := by
  unfold SetPermsRowIntent permGoodRow
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, PERMS_FIELD, paramSP.PERMS_NEW]
  all_goals
    simp only [saCol, sbCol, prmCol, selSP.SET_PERMS, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
      NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, PERMS_FIELD, state.BALANCE_LO,
      state.BALANCE_HI, state.NONCE, state.CAP_ROOT, state.RESERVED, paramSP.PERMS_NEW]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · intro i hi1 hi8
    -- field[i] (i ≥ 1) after-column (76+3+i) and before-column (54+3+i) miss every named column.
    have e1 : ¬ (76 + (3 + i) = 3) := by omega
    have e2 : ¬ (76 + (3 + i) = 57) := by omega
    have e3 : ¬ (76 + (3 + i) = 79) := by omega
    have e4 : ¬ (76 + (3 + i) = 69) := by omega
    have f1 : ¬ (54 + (3 + i) = 3) := by omega
    have f2 : ¬ (54 + (3 + i) = 57) := by omega
    have f3 : ¬ (54 + (3 + i) = 79) := by omega
    have f4 : ¬ (54 + (3 + i) = 69) := by omega
    simp only [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg f1, if_neg f2, if_neg f3, if_neg f4]

/-- A forged `setPermissionsA` row: `permGoodRow` with the post-`field[0]` tampered to `999 ≠ 3`. -/
def permBadRow : VmRowEnv where
  loc := fun v => if v = saCol (state.FIELD_BASE + PERMS_FIELD) then 999 else permGoodRow.loc v
  nxt := permGoodRow.nxt
  pub := permGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `permBadRow`'s post-`field[0]` is NOT the param
value, so the `gPermMove` gate REJECTS it — a concrete UNSAT. -/
theorem permBadRow_rejected : ¬ (VmConstraint.gate gPermMove).holdsVm permBadRow false false := by
  apply setPermsVm_rejects_wrong_perm
  show (if saCol (state.FIELD_BASE + PERMS_FIELD) = saCol (state.FIELD_BASE + PERMS_FIELD) then (999:ℤ)
      else permGoodRow.loc _) ≠ permBadRow.loc (prmCol paramSP.PERMS_NEW)
  rw [if_pos rfl]
  show (999:ℤ) ≠ (if prmCol paramSP.PERMS_NEW = saCol (state.FIELD_BASE + PERMS_FIELD) then (999:ℤ)
    else permGoodRow.loc (prmCol paramSP.PERMS_NEW))
  have hne : ¬ (prmCol paramSP.PERMS_NEW = saCol (state.FIELD_BASE + PERMS_FIELD)) := by
    simp only [saCol, prmCol, STATE_AFTER_BASE, PARAM_BASE, STATE_BEFORE_BASE, NUM_EFFECTS,
      STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, PERMS_FIELD, paramSP.PERMS_NEW]
  rw [if_neg hne]
  show (999:ℤ) ≠ permGoodRow.loc (prmCol paramSP.PERMS_NEW)
  show (999:ℤ) ≠ (if prmCol paramSP.PERMS_NEW = selSP.SET_PERMS then (1:ℤ)
    else if prmCol paramSP.PERMS_NEW = sbCol (state.FIELD_BASE + PERMS_FIELD) then 1
    else if prmCol paramSP.PERMS_NEW = saCol (state.FIELD_BASE + PERMS_FIELD) then 3
    else if prmCol paramSP.PERMS_NEW = prmCol paramSP.PERMS_NEW then 3 else 0)
  norm_num [prmCol, saCol, sbCol, selSP.SET_PERMS, STATE_AFTER_BASE, STATE_BEFORE_BASE, PARAM_BASE,
    NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, PERMS_FIELD, paramSP.PERMS_NEW]

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard setPermsVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard setPermsVmDescriptor.hashSites.length == 4
#guard setPermsVmDescriptor.traceWidth == 186

#assert_axioms setPermsRowGates_holds_iff
#assert_axioms setPermsVm_faithful
#assert_axioms setPermsVm_rejects_wrong_perm
#assert_axioms setPermsVm_rejects_wrong_output
#assert_axioms intent_to_permCellSpec
#assert_axioms setPermsDescriptor_full_sound
#assert_axioms setPermsDescriptor_commit_binds_state
#assert_axioms unify_setPerms
#assert_axioms unify_setPerms_via_exec
#assert_axioms permGoodRow_realizes_intent
#assert_axioms permBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitSetPermissions
