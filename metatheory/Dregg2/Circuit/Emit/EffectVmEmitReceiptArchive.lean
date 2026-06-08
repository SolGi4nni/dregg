/-
# Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive — the CELL-STATE-AUDIT effect `receiptArchiveA`,
  EMITTED onto a runnable EffectVM `field` column, with its full-state soundness and the connector to
  the validated universe-A `ReceiptArchiveSpec` / `execFullA_receiptArchiveA_iff_spec`.

## The "ONE circuit" thesis (follows the `attenuateA` / `setPermissionsA` LOCAL TEMPLATE)

`receiptArchiveA` (`Inst/receiptArchiveA.lean`, `Spec/cellstateaudit.lean`) writes ONE cell's
`lifecycle` record-slot to the CONSTANT `1` (`stateStep s lifecycleField actor cell (.int 1)`),
prepends one self-targeted receipt row to the log, and freezes the 16 non-`cell` kernel fields. Its
validation `receiptArchiveA_full_sound ⇒ ReceiptArchiveSpec` is DONE; this module emits the SAME
effect onto the running EffectVM row layout and welds the two.

The audit write is a `field`-COLUMN SET-TO-ONE: the post `lifecycle` column is the constant `1`, every
OTHER state column frozen, and the post-state bound into the published `state_commit` under Poseidon2
CR. We designate `field[1]` (`state.FIELD_BASE + 1`) as the EffectVM column carrying the cell's
`lifecycle` record-slot scalar (`fieldOf lifecycleField`, read as `ℤ` exactly like `balOf`). (DISTINCT
from `field[0]`, which `setPermissionsA` uses for `permissions` — the two record slots map to two
EffectVM field columns.)

`receiptArchiveVmDescriptor` emits exactly that: post `field[1]` pinned to the LITERAL `1` (the gate is
`new_field1 - 1 = 0`, NO param needed — the executor writes the constant), and the frame (balance
limbs / nonce / cap_root / reserved / field[0] / field[2..7]) frozen. We PROVE: satisfying the
descriptor pins the full per-cell post-state (`field[1]` set to `1`, frame frozen) `↔` the row intent
`ArchiveRowIntent`; the GROUP-4 sites bind the WHOLE post-state (the set `field[1]` included) into
`state_commit` — so a tampered post-`field[1]` that still claims `NEW_COMMIT` is UNSAT (the anti-ghost
tooth, REUSED from the transfer keystone since `field[1]` is an absorbed column, site 1).

## The CONNECTOR — `lifeProj` to universe-A's `ReceiptArchiveSpec`

`lifeProj k c = fieldOf lifecycleField (k.cell c)` reads the SAME `lifecycle` record-slot scalar
universe-A's `auditCellMap … lifecycleField` writes. `unify_archive` shows: when `ReceiptArchiveSpec`
holds, the projected post-`lifecycle` of the touched `cell` is EXACTLY `1` — the column value the
descriptor pins. So the runnable `field[1]` column transition IS universe-A's `lifecycle`-write
transition; not a fourth spec.

## HONEST BOUNDARY (precise — do NOT over-read)

  * **IR GAP — the LOG is not an EffectVM column.** `receiptArchiveA` GROWS the receipt log by one row;
    the EffectVM row layout (186 cols) has NO log column / no log-hash site. So the runnable descriptor
    pins the cell's `lifecycle` field-column set + frame freeze + the commitment binding, but it does
    NOT pin the log extension. That receipt-chain growth lives in universe-A's `logHashInjective`
    portal (`receiptArchiveA_full_sound`'s `hLog`), the SAME bar the validated soundness uses. FLAG: a
    future IR extension (a `VmHashSite` over a log column) would internalize it.

  * **`lifecycle` RECORD-SLOT vs `lifecycle` SIDE-TABLE.** Universe-A is careful (`cellstateaudit.lean`
    header): the audit write touches the cell-record `lifecycle` SLOT, a DISTINCT object from the
    kernel `lifecycle` SIDE-TABLE (which `ReceiptArchiveSpec` FREEZES as one of the 16 frame fields).
    We map the RECORD-SLOT to EffectVM `field[1]`. The kernel side-table has no EffectVM column on this
    effect (it is a frozen frame field, reached only by universe-A's full-state spec, not the per-row
    circuit). Reported, not papered.

  * **FIELD-COLUMN designation / GUARD off-row** — same boundary as `setPermissionsA`: `field[1]` is a
    NAMED column choice; the three-leg `auditGuard` is the v1 framework `propBit`, off-row.

  * PER-CELL / PER-ROW. Single-row AIR. Cross-row composition is the turn layer (`TurnEmit`), cited.

  * `state.RESERVED` is NOT absorbed by any hash-site (inherited finding from the transfer keystone).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. Poseidon2 CR enters ONLY as
the NAMED hypothesis `Poseidon2SpongeCR hash`. No `sorry`, no `:= True`, no `native_decide`, no
`rfl`-posing-as-bridge. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitTransferSound
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Circuit.Spec.cellstateaudit

namespace Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer
  (eSB eSA eSub transitionAll boundaryFirstPins transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — Selector + field offset for the audit-write effect row.

`receiptArchiveA` has its own selector index; we name it `selRA.RECEIPT_ARCHIVE`. The written value is
the CONSTANT `1` (no param column). The lifecycle record-slot lives in EffectVM `field[1]`. -/

namespace selRA
/-- The `receiptArchiveA` effect selector column. -/
def RECEIPT_ARCHIVE : Nat := 4
end selRA

/-- The designated EffectVM `field` offset that carries the cell's `lifecycle` record-slot scalar. -/
def LIFE_FIELD : Nat := 1

/-- The `receiptArchiveA` selector as an expression. -/
def eSelRA : EmittedExpr := .var selRA.RECEIPT_ARCHIVE

/-! ## §1 — The audit-write row gates (the running prover's, specialized to the row).

The effect SETS `field[1]` (the lifecycle column) to the constant `1` and FREEZES the rest of the block.
Mirror of the `setPermissionsA` gate set, with the param-move replaced by a constant-set. -/

/-- Field[1] (lifecycle) SET-TO-ONE body: `new_field1 - 1`. -/
def gLifeSet : EmittedExpr := eSub (eSA (state.FIELD_BASE + LIFE_FIELD)) (.const 1)

/-- Balance-lo freeze body. -/
def gBalLoFix : EmittedExpr := eSub (eSA state.BALANCE_LO) (eSB state.BALANCE_LO)
/-- Balance-hi freeze body. -/
def gBalHiFix : EmittedExpr := eSub (eSA state.BALANCE_HI) (eSB state.BALANCE_HI)
/-- Nonce freeze body (an audit write does NOT tick the nonce — matches the executor). -/
def gNonceFix : EmittedExpr := eSub (eSA state.NONCE) (eSB state.NONCE)
/-- Cap-root freeze body. -/
def gCapFix : EmittedExpr := eSub (eSA state.CAP_ROOT) (eSB state.CAP_ROOT)
/-- Reserved freeze body. -/
def gResFix : EmittedExpr := eSub (eSA state.RESERVED) (eSB state.RESERVED)

/-- Field-`i` freeze body (for the 7 NON-lifecycle field columns, `i ≠ 1`). -/
def gFieldFix (i : Nat) : EmittedExpr :=
  eSub (eSA (state.FIELD_BASE + i)) (eSB (state.FIELD_BASE + i))

/-- The seven field-freeze gates (field[0] and field[2..7]; field[1] is SET). The index set is
`{0,2,3,4,5,6,7}`, encoded as `if a = 1 then 0 else a` over `range 8` minus the duplicate — we use the
explicit list to keep the dispatch clean. -/
def gFieldFixRest : List VmConstraint :=
  [0, 2, 3, 4, 5, 6, 7].map (fun i => VmConstraint.gate (gFieldFix i))

/-! ## §2 — The emitted descriptor. -/

/-- The `receiptArchiveA` AIR identity (the fingerprint binding). -/
def receiptArchiveVmAirName : String := "dregg-effectvm-receiptArchiveA-v1"

/-- The per-row gates: field[1] SET-TO-ONE, balance/nonce/cap/reserved freeze, field[0],[2..7] freeze. -/
def archiveRowGates : List VmConstraint :=
  [ .gate gLifeSet, .gate gBalLoFix, .gate gBalHiFix, .gate gNonceFix
  , .gate gCapFix, .gate gResFix ] ++ gFieldFixRest

/-- The ordered GROUP-4 hash sites — DEFINITIONALLY the transfer keystone's (field[1] is absorbed by
site 1, so the set lifecycle column is bound into `state_commit` exactly as transfer binds it). -/
def archiveHashSites : List VmHashSite := transferHashSites

/-- **`receiptArchiveVmDescriptor`** — the `receiptArchiveA` effect's concrete circuit, emitted through
the EffectVM IR: the lifecycle field SET + frame-freeze gates ++ transition continuity ++ the row-0
boundary pins, with the 4 ordered GROUP-4 hash sites. No balance range checks (no balance move). -/
def receiptArchiveVmDescriptor : EffectVmDescriptor :=
  { name := receiptArchiveVmAirName
  , traceWidth := EFFECT_VM_WIDTH
  , piCount := 34
  , constraints := archiveRowGates ++ transitionAll ++ boundaryFirstPins
  , hashSites := archiveHashSites
  , ranges := [] }

/-! ## §3 — The audit-write ROW INTENT (the independent faithfulness target).

`ArchiveRowIntent env` is the field-level audit move: post `field[1]` IS the constant `1`, and the
balance limbs / nonce / cap_root / reserved / field[0] / field[2..7] are FIXED. This is the EffectVM-row
projection of universe-A's `ReceiptArchiveSpec` (`lifecycle`-slot set-to-one ⟹ the lifecycle
field-column set; the 16-field/balance freeze ⟹ the row's frozen columns). -/

/-- **`ArchiveRowIntent env`** — the intended audit move on the row `env.loc`: post `field[1] = 1`,
frame frozen. -/
def ArchiveRowIntent (env : VmRowEnv) : Prop :=
  env.loc (saCol (state.FIELD_BASE + LIFE_FIELD)) = 1
  ∧ env.loc (saCol state.BALANCE_LO) = env.loc (sbCol state.BALANCE_LO)
  ∧ env.loc (saCol state.BALANCE_HI) = env.loc (sbCol state.BALANCE_HI)
  ∧ env.loc (saCol state.NONCE) = env.loc (sbCol state.NONCE)
  ∧ env.loc (saCol state.CAP_ROOT) = env.loc (sbCol state.CAP_ROOT)
  ∧ env.loc (saCol state.RESERVED) = env.loc (sbCol state.RESERVED)
  ∧ (∀ i, i ≠ 1 → i < 8 →
      env.loc (saCol (state.FIELD_BASE + i)) = env.loc (sbCol (state.FIELD_BASE + i)))

/-- The row is a `receiptArchiveA` row: `s_receiptArchive = 1`, `s_noop = 0`. -/
def IsArchiveRow (env : VmRowEnv) : Prop :=
  env.loc selRA.RECEIPT_ARCHIVE = 1 ∧ env.loc sel.NOOP = 0

/-! ## §4 — FAITHFULNESS: the emitted per-row gates ⟺ the intent. -/

/-- **`archiveRowGates_holds_iff`** — on a `receiptArchiveA` row, the emitted per-row gates all hold IFF
`ArchiveRowIntent` holds. The gate bodies are the running prover's polynomials (field set-to-one + frame
freeze); they pin EXACTLY the intent move. -/
theorem archiveRowGates_holds_iff (env : VmRowEnv) :
    (∀ c ∈ archiveRowGates, c.holdsVm env false false) ↔ ArchiveRowIntent env := by
  unfold archiveRowGates gFieldFixRest ArchiveRowIntent
  constructor
  · intro h
    have hLife := h (.gate gLifeSet) (by simp)
    have hLo := h (.gate gBalLoFix) (by simp)
    have hHi := h (.gate gBalHiFix) (by simp)
    have hNon := h (.gate gNonceFix) (by simp)
    have hCap := h (.gate gCapFix) (by simp)
    have hRes := h (.gate gResFix) (by simp)
    have hFld : ∀ i ∈ ([0, 2, 3, 4, 5, 6, 7] : List Nat),
        VmConstraint.holdsVm env false false (.gate (gFieldFix i)) := by
      intro i hi
      apply h
      simp only [List.mem_append, List.mem_map]
      exact Or.inr ⟨i, hi, rfl⟩
    simp only [VmConstraint.holdsVm, gLifeSet, gBalLoFix, gBalHiFix, gNonceFix, gCapFix, gResFix,
      eSA, eSB, eSub, EmittedExpr.eval] at hLife hLo hHi hNon hCap hRes
    refine ⟨by linarith [hLife], by linarith [hLo], by linarith [hHi], by linarith [hNon],
      by linarith [hCap], by linarith [hRes], ?_⟩
    intro i hi1 hi8
    -- i ≠ 1, i < 8 ⟹ i ∈ {0,2,3,4,5,6,7}
    have hmem : i ∈ ([0, 2, 3, 4, 5, 6, 7] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]; omega
    have := hFld i hmem
    simp only [VmConstraint.holdsVm, gFieldFix, eSA, eSB, eSub, EmittedExpr.eval] at this
    linarith
  · rintro ⟨hLife, hLo, hHi, hNon, hCap, hRes, hFld⟩ c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, hi, rfl⟩
    · simp only [VmConstraint.holdsVm, gLifeSet, eSA, eSub, EmittedExpr.eval]
      rw [hLife]; ring
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
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · first
          | (rw [hFld 0 (by decide) (by decide)]; ring)
          | (rw [hFld 2 (by decide) (by decide)]; ring)
          | (rw [hFld 3 (by decide) (by decide)]; ring)
          | (rw [hFld 4 (by decide) (by decide)]; ring)
          | (rw [hFld 5 (by decide) (by decide)]; ring)
          | (rw [hFld 6 (by decide) (by decide)]; ring)
          | (rw [hFld 7 (by decide) (by decide)]; ring)

/-- **`archiveVm_faithful` — THE deliverable.** On a `receiptArchiveA` row, the emitted descriptor's
per-row gates hold IFF the audit move intent holds. -/
theorem archiveVm_faithful (env : VmRowEnv) :
    (∀ c ∈ archiveRowGates, c.holdsVm env false false) ↔ ArchiveRowIntent env :=
  archiveRowGates_holds_iff env

/-! ## §5 — ANTI-GHOST (per-row): a wrong field set fails the emitted descriptor. -/

/-- **Anti-ghost (lifecycle tamper).** A row whose post-`field[1]` is NOT the constant `1` fails the
`gLifeSet` gate (UNSAT). -/
theorem archiveVm_rejects_wrong_life (env : VmRowEnv)
    (hwrong : env.loc (saCol (state.FIELD_BASE + LIFE_FIELD)) ≠ 1) :
    ¬ (VmConstraint.gate gLifeSet).holdsVm env false false := by
  simp only [VmConstraint.holdsVm, gLifeSet, eSA, eSub, EmittedExpr.eval]
  intro h
  apply hwrong
  linarith

/-- **Anti-ghost (general).** A row whose post-state is NOT the intent move does NOT satisfy the per-row
gates. -/
theorem archiveVm_rejects_wrong_output (env : VmRowEnv) (hwrong : ¬ ArchiveRowIntent env) :
    ¬ (∀ c ∈ archiveRowGates, c.holdsVm env false false) :=
  fun h => hwrong ((archiveVm_faithful env).mp h)

/-! ## §6 — The structured per-cell soundness (the keystone analog).

Decode the row into a concrete `(pre, post)` `CellState` via an audit-write `RowEncodes`, mapping
`field[1]` to `CellState.fields 1`. The descriptor's satisfaction forces the post-state's `field[1]` =
`1`, every other column frozen. -/

/-- **`ArchiveRowEncodes env pre post`** — the row decodes to `(pre, post)` cell states. The `lifecycle`
record-slot scalar lives in `fields 1`. -/
def ArchiveRowEncodes (env : VmRowEnv) (pre post : CellState) : Prop :=
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

/-- The per-cell audit-write spec: the moved cell's WHOLE post-state is `pre` with `fields 1` set to
`1`, every other field frozen. The per-cell projection of universe-A's `ReceiptArchiveSpec`. -/
def ArchiveCellSpec (pre post : CellState) : Prop :=
  post.fields 1 = 1
  ∧ post.balLo = pre.balLo
  ∧ post.balHi = pre.balHi
  ∧ post.nonce = pre.nonce
  ∧ (∀ i : Fin 8, i ≠ 1 → post.fields i = pre.fields i)
  ∧ post.capRoot = pre.capRoot
  ∧ post.reserved = pre.reserved

/-- Under `ArchiveRowEncodes`, `ArchiveRowIntent` IS the structured per-cell `ArchiveCellSpec`. -/
theorem intent_to_archiveCellSpec (env : VmRowEnv) (pre post : CellState)
    (henc : ArchiveRowEncodes env pre post) (hint : ArchiveRowIntent env) :
    ArchiveCellSpec pre post := by
  obtain ⟨hsbLo, hsbHi, hsbN, hsbF, hsbCap, hsbRes,
          hsaLo, hsaHi, hsaN, hsaF, hsaCap, hsaRes⟩ := henc
  obtain ⟨hlife, hlo, hhi, hnon, hcap, hres, hfld⟩ := hint
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post.fields 1 = 1 : field[1] after = 1
    have h1 : env.loc (saCol (state.FIELD_BASE + (1 : Fin 8).val)) = post.fields 1 := hsaF 1
    rw [← h1]
    show env.loc (saCol (state.FIELD_BASE + LIFE_FIELD)) = 1
    exact hlife
  · rw [← hsaLo, ← hsbLo]; exact hlo
  · rw [← hsaHi, ← hsbHi]; exact hhi
  · rw [← hsaN, ← hsbN]; exact hnon
  · intro i hi
    have hival : i.val ≠ 1 := fun hc => hi (Fin.ext hc)
    rw [← hsaF i, ← hsbF i]; exact hfld i.val hival i.isLt
  · rw [← hsaCap, ← hsbCap]; exact hcap
  · rw [← hsaRes, ← hsbRes]; exact hres

/-- **`archiveDescriptor_full_sound` — the structured soundness.** Satisfying the per-row gates under
the `ArchiveRowEncodes` decoding forces the structured per-cell `ArchiveCellSpec` (post `field[1]` = `1`,
frame frozen). -/
theorem archiveDescriptor_full_sound (env : VmRowEnv) (pre post : CellState)
    (henc : ArchiveRowEncodes env pre post)
    (hgates : ∀ c ∈ archiveRowGates, c.holdsVm env false false) :
    ArchiveCellSpec pre post :=
  intent_to_archiveCellSpec env pre post henc ((archiveVm_faithful env).mp hgates)

/-! ## §7 — THE ANTI-GHOST COMMITMENT TOOTH (whole-state binding, field[1] included). -/

open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols absorbed_determined_by_commit)

/-- `archiveHashSites` is DEFINITIONALLY the transfer keystone's `transferHashSites`. -/
theorem archiveHashSites_eq : archiveHashSites = transferHashSites := rfl

/-- **`archiveDescriptor_commit_binds_state` — the whole-state tooth.** Two `receiptArchiveA` rows that
satisfy the hash-sites and publish equal `state_commit`s have identical absorbed columns — the set
post-`field[1]` (an absorbed column, site 1) included. So a prover CANNOT tamper the post-`field[1]` (or
any absorbed cell) while keeping the published commitment. -/
theorem archiveDescriptor_commit_binds_state (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (hs₁ : siteHoldsAll hash e₁ archiveHashSites)
    (hs₂ : siteHoldsAll hash e₂ archiveHashSites)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    absorbedCols e₁ = absorbedCols e₂ := by
  rw [archiveHashSites_eq] at hs₁ hs₂
  exact absorbed_determined_by_commit hash hCR e₁ e₂ hs₁ hs₂ hcommit

/-! ## §8 — THE CONNECTOR — `lifeProj` to universe-A's `ReceiptArchiveSpec`.

`lifeProj k c = fieldOf lifecycleField (k.cell c)` reads the SAME `lifecycle` record-slot scalar
universe-A's `auditCellMap … lifecycleField` writes. The unification: a committed `ReceiptArchiveSpec`
makes the projected post-`lifecycle` of the touched `cell` EXACTLY `1` — the column value the descriptor
pins. -/

open Dregg2.Circuit.Spec.CellStateAudit
  (ReceiptArchiveSpec auditCellMap auditCellWrite_correct execFullA_receiptArchiveA_iff_spec)

/-- **`lifeProj k c`** — the EffectVM `field[1]` column value for cell `c` of kernel state `k`: the
`lifecycle` record-slot scalar (`fieldOf lifecycleField`). -/
def lifeProj (k : RecordKernelState) (c : CellId) : ℤ := fieldOf lifecycleField (k.cell c)

/-- `lifecycleField ≠ balanceField` (the distinct-slot fact `auditCellWrite_correct` needs). -/
theorem lifecycle_ne_balance : lifecycleField ≠ balanceField := by decide

/-- **`unify_archive` — THE CONNECTOR.** When universe-A's `ReceiptArchiveSpec` holds, the projected
post-`lifecycle` of the touched `cell` is EXACTLY `1` — the column value the descriptor pins. So
`ArchiveCellSpec`'s `field[1]` clause IS universe-A's `lifecycle`-clause, projected to the field column. -/
theorem unify_archive (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (hspec : ReceiptArchiveSpec s actor cell s') :
    lifeProj s'.kernel cell = 1 := by
  -- ReceiptArchiveSpec's cell clause is `s'.kernel.cell = auditCellMap s.kernel cell lifecycleField`.
  obtain ⟨_, hcell, _⟩ := hspec
  show fieldOf lifecycleField (s'.kernel.cell cell) = 1
  rw [hcell]
  exact (auditCellWrite_correct s.kernel cell lifecycleField lifecycle_ne_balance).1

/-- **`unify_archive_via_exec` — the runnable column move inherits the VALIDATED guarantee.** Chaining
universe-A's `execFullA_receiptArchiveA_iff_spec` (a committed executor write ⟹ `ReceiptArchiveSpec`)
with `unify_archive`: a committed `receiptArchiveA` forces the projected post-`lifecycle` to `1` — the
EXACT column value the runnable descriptor pins. So the runnable `field[1]` set is universe-A's
validated `lifecycle` write, not a fourth spec. -/
theorem unify_archive_via_exec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState)
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    lifeProj s'.kernel cell = 1 :=
  unify_archive s actor cell s' ((execFullA_receiptArchiveA_iff_spec s actor cell s').mp h)

/-! ## §9 — NON-VACUITY: a concrete audit-write row that satisfies the intent, and one that does not. -/

/-- A concrete `receiptArchiveA` row: `field[1]` set to `1`, frame frozen at `0`. -/
def archiveGoodRow : VmRowEnv where
  loc := fun v =>
    if v = selRA.RECEIPT_ARCHIVE then 1
    else if v = saCol (state.FIELD_BASE + LIFE_FIELD) then 1
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- `archiveGoodRow` is a genuine `receiptArchiveA` row. -/
theorem archiveGoodRow_isArchiveRow : IsArchiveRow archiveGoodRow := by
  unfold IsArchiveRow archiveGoodRow
  constructor <;> norm_num [selRA.RECEIPT_ARCHIVE, sel.NOOP, saCol, STATE_AFTER_BASE, PARAM_BASE,
    STATE_BEFORE_BASE, NUM_EFFECTS, STATE_SIZE, NUM_PARAMS, state.FIELD_BASE, LIFE_FIELD]

/-- Evaluate `archiveGoodRow.loc` at a column given as a LITERAL `Nat` not in the named set `{4,80}`
(selector `4`, post-`field[1]` `80`) — returns the `else 0` default. -/
theorem archiveGoodRow_loc_default (n : Nat) (h4 : n ≠ 4) (h80 : n ≠ 80) :
    archiveGoodRow.loc n = 0 := by
  show (if n = selRA.RECEIPT_ARCHIVE then (1:ℤ)
    else if n = saCol (state.FIELD_BASE + LIFE_FIELD) then 1 else 0) = 0
  have c1 : (selRA.RECEIPT_ARCHIVE : Nat) = 4 := rfl
  have c2 : saCol (state.FIELD_BASE + LIFE_FIELD) = 80 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.FIELD_BASE LIFE_FIELD; rfl
  rw [c1, c2, if_neg h4, if_neg h80]

/-- **NON-VACUITY (witness TRUE).** `archiveGoodRow` REALIZES the audit intent: post `field[1] = 1`,
everything else frozen at `0`. -/
theorem archiveGoodRow_realizes_intent : ArchiveRowIntent archiveGoodRow := by
  have hsa1 : saCol (state.FIELD_BASE + LIFE_FIELD) = 80 := by
    unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
      state.FIELD_BASE LIFE_FIELD; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- post field[1] = 1
    show archiveGoodRow.loc (saCol (state.FIELD_BASE + LIFE_FIELD)) = 1
    rw [hsa1]; rfl
  · show archiveGoodRow.loc (saCol state.BALANCE_LO) = archiveGoodRow.loc (sbCol state.BALANCE_LO)
    rw [archiveGoodRow_loc_default (saCol state.BALANCE_LO) (by decide) (by decide),
        archiveGoodRow_loc_default (sbCol state.BALANCE_LO) (by decide) (by decide)]
  · show archiveGoodRow.loc (saCol state.BALANCE_HI) = archiveGoodRow.loc (sbCol state.BALANCE_HI)
    rw [archiveGoodRow_loc_default (saCol state.BALANCE_HI) (by decide) (by decide),
        archiveGoodRow_loc_default (sbCol state.BALANCE_HI) (by decide) (by decide)]
  · show archiveGoodRow.loc (saCol state.NONCE) = archiveGoodRow.loc (sbCol state.NONCE)
    rw [archiveGoodRow_loc_default (saCol state.NONCE) (by decide) (by decide),
        archiveGoodRow_loc_default (sbCol state.NONCE) (by decide) (by decide)]
  · show archiveGoodRow.loc (saCol state.CAP_ROOT) = archiveGoodRow.loc (sbCol state.CAP_ROOT)
    rw [archiveGoodRow_loc_default (saCol state.CAP_ROOT) (by decide) (by decide),
        archiveGoodRow_loc_default (sbCol state.CAP_ROOT) (by decide) (by decide)]
  · show archiveGoodRow.loc (saCol state.RESERVED) = archiveGoodRow.loc (sbCol state.RESERVED)
    rw [archiveGoodRow_loc_default (saCol state.RESERVED) (by decide) (by decide),
        archiveGoodRow_loc_default (sbCol state.RESERVED) (by decide) (by decide)]
  · intro i hi1 hi8
    show archiveGoodRow.loc (saCol (state.FIELD_BASE + i)) = archiveGoodRow.loc (sbCol (state.FIELD_BASE + i))
    have hsaI : saCol (state.FIELD_BASE + i) = 79 + i := by
      unfold saCol STATE_AFTER_BASE PARAM_BASE STATE_BEFORE_BASE NUM_EFFECTS STATE_SIZE NUM_PARAMS
        state.FIELD_BASE; omega
    have hsbI : sbCol (state.FIELD_BASE + i) = 57 + i := by
      unfold sbCol STATE_BEFORE_BASE NUM_EFFECTS state.FIELD_BASE; omega
    rw [hsaI, hsbI,
        archiveGoodRow_loc_default (79 + i) (by omega) (by omega),
        archiveGoodRow_loc_default (57 + i) (by omega) (by omega)]

/-- A forged `receiptArchiveA` row: `archiveGoodRow` with the post-`field[1]` tampered to `999 ≠ 1`. -/
def archiveBadRow : VmRowEnv where
  loc := fun v => if v = saCol (state.FIELD_BASE + LIFE_FIELD) then 999 else archiveGoodRow.loc v
  nxt := archiveGoodRow.nxt
  pub := archiveGoodRow.pub

/-- **NON-VACUITY (witness FALSE / concrete anti-ghost).** `archiveBadRow`'s post-`field[1]` is NOT the
constant `1`, so the `gLifeSet` gate REJECTS it — a concrete UNSAT. -/
theorem archiveBadRow_rejected : ¬ (VmConstraint.gate gLifeSet).holdsVm archiveBadRow false false := by
  apply archiveVm_rejects_wrong_life
  have hbad : archiveBadRow.loc (saCol (state.FIELD_BASE + LIFE_FIELD)) = 999 := by
    show (if saCol (state.FIELD_BASE + LIFE_FIELD) = saCol (state.FIELD_BASE + LIFE_FIELD)
      then (999:ℤ) else archiveGoodRow.loc (saCol (state.FIELD_BASE + LIFE_FIELD))) = 999
    rw [if_pos rfl]
  rw [hbad]; decide

/-! ## §10 — Axiom-hygiene tripwires (the honesty tripwire). -/

#guard receiptArchiveVmDescriptor.constraints.length == 13 + 14 + 4  -- 13 gates + 14 transitions + 4 first
#guard receiptArchiveVmDescriptor.hashSites.length == 4
#guard receiptArchiveVmDescriptor.traceWidth == 186

#assert_axioms archiveRowGates_holds_iff
#assert_axioms archiveVm_faithful
#assert_axioms archiveVm_rejects_wrong_life
#assert_axioms archiveVm_rejects_wrong_output
#assert_axioms intent_to_archiveCellSpec
#assert_axioms archiveDescriptor_full_sound
#assert_axioms archiveDescriptor_commit_binds_state
#assert_axioms unify_archive
#assert_axioms unify_archive_via_exec
#assert_axioms archiveGoodRow_realizes_intent
#assert_axioms archiveBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitReceiptArchive
