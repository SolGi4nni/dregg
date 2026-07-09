/-
# Dregg2.Circuit.Spec.cellstateprogram — INDEPENDENT full-state spec for the SetProgram effect
  (the ordered mid-session program-install effect, the genesis-reframe escape hatch).

This is a LEAF spec module in the shape of `Dregg2.Circuit.Spec.CellStateVK` (`SetVKSpec` +
`vkStateStep_iff_spec` + `setVK_cellWrite_correct`), but for the cell `program` slot the live executor
writes in its SetProgram arm (`turn/src/executor/apply.rs apply_set_program`):

    apply_set_program:  c.program = program.clone()

This is dregg1's `SetProgram { cell, program }`: the mid-session program/caveat-table install. A program
install is a DISTINCT authority surface from a VK change (the caveat table, not the upgrade key), but it
has the SAME kernel SHAPE: a single PROTOCOL-managed record-slot write through the bare authority-gated
`stateStep` (NOT the per-slot caveat gate `stateStepGuarded`). So this leaf mirrors `cellstatevk`
exactly, specialized to the `program` slot (`programField`).

`stateStep` (EffectsState.lean:205) commits iff its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: the actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the `program` field of `cell` to `prog` (`writeField`, touching ONLY that cell's
`program` slot) and extends the receipt chain by one self-targeted row. NO balance move, NO cap edit:
the whole regime invariant. THIS module proves an INDEPENDENT declarative full-state spec characterizes
the `stateStep` program write EXACTLY (both directions), enumerating ALL 17 kernel fields + the `log`
so no ghost field can be silently mutated.

The program slot is folded into the deployed `compute_authority_digest_felt` (`cell/src/commitment.rs`,
the `--- Program ---` arm) and committed into the opaque authority residue register r23
(`B_RECORD_DIGEST = 24`). So a genuine program install MOVES the AFTER `record_digest` limb — the
record-pin family. The CIRCUIT side of this spec⟺circuit triangle is `setProgramV3` (the record-pin
descriptor) + `RotatedKernelRefinementProgram.setProgram_descriptorRefines_sat`.

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStateProgram

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull

set_option linter.unusedVariables false
set_option autoImplicit false

/-- The protocol-managed `program` field name (the cell's `CellProgram` / caveat-table slot). DISTINCT
from `permsField`/`vkField`/`nonceField` — a SetProgram write touches its OWN slot. This is the SAME
`TurnExecutorFull.programField` the executor's `.setProgramA` arm writes (`= "program"`), re-exported
here so the spec module's clauses and the executor's arm name the identical slot. -/
abbrev programField : FieldName := Dregg2.Exec.TurnExecutorFull.programField

/-! ## §1 — the admissibility guard, as a `Prop`. -/

/-- **`setProgramGuard` — the three-leg admissibility gate** the executor checks before it commits a
program install: AUTHORITY over `cell`, `cell` is a live account (MEMBERSHIP), and `cell`'s lifecycle
admits effects (LIVENESS — the R6 gate). Stated independently of the executor term, mirroring
`setVKGuard`. -/
def setProgramGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — the post-state cell-map helper, validated DECLARATIVELY (not trusted). -/

/-- The declarative post-cell-map of a program write: only `cell`'s `program` field moves. -/
def setProgramCellMap (k : RecordKernelState) (cell : CellId) (prog : Int) : CellId → Value :=
  fun c => if c = cell then setField programField (k.cell c) (.int prog) else k.cell c

/-- **`setProgramCellMap_eq_writeField` — the helper matches the executor's `writeField`** (so the
declarative cell-clause and the executor's actual post-cell-map are the SAME function). -/
theorem setProgramCellMap_eq_writeField (k : RecordKernelState) (cell : CellId) (prog : Int) :
    setProgramCellMap k cell prog = (writeField k programField cell (.int prog)).cell := by
  rfl

/-- **`setProgram_cellWrite_correct` — the cell-update helper validated DECLARATIVELY** (the
`setVK_cellWrite_correct` analog). A program write (a) sets `cell`'s `program` slot to exactly `prog`,
(b) leaves `cell`'s conserved `balance` field untouched (the regime's balance-Δ=0 obligation, via the
non-interference of a DISTINCT slot — `program ≠ balance`), and (c) leaves every OTHER cell's whole
record untouched. -/
theorem setProgram_cellWrite_correct (k : RecordKernelState) (cell : CellId) (prog : Int) :
    fieldOf programField (setProgramCellMap k cell prog cell) = prog
    ∧ balOf (setProgramCellMap k cell prog cell) = balOf (k.cell cell)
    ∧ (∀ c, c ≠ cell → setProgramCellMap k cell prog c = k.cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [setProgramCellMap, if_pos]; exact setField_fieldOf programField (k.cell cell) prog
  · simp only [setProgramCellMap, if_pos]
    exact setField_balOf programField (k.cell cell) (.int prog) (by decide)
  · intro c hc; simp only [setProgramCellMap, if_neg hc]

/-! ## §3 — the FULL-STATE declarative spec (the INDEPENDENT reference) + the stateStep⟺spec engine. -/

/-- **The full-state declarative spec of a committed program install** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `cell` map is the program write (`setProgramCellMap`,
validated above); the `log` is the one-row self-targeted extension; and ALL 16 non-`cell` kernel
components are LITERALLY unchanged. Missing ANY of these reintroduces a ghost, so all 17 kernel fields +
the `log` are enumerated. This is the apex reference truth the circuit `setProgram_descriptorRefines_sat`
forces. -/
def SetProgramSpec (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (s' : RecChainedState) : Prop :=
  setProgramGuard s actor cell
  ∧ s'.kernel.cell = setProgramCellMap s.kernel cell prog
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
  ∧ s'.kernel.heaps = s.kernel.heaps
  ∧ s'.kernel.nullifierRoot = s.kernel.nullifierRoot
  ∧ s'.kernel.revokedRoot = s.kernel.revokedRoot

/-- **`programStateStep_iff_spec` — the GENERIC `stateStep` characterization (executor⟺spec, full
state), re-derived LOCALLY.** The bare `stateStep` (the engine a protocol-managed slot write runs)
commits a write of field `f`:=`v` into `s'` IFF `s'` is EXACTLY the three-leg-gated full post-state: the
`cell` map is the single-field write, the `log` is the one-row self-targeted extension, and ALL 16 other
kernel components are literally unchanged. -/
theorem programStateStep_iff_spec (s : RecChainedState) (f : FieldName) (actor cell : CellId) (v : Value)
    (s' : RecChainedState) :
    stateStep s f actor cell v = some s' ↔
      ( (stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
            ∧ cellLive s.kernel cell = true)
        ∧ s'.kernel.cell = (fun c => if c = cell then setField f (s.kernel.cell c) v
                                     else s.kernel.cell c)
        ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
        ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.caps = s.kernel.caps
        ∧ s'.kernel.nullifiers = s.kernel.nullifiers
        ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
        ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
        ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
        ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
        ∧ s'.kernel.delegations = s.kernel.delegations
        ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
        ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt
        ∧ s'.kernel.heaps = s.kernel.heaps
        ∧ s'.kernel.nullifierRoot = s.kernel.nullifierRoot
        ∧ s'.kernel.revokedRoot = s.kernel.revokedRoot ) := by
  unfold stateStep
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ cellLive s.kernel cell = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl⟩
    · rintro ⟨_, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩
      obtain ⟨k', l'⟩ := s'
      obtain ⟨a, ce, ca, nu, re, co, ba, sl, fa, li, dc, de, dg, dge, dgea, hp, nr, rr⟩ := k'
      simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`stateStep_program_iff_spec` — STATESTEP ⟺ SPEC (FULL state, both directions).** A committed
authority-gated `program` write into `s'` holds IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES the write against the independent spec — all 17 kernel components + the `log` are
checked, so a silently-mutated `bal`/`nullifiers`/`caps`/… would make the frame clauses FAIL; the `←`
reconstructs the committed state from the spec. -/
theorem stateStep_program_iff_spec (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (s' : RecChainedState) :
    stateStep s programField actor cell (.int prog) = some s' ↔ SetProgramSpec s actor cell prog s' := by
  rw [programStateStep_iff_spec]
  unfold SetProgramSpec setProgramGuard setProgramCellMap
  rfl

/-! ## §4 — corollaries: the projections onto the touched component + the balance/cap frame. -/

/-- **`stateStep_program_programWritten` — the `program` slot is set to exactly `prog`.** -/
theorem stateStep_program_programWritten {s s' : RecChainedState} {actor cell : CellId}
    {prog : Int} (h : stateStep s programField actor cell (.int prog) = some s') :
    fieldOf programField (s'.kernel.cell cell) = prog := by
  have hspec := (stateStep_program_iff_spec s actor cell prog s').mp h
  rw [hspec.2.1]
  exact (setProgram_cellWrite_correct s.kernel cell prog).1

/-- **`stateStep_program_balFrame` — BALANCE LEDGER untouched (the regime balance-Δ=0).** -/
theorem stateStep_program_balFrame {s s' : RecChainedState} {actor cell : CellId}
    {prog : Int} (h : stateStep s programField actor cell (.int prog) = some s') :
    s'.kernel.bal = s.kernel.bal :=
  ((stateStep_program_iff_spec s actor cell prog s').mp h).2.2.2.2.2.2.2.2.1

/-- **`stateStep_program_capFrame` — CAP-GRAPH untouched (no authority amplification).** A program
install edits NO capability — DISTINCT from the cap-graph it gates over. -/
theorem stateStep_program_capFrame {s s' : RecChainedState} {actor cell : CellId}
    {prog : Int} (h : stateStep s programField actor cell (.int prog) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  ((stateStep_program_iff_spec s actor cell prog s').mp h).2.2.2.2.1

/-- **`stateStep_program_otherCellsFrame` — every OTHER cell's whole record untouched.** -/
theorem stateStep_program_otherCellsFrame {s s' : RecChainedState} {actor cell : CellId}
    {prog : Int} (h : stateStep s programField actor cell (.int prog) = some s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  have hspec := (stateStep_program_iff_spec s actor cell prog s').mp h
  intro c hc
  rw [hspec.2.1]
  exact (setProgram_cellWrite_correct s.kernel cell prog).2.2 c hc

/-- **`stateStep_program_admits_guard` — a committed program write means the guard held.** -/
theorem stateStep_program_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    {prog : Int} (h : stateStep s programField actor cell (.int prog) = some s') :
    setProgramGuard s actor cell :=
  ((stateStep_program_iff_spec s actor cell prog s').mp h).1

/-! ## §4.5 — the executor⟺spec corner: lift `stateStep` onto `execFullA`'s `.setProgramA` arm. -/

/-- The `.setProgramA` arm of `execFullA` is DEFINITIONALLY the bare authority-gated `program`-field
write (`TurnExecutorFull.programField = "program" = programField` here). -/
theorem execFullA_setProgram_eq (s : RecChainedState) (actor cell : CellId) (prog : Int) :
    execFullA s (.setProgramA actor cell prog) = stateStep s programField actor cell (.int prog) := rfl

/-- **`execFullA_setProgram_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live
executor's `.setProgramA` arm commits a `program` write into `s'` IFF `s'` is EXACTLY the spec'd full
post-state. The `→` VALIDATES the executor against the independent `SetProgramSpec` — all 17 kernel
components + the `log` are checked; the `←` reconstructs the committed state. This is the executor
corner of the spec⟺executor⟺circuit triangle for the SetProgram (cell-state-program) family. -/
theorem execFullA_setProgram_iff_spec (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (s' : RecChainedState) :
    execFullA s (.setProgramA actor cell prog) = some s' ↔ SetProgramSpec s actor cell prog s' := by
  rw [execFullA_setProgram_eq, stateStep_program_iff_spec]

/-! ## §5 — NON-VACUITY: the guard REJECTS bad inputs. -/

/-- **`setProgram_rejects_unauthorized`.** Unauthorized actor ⟹ fail closed. -/
theorem setProgram_rejects_unauthorized (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    stateStep s programField actor cell (.int prog) = none := by
  unfold stateStep
  rw [if_neg]
  rintro ⟨hauth, _, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`setProgram_rejects_nonaccount`.** Non-account `cell` ⟹ fail closed. -/
theorem setProgram_rejects_nonaccount (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (hbad : cell ∉ s.kernel.accounts) :
    stateStep s programField actor cell (.int prog) = none := by
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, hmem, _⟩; exact hbad hmem

/-- **`setProgram_rejects_nonlive`.** A non-Live (sealed/destroyed) `cell` ⟹ fail closed. A program
install into a sealed cell is REJECTED — the lifecycle-safety the genesis-reframe escape hatch needs
(a destroyed cell cannot have its caveat table re-installed out from under its proofs). -/
theorem setProgram_rejects_nonlive (s : RecChainedState) (actor cell : CellId) (prog : Int)
    (hbad : cellLive s.kernel cell = false) :
    stateStep s programField actor cell (.int prog) = none := by
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, _, hlive⟩
  rw [hbad] at hlive; exact absurd hlive (by simp)

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms setProgramCellMap_eq_writeField
#assert_axioms setProgram_cellWrite_correct
#assert_axioms programStateStep_iff_spec
#assert_axioms stateStep_program_iff_spec
#assert_axioms stateStep_program_programWritten
#assert_axioms stateStep_program_balFrame
#assert_axioms stateStep_program_capFrame
#assert_axioms stateStep_program_otherCellsFrame
#assert_axioms stateStep_program_admits_guard
#assert_axioms execFullA_setProgram_eq
#assert_axioms execFullA_setProgram_iff_spec
#assert_axioms setProgram_rejects_unauthorized
#assert_axioms setProgram_rejects_nonaccount
#assert_axioms setProgram_rejects_nonlive

end Dregg2.Circuit.Spec.CellStateProgram
