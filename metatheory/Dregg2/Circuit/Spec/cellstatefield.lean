/-
# Dregg2.Circuit.Spec.cellstatefield — INDEPENDENT full-state spec + executor⟺spec for `setFieldA`.

The effect family **`cell-state-field`** (sole variant `setFieldA`) is dregg2's developer-facing
`SetField`: the one effect dregg1 routes through the cell's per-slot `RecordProgram::evaluate`
caveats (`apply_set_field` → `cell/src/program.rs:1314`+). Its executor arm
(`TurnExecutorFull.execFullA`, `:3491`) is:

    | .setFieldA actor cell f v => stateStepGuarded s f actor cell v

`stateStepGuarded` (`EffectsState.lean:260`) is the CAVEAT-GATED authority write. It commits iff

    caveatsAdmit s.kernel f actor cell v = true          -- (slot-caveat gate, per written field)
  ∧ stateAuthB s.kernel.caps actor cell = true           -- (authority: actor holds a cap over cell)
  ∧ cell ∈ s.kernel.accounts                             -- (membership: a live account)
  ∧ cellLive s.kernel cell = true                        -- (lifecycle liveness, R6)

and on commit produces EXACTLY `stateStep`'s post-state: it writes field `f` of `cell` to `.int v`
(via `writeField`, which touches ONLY the `cell` map's value at `cell`), prepends a one-row receipt
to the chain `log`, and leaves EVERYTHING ELSE literally unchanged.

`caveatsAdmit` is the conjunction over the caveats bound to slot `f`: each of `Immutable`
(`new = old`), `MonotonicSequence` (`new = old+1`), `Monotonic` (`old ≤ new`), `WriteOnce`
(`old = 0 ∨ new = old`), `SenderAuthorized` (`actor ∈ set`), `BoundedBy` (`lo ≤ new ≤ hi`)
(`SlotCaveat.eval`, against `old = fieldOf f (k.cell cell)`, dregg1's `FIELD_ZERO`).

## This module (mirrors `Dregg2.Circuit.Transfer`'s `TransferSpec` + `recKExec_iff_spec` pattern)

  1. `SetFieldSpec st t st'` : Prop — the INDEPENDENT declarative full-state spec. The admissibility
     guard (`SetFieldGuard`, the 4-conjunct caveat+authority+membership+liveness gate, written
     directly — NO `stateStepGuarded`/`stateStep` term), the EXACT post-state on the two touched
     components (`kernel.cell` pointwise = the field write at `cell`; `log` = receipt :: old log),
     and EVERY OTHER component — all 16 non-`cell` kernel fields — LITERALLY unchanged (THE FRAME).
  2. `execFullA_setFieldA_iff_spec` : `execFullA st (.setFieldA actor cell f v) = some st' ↔
     SetFieldSpec …` — BOTH directions. The `→` validates the executor against the independent spec:
     all 17 kernel fields + log are checked, so a silently-mutated field would make it FAIL.
  3. `writeFieldCellMap_correct` : the declarative validation of the touched-cell post helper (the
     `setFieldA` analog of `recTransfer_correct`): the written slot reads back `v`, OTHER cells whole-
     preserved.
-/
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Tactics

namespace Dregg2.Circuit.Spec.CellStateField

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Exec.EffectsState
  (setField fieldOf writeField stateAuthB caveatsAdmit cellLive
   stateStep stateStepGuarded stateStep_factors stateStepGuarded_eq
   setField_fieldOf)

set_option linter.dupNamespace false

/-! ## §1 — The independent admissibility guard.

The EXACT 4-conjunct gate `stateStepGuarded` checks, written DIRECTLY over the pre-state (no
executor term). The caveat conjunct, the authority conjunct, the membership conjunct, the lifecycle
conjunct — the full domain restriction of the guarded field write. -/

/-- **`SetFieldGuard s actor cell f v`** — the full admissibility predicate of a committed
`setFieldA`, stated declaratively. Every caveat bound to slot `f` of `cell` admits the
`(actor, old, v)` transition (`caveatsAdmit`), the actor holds authority over `cell`
(`stateAuthB`), `cell` is a live account (`∈ accounts`), and `cell`'s lifecycle admits new effects
(`cellLive`, R6). This is the EXACT `if`-conjunction inside `stateStepGuarded`/`stateStep`, peeled
out so the spec⟺executor bridge is a clean re-assembly. -/
def SetFieldGuard (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) : Prop :=
  caveatsAdmit s.kernel f actor cell v = true
  ∧ stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — The touched-cell post map, declaratively, and its validation.

The committed write replaces ONLY the `cell` map: at index `cell` it writes field `f` to `.int v`
(via `setField`), every other index whole-preserved. We state that map POINTWISE — no `writeField`
helper — and validate it with `writeFieldCellMap_correct` (the `recTransfer_correct` analog). -/

/-- The post `cell` map a committed `setFieldA` produces, declaratively (pointwise): index `cell`
gets field `f` written to `.int v`; every other cell's whole record is preserved. Written without the
`writeField` executor helper, so the spec's `cell`-frame clause is independent. -/
def setFieldCellMap (base : CellId → Value) (target : CellId) (f : FieldName) (v : Int) :
    CellId → Value :=
  fun c => if c = target then setField f (base c) (.int v) else base c

/-- **`writeFieldCellMap_correct`** — the touched-cell post map validated DECLARATIVELY (not
trusted), the `setFieldA` analog of `Transfer.recTransfer_correct`: at the target, reading slot `f`
back yields exactly `v` (the write/read law); every OTHER cell's whole record is untouched. So the
spec's `setFieldCellMap` clause encodes write-`f`-to-`v` ∧ cell-frame. -/
theorem writeFieldCellMap_correct (base : CellId → Value) (target : CellId) (f : FieldName)
    (v : Int) :
    fieldOf f (setFieldCellMap base target f v target) = v
    ∧ (∀ c, c ≠ target → setFieldCellMap base target f v c = base c) := by
  refine ⟨?_, ?_⟩
  · simp only [setFieldCellMap, if_pos]; exact setField_fieldOf f (base target) v
  · intro c hc; simp only [setFieldCellMap, if_neg hc]

/-- The declarative post `cell` map coincides with the executor's `writeField` post map (the bridge
that lets the executor↔spec proof discharge the touched-component clause). -/
theorem setFieldCellMap_eq_writeField (k : RecordKernelState) (target : CellId) (f : FieldName)
    (v : Int) :
    setFieldCellMap k.cell target f v = (writeField k f target (.int v)).cell := by
  funext c; simp only [setFieldCellMap, writeField]

/-! ## §3 — THE FULL-STATE DECLARATIVE SPEC (the INDEPENDENT reference). -/

/-- **`SetFieldSpec` — the full-state declarative spec of a committed `setFieldA`.** The guard holds;
the post-state's `cell` map is the declarative field write (`setFieldCellMap` — other cells whole-
preserved, see `writeFieldCellMap_correct`); the receipt chain grows by exactly the one self-targeted
row; and EVERY OTHER state component is LITERALLY unchanged — all 16 non-`cell` kernel fields
(`accounts caps nullifiers revoked commitments bal queues swiss slotCaveats factories
lifecycle deathCert delegate delegations sealedBoxes`). No frame clause mentions the executor. -/
def SetFieldSpec (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (s' : RecChainedState) : Prop :=
  SetFieldGuard s actor cell f v
  -- the two TOUCHED components: the field-write cell map, and the one-row chain extension.
  ∧ s'.kernel.cell = setFieldCellMap s.kernel.cell cell f v
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  -- THE FRAME: all 16 non-`cell` kernel fields, literally unchanged.
  ∧ s'.kernel.accounts = s.kernel.accounts
  ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked
  ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal
  ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories
  ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert
  ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-! ## §4 — executor ⟺ spec (FULL state, both directions). -/

/-- The `setFieldA` arm of `execFullA` is DEFINITIONALLY the caveat-gated guarded write — the seam
the whole bridge sits on. -/
theorem execFullA_setFieldA_eq (s : RecChainedState) (actor cell : CellId) (f : FieldName)
    (v : Int) :
    execFullA s (.setFieldA actor cell f v) = stateStepGuarded s f actor cell v := rfl

/-- `stateStepGuarded` commits IFF its full admissibility guard (`SetFieldGuard`) holds — and then
the post-state is exactly `stateStep`'s field-write + chain extension. The decidable seam both
directions of the bridge reuse. -/
theorem stateStepGuarded_iff_guard_and_post
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState) :
    stateStepGuarded s f actor cell v = some s'
      ↔ (SetFieldGuard s actor cell f v
          ∧ s' = { kernel := writeField s.kernel f cell (.int v),
                   log := { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log }) := by
  unfold stateStepGuarded stateStep SetFieldGuard
  by_cases hcav : caveatsAdmit s.kernel f actor cell v = true
  · rw [if_pos hcav]
    by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
        ∧ cellLive s.kernel cell = true
    · rw [if_pos hg]
      constructor
      · intro h
        simp only [Option.some.injEq] at h
        exact ⟨⟨hcav, hg.1, hg.2.1, hg.2.2⟩, h.symm⟩
      · rintro ⟨_, hs'⟩; rw [hs']
    · rw [if_neg hg]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨⟨_, ha, hm, hl⟩, _⟩; exact absurd ⟨ha, hm, hl⟩ hg
  · rw [if_neg hcav]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hc, _⟩, _⟩; exact absurd hc hcav

/-- **`execFullA_setFieldA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live
executor commits a `setFieldA` into `s'` IFF `s'` is EXACTLY the spec'd full post-state. The `→`
direction VALIDATES `execFullA`'s `setFieldA` arm against the independent spec — all 17 kernel
components + the log are checked, so had the arm silently mutated `bal`/`nullifiers`/`caps`/… any of
the 16 frame fields, the frame clauses would make this proof FAIL; the `←` reconstructs the committed
state from the spec. This is the executor corner of the spec⟺executor⟺circuit triangle for the
`cell-state-field` family. -/
theorem execFullA_setFieldA_iff_spec
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int) (s' : RecChainedState) :
    execFullA s (.setFieldA actor cell f v) = some s' ↔ SetFieldSpec s actor cell f v s' := by
  rw [execFullA_setFieldA_eq, stateStepGuarded_iff_guard_and_post]
  constructor
  · rintro ⟨hg, hs'⟩
    subst hs'
    refine ⟨hg, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (setFieldCellMap_eq_writeField s.kernel cell f v).symm
    all_goals rfl
  · rintro ⟨hg, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    refine ⟨hg, ?_⟩
    -- rebuild s' field-by-field: the touched cell map, the log, and the 16 frame fields, then η.
    obtain ⟨k', lg'⟩ := s'
    obtain ⟨acc, cl, cps, nul, rev, cmt, bl, sc, fac, lc, dc, dg, dgs, dge, dgea⟩ := k'
    simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    subst hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    -- the touched cell map: rewrite the declarative map to the executor's writeField form.
    rw [setFieldCellMap_eq_writeField] at hcell
    subst hcell
    rfl

/-! ## §5 — Spec-side corollaries (the touched components + the FRAME, read off the spec).

These show the spec is the genuine semantics: a committed `setFieldA` writes the slot to `v`, leaves
every other cell whole, and leaves every non-`cell` component untouched — derived from the spec, NOT
the executor. -/

/-- **Touched slot reads back `v`.** Off the spec: a committed `setFieldA` makes slot `f` of `cell`
read exactly `v`. -/
theorem setFieldSpec_writes_slot
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    fieldOf f (s'.kernel.cell cell) = v := by
  rw [h.2.1]; exact (writeFieldCellMap_correct s.kernel.cell cell f v).1

/-- **Cell-frame: other cells whole-preserved.** Off the spec: a committed `setFieldA` leaves every
cell OTHER than `cell` byte-for-byte unchanged. -/
theorem setFieldSpec_cell_frame
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  intro c hc; rw [h.2.1]; exact (writeFieldCellMap_correct s.kernel.cell cell f v).2 c hc

/-- **Authority obligation.** Off the spec: a committed `setFieldA` was authorized over `cell`. -/
theorem setFieldSpec_authorized
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    stateAuthB s.kernel.caps actor cell = true := h.1.2.1

/-- **Caveat obligation.** Off the spec: every caveat on slot `f` of `cell` admitted the write. -/
theorem setFieldSpec_caveats
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    caveatsAdmit s.kernel f actor cell v = true := h.1.1

/-- **The `bal` ledger frame.** Off the spec: a `setFieldA` never touches the per-asset ledger
(the conservation-relevant frame fact). -/
theorem setFieldSpec_bal_frame
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    s'.kernel.bal = s.kernel.bal := h.2.2.2.2.2.2.2.2.1

/-- **The caps frame.** Off the spec: a `setFieldA` never edits the cap table (authority Δ = 0). -/
theorem setFieldSpec_caps_frame
    {s s' : RecChainedState} {actor cell : CellId} {f : FieldName} {v : Int}
    (h : SetFieldSpec s actor cell f v s') :
    s'.kernel.caps = s.kernel.caps := h.2.2.2.2.1

/-! ## §6 — NON-VACUITY: the spec REJECTS bad inputs (fail-closed teeth).

A spec that accepts everything is worthless. We exhibit that a caveat violation, an authority
failure, a non-account target, or a non-live cell each make `SetFieldSpec` UNINHABITED — exactly the
executor's fail-closed behavior, mirrored on the independent spec. -/

/-- **Caveat-violation rejection.** If ANY caveat on slot `f` rejects the write
(`caveatsAdmit = false`), no `s'` satisfies the spec (an `Immutable` slot rejects a rewrite, a
`MonotonicSequence` slot a non-`+1` write, a `WriteOnce` slot a second write, …). -/
theorem setFieldSpec_rejects_caveat_violation
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hbad : caveatsAdmit s.kernel f actor cell v = false) :
    ¬ ∃ s', SetFieldSpec s actor cell f v s' := by
  rintro ⟨s', h⟩; rw [setFieldSpec_caveats h] at hbad; exact absurd hbad (by simp)

/-- **Unauthorized rejection.** If the actor does NOT hold authority over `cell`
(`stateAuthB = false`), no `s'` satisfies the spec. -/
theorem setFieldSpec_rejects_unauthorized
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    ¬ ∃ s', SetFieldSpec s actor cell f v s' := by
  rintro ⟨s', h⟩; rw [setFieldSpec_authorized h] at hbad; exact absurd hbad (by simp)

/-- **Non-live rejection.** If `cell`'s lifecycle does not admit effects (`cellLive = false`,
sealed/destroyed), no `s'` satisfies the spec — the R6 fail-closed gate, on the spec. -/
theorem setFieldSpec_rejects_nonlive
    (s : RecChainedState) (actor cell : CellId) (f : FieldName) (v : Int)
    (hbad : cellLive s.kernel cell = false) :
    ¬ ∃ s', SetFieldSpec s actor cell f v s' := by
  rintro ⟨s', h⟩
  have := h.1.2.2.2; rw [hbad] at this; exact absurd this (by simp)

/-! ## §7 — Concrete #guard witnesses: a GOOD write commits to the spec'd state; BAD ones reject.

Cell 0 is a live self-owned account (actor 0 = cell 0, so `stateAuthB` passes by ownership; empty
slot caveats ⇒ `caveatsAdmit` passes). A write of `"status" := 7` to cell 0 commits. The forged
inputs (unauthorized actor; a caveat-bound `Immutable` slot rewrite) each fail to commit. -/

/-- A concrete pre-state: one live account (cell 0), no caveats, empty caps (authority by ownership),
empty log. -/
def sSF0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun _ => .record [("status", .int 1)]
        caps := fun _ => [] }
    log := [] }

-- the executor COMMITS the good self-authored write (actor 0 owns cell 0, no caveats):
#guard (execFullA sSF0 (.setFieldA 0 0 "status" 7)).isSome  -- true

-- ...and the committed slot reads back exactly 7 (the write/read law on the real post-state):
#guard
  (match execFullA sSF0 (.setFieldA 0 0 "status" 7) with
   | some s' => decide (fieldOf "status" (s'.kernel.cell 0) = 7)
   | none    => false)  -- true

-- an UNAUTHORIZED actor (9 owns nothing, no cap over cell 0) is REJECTED:
#guard (execFullA sSF0 (.setFieldA 9 0 "status" 7)).isNone  -- true

/-- A pre-state whose cell 0 carries an `Immutable "status"` caveat — the slot is registered-forever. -/
def sSFImmut : RecChainedState :=
  { sSF0 with
    kernel := { sSF0.kernel with slotCaveats := fun _ => [.immutable "status"] } }

-- a rewrite of the Immutable slot to a DIFFERENT value (old = 1, new = 7) is REJECTED (fail-closed):
#guard (execFullA sSFImmut (.setFieldA 0 0 "status" 7)).isNone  -- true
-- ...but a no-op write of the SAME value (new = old = 1) still COMMITS (Immutable admits new = old):
#guard (execFullA sSFImmut (.setFieldA 0 0 "status" 1)).isSome  -- true

/-! ## §8 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms writeFieldCellMap_correct
#assert_axioms setFieldCellMap_eq_writeField
#assert_axioms execFullA_setFieldA_eq
#assert_axioms stateStepGuarded_iff_guard_and_post
#assert_axioms execFullA_setFieldA_iff_spec
#assert_axioms setFieldSpec_writes_slot
#assert_axioms setFieldSpec_cell_frame
#assert_axioms setFieldSpec_authorized
#assert_axioms setFieldSpec_caveats
#assert_axioms setFieldSpec_bal_frame
#assert_axioms setFieldSpec_caps_frame
#assert_axioms setFieldSpec_rejects_caveat_violation
#assert_axioms setFieldSpec_rejects_unauthorized
#assert_axioms setFieldSpec_rejects_nonlive

end Dregg2.Circuit.Spec.CellStateField
