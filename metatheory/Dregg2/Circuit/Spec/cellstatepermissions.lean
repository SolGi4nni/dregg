/-
# Dregg2.Circuit.Spec.cellstatepermissions — INDEPENDENT full-state spec + executor⟺spec for the
  "cell-state-permissions" effect family (variant: `setPermissionsA`).

This is a LEAF spec module in the shape of `Dregg2.Circuit.Transfer` (`TransferSpec` +
`recKExec_iff_spec` + `recTransfer_correct`), but for the protocol-managed `permissions` field-write
the live executor runs in its `.setPermissionsA` arm (`TurnExecutorFull.execFullA`, `:3495`):

    execFullA s (.setPermissionsA actor cell p)  =  stateStep s permsField actor cell (.int p)

`stateStep` (EffectsState.lean:207) commits iff its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: the actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the `permissions` field of `cell` to `p` (`writeField`, touching ONLY that
cell's `permissions` slot) and extends the receipt chain by one self-targeted row. NO balance move,
NO cap edit — the protocol-managed-metadata regime invariant. THIS module proves the executor meets
an INDEPENDENT declarative full-state spec EXACTLY (both directions), enumerating ALL 17 kernel fields
+ the `log` so no ghost field can be silently mutated.

The task statement names only the `stateAuthB` leg of the guard, but the LIVE executor's `stateStep`
gate is the FULL three-leg conjunction (authority ∧ membership ∧ liveness — R6). Writing the spec
guard as the FULL conjunction is the faithful (tighter, more honest) choice: omitting the membership /
liveness legs would make the spec ACCEPT a write into a sealed or non-account cell that the executor
actually REJECTS, breaking the `←` direction. So `SetPermissionsGuard` carries all three.

## What is proved (the §6b corner of the spec⟺executor triangle, copied from `Transfer.lean`)

  1. `SetPermissionsSpec s actor cell p s'` : Prop — the INDEPENDENT declarative post-state: the
     three-leg guard ∧ the EXACT `cell`-map post-image (the `permissions` of `cell` set to `p`, every
     other cell's whole record untouched) ∧ EVERY OTHER kernel field (16 of them) LITERALLY unchanged
     ∧ the `log` extended by exactly the one self-targeted receipt row. No frame clause mentions
     `execFullA` / `stateStep` / `writeField`.

  2. `execFullA_setPermissions_iff_spec` : `execFullA s (.setPermissionsA actor cell p) = some s' ↔
     SetPermissionsSpec s actor cell p s'` — BOTH directions. The `→` half VALIDATES the executor: all
     17 kernel components + the `log` are checked, so a silently-mutated field would make it FAIL.

  3. `setPermissions_cellWrite_correct` — the post-state-helper validation lemma (mirrors
     `recTransfer_correct`): the `permissions`-write helper sets `cell`'s `permissions` to exactly `p`,
     leaves `cell`'s `balance` (and every other field — via the non-interference of the DISTINCT slot
     `permissions ≠ balance`) intact, and leaves every OTHER cell's whole record untouched.

  4. `#assert_axioms` on every theorem — whitelist `{propext, Classical.choice, Quot.sound}` only.

The family has the single executable variant `setPermissionsA`; it shares the EXACT `stateStep` shape
with `incrementNonceA`/`setVKA` (different `FieldName`), so the generic `stateStep_iff_spec` proved
here (independently) instantiates to all three.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStatePermissions

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps)

/-! ## §1 — the admissibility guard `stateStep`/`setPermissionsA` checks, as a `Prop`.

The exact conjunction in `stateStep`'s `if` (EffectsState.lean:209) — extracting it makes the
spec⟺executor proof a clean re-assembly, mirroring `Transfer.admitGuard`. -/

/-- **`setPermsGuard` — the three-leg admissibility gate** the executor checks before it commits a
`setPermissionsA`: AUTHORITY over `cell`, `cell` is a live account (MEMBERSHIP), and `cell`'s
lifecycle admits effects (LIVENESS — the R6 gate). Stated independently of the executor term. The
task names the `stateAuthB` leg; the live `stateStep` gate is this FULL conjunction. -/
def setPermsGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — the post-state cell-map helper, validated DECLARATIVELY (not trusted).

`setPermsCellMap k cell p` is the `cell`-indexed record map a committed permissions write produces:
cell `cell`'s `permissions` slot set to `p` (its other fields kept), every other cell whole-preserved.
Written WITHOUT the executor's `writeField` so the spec's `cell`-clause is the genuine semantics, and
proved equal to `writeField … permsField …` so the executor's actual post-cell-map meets it. -/

/-- The declarative post-cell-map of a permissions write: only `cell`'s `permissions` field moves. -/
def setPermsCellMap (k : RecordKernelState) (cell : CellId) (p : Int) : CellId → Value :=
  fun c => if c = cell then setField permsField (k.cell c) (.int p) else k.cell c

/-- **`setPermsCellMap_eq_writeField` — the helper matches the executor's `writeField`** (so the
declarative cell-clause and the executor's actual post-cell-map are the SAME function). -/
theorem setPermsCellMap_eq_writeField (k : RecordKernelState) (cell : CellId) (p : Int) :
    setPermsCellMap k cell p = (writeField k permsField cell (.int p)).cell := by
  rfl

/-- **`setPermissions_cellWrite_correct` — the cell-update helper validated DECLARATIVELY** (the
`recTransfer_correct` analog). A permissions write (a) sets `cell`'s `permissions` slot to exactly
`p`, (b) leaves `cell`'s conserved `balance` field untouched (the regime's balance-Δ=0 obligation, via
the non-interference of a DISTINCT slot — `permissions ≠ balance`), and (c) leaves every OTHER cell's
whole record untouched. So the spec's `cell`-clause genuinely encodes write ∧ balance-frame ∧
cell-frame, rather than blindly trusting the helper. -/
theorem setPermissions_cellWrite_correct (k : RecordKernelState) (cell : CellId) (p : Int) :
    fieldOf permsField (setPermsCellMap k cell p cell) = p
    ∧ balOf (setPermsCellMap k cell p cell) = balOf (k.cell cell)
    ∧ (∀ c, c ≠ cell → setPermsCellMap k cell p c = k.cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [setPermsCellMap, if_pos]; exact setField_fieldOf permsField (k.cell cell) p
  · simp only [setPermsCellMap, if_pos]
    exact setField_balOf permsField (k.cell cell) (.int p) (by decide)
  · intro c hc; simp only [setPermsCellMap, if_neg hc]

/-! ## §3 — the FULL-STATE declarative spec (the INDEPENDENT reference) + executor⟺spec.

`SetPermissionsSpec` is the COMPLETE state transition of a committed permissions write, written
INDEPENDENTLY of the executor (no `execFullA`/`stateStep`/`writeField` term in any frame clause): the
three-leg guard holds; the post-state's `cell` map is the permissions write (`setPermsCellMap`,
validated above); the `log` is extended by exactly the one self-targeted receipt row; and ALL 16
non-`cell` kernel components — `accounts` `caps` `escrows` `nullifiers` `revoked` `commitments` `bal`
`queues` `swiss` `slotCaveats` `factories` `lifecycle` `deathCert` `delegate` `delegations`
`sealedBoxes` — are LITERALLY unchanged. Missing ANY of these reintroduces a ghost, so all 17 kernel
fields + the `log` are enumerated. This is the apex reference truth the executor is proved equal to. -/

/-- **The full-state declarative spec of a committed `setPermissionsA`** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `cell` map is the permissions write (every other cell
whole, `cell`'s other fields kept — see `setPermissions_cellWrite_correct`); the `log` is the one-row
self-targeted extension; and every one of the 16 non-`cell` kernel components is unchanged. No frame
clause mentions the executor. -/
def SetPermissionsSpec (s : RecChainedState) (actor cell : CellId) (p : Int)
    (s' : RecChainedState) : Prop :=
  setPermsGuard s actor cell
  -- the ONE touched component: cell `cell`'s `permissions` slot set, every other cell whole
  ∧ s'.kernel.cell = setPermsCellMap s.kernel cell p
  -- the log: extended by EXACTLY one self-targeted receipt row (the metadata advance)
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  -- THE FRAME: every one of the 16 OTHER kernel components literally unchanged
  ∧ s'.kernel.accounts = s.kernel.accounts ∧ s'.kernel.caps = s.kernel.caps
  ∧ s'.kernel.nullifiers = s.kernel.nullifiers
  ∧ s'.kernel.revoked = s.kernel.revoked ∧ s'.kernel.commitments = s.kernel.commitments
  ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
  ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
  ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
  ∧ s'.kernel.delegations = s.kernel.delegations ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
  ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
  ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt

/-- **`stateStep_iff_spec` — the GENERIC `stateStep` characterization (executor⟺spec, full state).**
The bare `stateStep` (the shared engine of the cell-state-permissions/monotone families) commits a
write of field `f`:=`v` into `s'` IFF `s'` is EXACTLY the three-leg-gated full post-state: the `cell`
map is the single-field write, the `log` is the one-row self-targeted extension, and ALL 16 other
kernel components are literally unchanged. The `→` direction VALIDATES `stateStep` — all 17 kernel
components + the `log` are checked, so a silently mutated `bal`/`nullifiers`/`caps`/… would make the
frame clauses FAIL; the `←` reconstructs the committed state from the spec. The variant theorem below
is a clean instance of this. Proved here INDEPENDENTLY (no dependence on a sibling Spec module). -/
theorem stateStep_iff_spec (s : RecChainedState) (f : FieldName) (actor cell : CellId) (v : Value)
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
        ∧ s'.kernel.bal = s.kernel.bal ∧ s'.kernel.swiss = s.kernel.swiss ∧ s'.kernel.slotCaveats = s.kernel.slotCaveats
        ∧ s'.kernel.factories = s.kernel.factories ∧ s'.kernel.lifecycle = s.kernel.lifecycle
        ∧ s'.kernel.deathCert = s.kernel.deathCert ∧ s'.kernel.delegate = s.kernel.delegate
        ∧ s'.kernel.delegations = s.kernel.delegations
        ∧ s'.kernel.sealedBoxes = s.kernel.sealedBoxes
        ∧ s'.kernel.delegationEpoch = s.kernel.delegationEpoch
        ∧ s'.kernel.delegationEpochAt = s.kernel.delegationEpochAt ) := by
  unfold stateStep
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ cellLive s.kernel cell = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
      obtain ⟨k', l'⟩ := s'
      obtain ⟨a, ce, ca, nu, re, co, ba, sw, sl, fa, li, dc, de, dg, sb, dge, dgea⟩ := k'
      simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      subst hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execFullA_setPermissions_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The
live per-asset executor's `.setPermissionsA` arm commits a permissions write into `s'` IFF `s'` is
EXACTLY the spec'd full post-state. The `→` direction VALIDATES the executor against the independent
spec — all 17 kernel components + the `log` are checked, so had the arm silently mutated
`bal`/`nullifiers`/`caps`/… the frame clauses would make this proof FAIL; the `←` reconstructs the
committed state from the spec. This is the executor corner of the spec⟺executor⟺circuit triangle for
the cell-state-permissions family. -/
theorem execFullA_setPermissions_iff_spec (s : RecChainedState) (actor cell : CellId) (p : Int)
    (s' : RecChainedState) :
    execFullA s (.setPermissionsA actor cell p) = some s' ↔ SetPermissionsSpec s actor cell p s' := by
  -- the arm IS `stateStep s permsField actor cell (.int p)` definitionally
  show stateStep s permsField actor cell (.int p) = some s' ↔ SetPermissionsSpec s actor cell p s'
  rw [stateStep_iff_spec]
  unfold SetPermissionsSpec setPermsGuard setPermsCellMap
  -- the two statements are the SAME conjunction modulo `permsField`/`(.int p)` substitution
  rfl

/-! ## §4 — corollaries: the projections onto the touched component + the balance/cap frame.

These are the cell-state-permissions analogs of `Transfer`'s debit/credit/conservation facts: a
committed permissions write leaves the conserved balance untouched (regime balance-Δ=0) and the
cap-graph untouched (no authority amplification), with the `permissions` slot set to exactly `p`. Each
is a clean read off `execFullA_setPermissions_iff_spec`. -/

/-- **`execFullA_setPermissions_permsSet` — the `permissions` slot is set to exactly `p`.** -/
theorem execFullA_setPermissions_permsSet {s s' : RecChainedState} {actor cell : CellId}
    {p : Int} (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    fieldOf permsField (s'.kernel.cell cell) = p := by
  have hspec := (execFullA_setPermissions_iff_spec s actor cell p s').mp h
  rw [hspec.2.1]
  exact (setPermissions_cellWrite_correct s.kernel cell p).1

/-- **`execFullA_setPermissions_balFrame` — BALANCE LEDGER untouched (the regime balance-Δ=0).** The
per-asset `bal` ledger is literally unchanged: a permissions write moves NO value. -/
theorem execFullA_setPermissions_balFrame {s s' : RecChainedState} {actor cell : CellId}
    {p : Int} (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    s'.kernel.bal = s.kernel.bal :=
  ((execFullA_setPermissions_iff_spec s actor cell p s').mp h).2.2.2.2.2.2.2.2.1

/-- **`execFullA_setPermissions_capFrame` — CAP-GRAPH untouched (no authority amplification).** The
`caps` table is literally unchanged: a permissions write edits NO capability. (Note: this is a
PERMISSIONS slot on the cell record, distinct from the kernel cap table — writing it does NOT amplify
authority.) -/
theorem execFullA_setPermissions_capFrame {s s' : RecChainedState} {actor cell : CellId}
    {p : Int} (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  ((execFullA_setPermissions_iff_spec s actor cell p s').mp h).2.2.2.2.1

/-- **`execFullA_setPermissions_otherCellsFrame` — every OTHER cell's whole record untouched.** -/
theorem execFullA_setPermissions_otherCellsFrame {s s' : RecChainedState} {actor cell : CellId}
    {p : Int} (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  have hspec := (execFullA_setPermissions_iff_spec s actor cell p s').mp h
  intro c hc
  rw [hspec.2.1]
  exact (setPermissions_cellWrite_correct s.kernel cell p).2.2 c hc

/-- **`execFullA_setPermissions_admits_guard` — a committed write means the guard held** (the
soundness projection: the arm commits IFF the three-leg admissibility gate is satisfied). -/
theorem execFullA_setPermissions_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    {p : Int} (h : execFullA s (.setPermissionsA actor cell p) = some s') :
    setPermsGuard s actor cell :=
  ((execFullA_setPermissions_iff_spec s actor cell p s').mp h).1

/-! ## §5 — NON-VACUITY: the guard genuinely REJECTS bad inputs.

A spec that the executor meets vacuously (because the arm accepts everything) is worthless. These
exhibit the arm as a genuine gate: an unauthorized actor, a non-account `cell`, and a non-Live
(sealed/destroyed) `cell` each make the arm FAIL CLOSED (`= none`), so no spec post-state exists. -/

/-- **`setPermissions_rejects_unauthorized` — PROVED.** If the actor does NOT hold authority over
`cell`, the arm fails closed: no committed post-state exists. -/
theorem setPermissions_rejects_unauthorized (s : RecChainedState) (actor cell : CellId) (p : Int)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    execFullA s (.setPermissionsA actor cell p) = none := by
  show stateStep s permsField actor cell (.int p) = none
  unfold stateStep
  rw [if_neg]
  rintro ⟨hauth, _, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`setPermissions_rejects_nonaccount` — PROVED.** If `cell` is not a live account, the arm fails
closed. -/
theorem setPermissions_rejects_nonaccount (s : RecChainedState) (actor cell : CellId) (p : Int)
    (hbad : cell ∉ s.kernel.accounts) :
    execFullA s (.setPermissionsA actor cell p) = none := by
  show stateStep s permsField actor cell (.int p) = none
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, hmem, _⟩; exact hbad hmem

/-- **`setPermissions_rejects_nonlive` — PROVED.** If `cell`'s lifecycle does NOT admit effects
(sealed/destroyed — the R6 gate), the arm fails closed. This is the executor-level lifecycle
enforcement: a permissions write into a sealed cell is REJECTED. -/
theorem setPermissions_rejects_nonlive (s : RecChainedState) (actor cell : CellId) (p : Int)
    (hbad : cellLive s.kernel cell = false) :
    execFullA s (.setPermissionsA actor cell p) = none := by
  show stateStep s permsField actor cell (.int p) = none
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, _, hlive⟩
  rw [hbad] at hlive; exact absurd hlive (by simp)

/-! ## §6 — Concrete #guard witnesses: a GOOD write commits to the spec'd state; BAD ones reject.

Cell 0 is a live self-owned account (actor 0 = cell 0, so `stateAuthB` passes by ownership). A write
of `permissions := 3` to cell 0 commits and reads back `3`. An unauthorized actor (9) is rejected. -/

/-- A concrete pre-state: one live account (cell 0), empty caps (authority by ownership), empty log. -/
def sSP0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun _ => .record [("permissions", .int 1)]
        caps := fun _ => [] }
    log := [] }

-- the executor COMMITS the good self-authored permissions write (actor 0 owns cell 0):
#guard (execFullA sSP0 (.setPermissionsA 0 0 3)).isSome  -- true

-- ...and the committed slot reads back exactly 3 (the write/read law on the real post-state):
#guard
  (match execFullA sSP0 (.setPermissionsA 0 0 3) with
   | some s' => decide (fieldOf permsField (s'.kernel.cell 0) = 3)
   | none    => false)  -- true

-- an UNAUTHORIZED actor (9 owns nothing, no cap over cell 0) is REJECTED:
#guard (execFullA sSP0 (.setPermissionsA 9 0 3)).isNone  -- true

-- a NON-ACCOUNT target (cell 5 ∉ accounts) is REJECTED:
#guard (execFullA sSP0 (.setPermissionsA 5 5 3)).isNone  -- true

/-! ## §7 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms setPermsCellMap_eq_writeField
#assert_axioms setPermissions_cellWrite_correct
#assert_axioms stateStep_iff_spec
#assert_axioms execFullA_setPermissions_iff_spec
#assert_axioms execFullA_setPermissions_permsSet
#assert_axioms execFullA_setPermissions_balFrame
#assert_axioms execFullA_setPermissions_capFrame
#assert_axioms execFullA_setPermissions_otherCellsFrame
#assert_axioms execFullA_setPermissions_admits_guard
#assert_axioms setPermissions_rejects_unauthorized
#assert_axioms setPermissions_rejects_nonaccount
#assert_axioms setPermissions_rejects_nonlive

end Dregg2.Circuit.Spec.CellStatePermissions
