/-
# Dregg2.Circuit.Spec.cellstateaudit — INDEPENDENT full-state spec + executor⟺spec for the
  "cell-state-audit" effect family (variants: `refusalA`, `receiptArchiveA`).

This is a LEAF spec module in the shape of `Dregg2.Circuit.Transfer` (`TransferSpec` +
`recKExec_iff_spec` + `recTransfer_correct`) and its sibling `Dregg2.Circuit.Spec.cellstatevk`, but
for the two PROTOCOL-managed cell-audit slot writes the live executor runs in its `.refusalA` /
`.receiptArchiveA` arms (`TurnExecutorFull.execFullA`, `:3565`/`:3566`):

    execFullA s (.refusalA actor cell)        =  stateStep s refusalField   actor cell (.int 1)
    execFullA s (.receiptArchiveA actor cell) =  stateStep s lifecycleField actor cell (.int 1)

These are dregg1's cross-cell audit writes: `refusalA` flips the `"refusal"` audit slot to `1` (a
SetState refusal commitment — per dregg1 the refusal gate is cross-cell on `SetState`), and
`receiptArchiveA` flips the `"lifecycle"` RECORD slot to `1` (a receipt-archive lifecycle commitment).
Both write a FIXED value `.int 1` (a one-shot commitment flag), gated on the SAME authority leg
`stateAuthB s.kernel.caps actor cell` that the developer-facing `setFieldA` and the protocol VK write
use — so they stay on the bare authority-gated `stateStep` (NOT the per-slot caveat gate
`stateStepGuarded`).

`stateStep` (EffectsState.lean:207) commits iff its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: the actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the field (`refusal` / `lifecycle`) of `cell` to `1` (`writeField`, touching
ONLY that cell's audit slot in the `cell` map), and extends the receipt chain by one self-targeted
row. NO balance move, NO cap edit, and — critically — NO edit of the `k.lifecycle` SIDE-TABLE that
`cellLive` consults (see the `receiptArchiveA` note below). THIS module proves the executor meets an
INDEPENDENT declarative full-state spec EXACTLY (both directions), enumerating ALL 17 kernel fields +
the `log` so no ghost field can be silently mutated.

## A subtlety re `receiptArchiveA` (recorded, NOT a gap)

`receiptArchiveA` writes the `"lifecycle"` RECORD FIELD — i.e. it sets slot `"lifecycle"` inside the
`cell` MAP's record at index `cell`. This is a DIFFERENT object from `RecordKernelState.lifecycle`,
the `CellId → Int` SIDE-TABLE that `cellLive`/the R6 gate reads. So the audit write does NOT touch
the liveness discriminant: the spec's frame clause `s'.kernel.lifecycle = s.kernel.lifecycle` (the
side-table) holds, and the cell can still be re-targeted later. This is a genuine confirmation
(`stateStep` only edits `cell`), surfaced here because the name collision could otherwise hide a
frame interaction. No `frameGaps` arise.

## What is proved (the §6b corner of the spec⟺executor triangle, copied from `Transfer.lean`)

  1. `RefusalSpec` / `ReceiptArchiveSpec` : Prop — the INDEPENDENT declarative full-state post-states:
     the three-leg guard ∧ the EXACT `cell`-map post-image (the audit slot of `cell` set to `1`, every
     other cell's whole record untouched) ∧ EVERY OTHER kernel field (16 of them) LITERALLY unchanged
     ∧ the `log` extended by exactly the one self-targeted receipt row. No frame clause mentions
     `execFullA` / `stateStep`.

  2. `execFullA_refusalA_iff_spec` / `execFullA_receiptArchiveA_iff_spec` : both directions. The `→`
     half VALIDATES the executor: all 17 kernel components + the `log` are checked, so a silently
     mutated field would make the proof FAIL → reported in `frameGaps` (none arose).

  3. `auditCellWrite_correct` — the post-state-helper validation lemma (mirrors `recTransfer_correct`):
     the audit-write helper sets `cell`'s audit slot to exactly `1`, leaves `cell`'s conserved
     `balance` (a DISTINCT slot) intact, and leaves every OTHER cell's whole record untouched.

  4. `#assert_axioms` on every theorem — whitelist `{propext, Classical.choice, Quot.sound}` only.

The generic `auditStateStep_iff_spec` engine below is re-derived LOCALLY (so this leaf is
self-contained — no dependence on a sibling spec module) and specialized to BOTH variants over their
respective fields (`refusalField`, `lifecycleField`) at the fixed value `1`.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStateAudit

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps)

set_option linter.dupNamespace false

/-! ## §1 — the admissibility guard `stateStep`/`refusalA`/`receiptArchiveA` checks, as a `Prop`.

The exact conjunction in `stateStep`'s `if` (EffectsState.lean:209) — extracting it makes the
spec⟺executor proof a clean re-assembly, mirroring `Transfer.admitGuard` / `CellStateVK.setVKGuard`.
Both audit variants share THIS gate (they differ only in which field/value they write). -/

/-- **`auditGuard` — the three-leg admissibility gate** the executor checks before it commits a
`refusalA` or `receiptArchiveA`: AUTHORITY over `cell` (`stateAuthB` — dregg1's cross-cell SetState
refusal authority leg), `cell` is a live account (MEMBERSHIP), and `cell`'s lifecycle admits effects
(LIVENESS — the R6 gate). Stated independently of the executor term. -/
def auditGuard (s : RecChainedState) (actor cell : CellId) : Prop :=
  stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — the post-state cell-map helper, validated DECLARATIVELY (not trusted).

`auditCellMap k cell f` is the `cell`-indexed record map a committed audit write produces: cell
`cell`'s audit slot `f` set to `1` (its other fields kept), every other cell whole-preserved. Written
WITHOUT the executor's `writeField` so the spec's `cell`-clause is the genuine semantics, and proved
equal to `writeField … f … (.int 1)` so the executor's actual post-cell-map meets it. -/

/-- The declarative post-cell-map of an audit write: only `cell`'s slot `f` moves (to `1`). -/
def auditCellMap (k : RecordKernelState) (cell : CellId) (f : FieldName) : CellId → Value :=
  fun c => if c = cell then setField f (k.cell c) (.int 1) else k.cell c

/-- **`auditCellMap_eq_writeField` — the helper matches the executor's `writeField`** (so the
declarative cell-clause and the executor's actual post-cell-map are the SAME function). -/
theorem auditCellMap_eq_writeField (k : RecordKernelState) (cell : CellId) (f : FieldName) :
    auditCellMap k cell f = (writeField k f cell (.int 1)).cell := by
  rfl

/-- **`auditCellWrite_correct` — the cell-update helper validated DECLARATIVELY** (the
`recTransfer_correct` analog). An audit write to a slot `f` DISTINCT from `balance` (a) sets `cell`'s
slot `f` to exactly `1`, (b) leaves `cell`'s conserved `balance` field untouched (the regime's
balance-Δ=0 obligation, via the non-interference of a distinct slot), and (c) leaves every OTHER
cell's whole record untouched. So the spec's `cell`-clause encodes write ∧ balance-frame ∧
cell-frame, rather than blindly trusting the helper. -/
theorem auditCellWrite_correct (k : RecordKernelState) (cell : CellId) (f : FieldName)
    (hf : f ≠ balanceField) :
    fieldOf f (auditCellMap k cell f cell) = 1
    ∧ balOf (auditCellMap k cell f cell) = balOf (k.cell cell)
    ∧ (∀ c, c ≠ cell → auditCellMap k cell f c = k.cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [auditCellMap, if_pos]; exact setField_fieldOf f (k.cell cell) 1
  · simp only [auditCellMap, if_pos]
    exact setField_balOf f (k.cell cell) (.int 1) hf
  · intro c hc; simp only [auditCellMap, if_neg hc]

/-! ## §3 — the GENERIC `stateStep` characterization (executor⟺spec, full state), re-derived LOCALLY.

The bare `stateStep` (the engine BOTH audit arms run) commits a write of field `f`:=`(.int 1)` into
`s'` IFF `s'` is EXACTLY the three-leg-gated full post-state: the `cell` map is the single-field
write, the `log` is the one-row self-targeted extension, and ALL 16 other kernel components are
literally unchanged. The `→` direction VALIDATES `stateStep` — all 17 kernel components + the `log`
are checked, so a silently mutated `bal`/`nullifiers`/`caps`/… would make the frame clauses FAIL; the
`←` reconstructs the committed state from the spec. The two variant theorems below are clean
instances of this. -/

theorem auditStateStep_iff_spec (s : RecChainedState) (f : FieldName) (actor cell : CellId)
    (s' : RecChainedState) :
    stateStep s f actor cell (.int 1) = some s' ↔
      ( (stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
            ∧ cellLive s.kernel cell = true)
        ∧ s'.kernel.cell = (fun c => if c = cell then setField f (s.kernel.cell c) (.int 1)
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
        ∧ s'.kernel.heaps = s.kernel.heaps ) := by
  unfold stateStep
  by_cases hg : stateAuthB s.kernel.caps actor cell = true ∧ cell ∈ s.kernel.accounts
      ∧ cellLive s.kernel cell = true
  · rw [if_pos hg]
    constructor
    · intro h
      simp only [Option.some.injEq] at h; subst h
      refine ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rintro ⟨_, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
      obtain ⟨k', l'⟩ := s'
      obtain ⟨a, ce, ca, nu, re, co, ba, sl, fa, li, dc, de, dg, dge, dgea, hp⟩ := k'
      simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      subst hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-! ## §4 — VARIANT 1: `refusalA` — the FULL-STATE declarative spec (INDEPENDENT reference) + ⟺.

The `.refusalA` arm writes the `"refusal"` audit slot to `1` — dregg1's cross-cell SetState refusal
commitment. `RefusalSpec` is the COMPLETE state transition written INDEPENDENTLY of the executor (no
`execFullA`/`stateStep` term in any frame clause): the three-leg guard holds; the post-state's `cell`
map is the refusal-slot write (`auditCellMap … refusalField`, validated above); the `log` is extended
by exactly the one self-targeted receipt row; and ALL 16 non-`cell` kernel components — `accounts`
`caps` `escrows` `nullifiers` `revoked` `commitments` `bal` `queues` `swiss` `slotCaveats`
`factories` `lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes` — are LITERALLY unchanged.
Missing ANY reintroduces a ghost, so all 17 kernel fields + the `log` are enumerated. -/

/-- **`RefusalSpec` — the full-state declarative spec of a committed `refusalA`.** The guard holds;
the `cell` map is the `"refusal" := 1` write (every other cell whole, `cell`'s other fields kept);
the `log` is the one-row self-targeted extension; every non-`cell` kernel component unchanged. No
frame clause mentions the executor. -/
def RefusalSpec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) : Prop :=
  auditGuard s actor cell
  ∧ s'.kernel.cell = auditCellMap s.kernel cell refusalField
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

/-- The `.refusalA` arm of `execFullA` is DEFINITIONALLY the bare authority-gated refusal-slot write
— the seam the whole bridge sits on. -/
theorem execFullA_refusalA_eq (s : RecChainedState) (actor cell : CellId) :
    execFullA s (.refusalA actor cell) = stateStep s refusalField actor cell (.int 1) := rfl

/-- **`execFullA_refusalA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The live
executor's `.refusalA` arm commits a refusal write into `s'` IFF `s'` is EXACTLY the spec'd full
post-state. The `→` direction VALIDATES the executor against the independent spec — all 17 kernel
components + the `log` are checked, so had the arm silently mutated `bal`/`nullifiers`/`caps`/… the
frame clauses would make this proof FAIL; the `←` reconstructs the committed state from the spec. -/
theorem execFullA_refusalA_iff_spec (s : RecChainedState) (actor cell : CellId)
    (s' : RecChainedState) :
    execFullA s (.refusalA actor cell) = some s' ↔ RefusalSpec s actor cell s' := by
  rw [execFullA_refusalA_eq, auditStateStep_iff_spec]
  unfold RefusalSpec auditGuard auditCellMap
  rfl

/-! ## §5 — VARIANT 2: `receiptArchiveA` — the FULL-STATE declarative spec + ⟺.

The `.receiptArchiveA` arm writes the `"lifecycle"` RECORD slot to `1` — a receipt-archive lifecycle
commitment. (Recall: this is the record FIELD inside the `cell` map, NOT the `k.lifecycle`
side-table — the spec's `s'.kernel.lifecycle = s.kernel.lifecycle` frame clause confirms the
side-table is untouched.) `ReceiptArchiveSpec` is the COMPLETE state transition, written
INDEPENDENTLY of the executor, enumerating all 17 kernel fields + the `log`. -/

/-- **`ReceiptArchiveSpec` — the full-state declarative spec of a committed `receiptArchiveA`.** The
guard holds; the `cell` map is the `"lifecycle" := 1` RECORD-slot write (every other cell whole,
`cell`'s other fields kept); the `log` is the one-row self-targeted extension; every non-`cell`
kernel component unchanged — INCLUDING the `lifecycle` SIDE-TABLE (a distinct object from the record
slot). No frame clause mentions the executor. -/
def ReceiptArchiveSpec (s : RecChainedState) (actor cell : CellId) (s' : RecChainedState) : Prop :=
  auditGuard s actor cell
  ∧ s'.kernel.cell = auditCellMap s.kernel cell lifecycleField
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

/-- The `.receiptArchiveA` arm of `execFullA` is DEFINITIONALLY the bare authority-gated lifecycle-slot
write. -/
theorem execFullA_receiptArchiveA_eq (s : RecChainedState) (actor cell : CellId) :
    execFullA s (.receiptArchiveA actor cell) = stateStep s lifecycleField actor cell (.int 1) := rfl

/-- **`execFullA_receiptArchiveA_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** Mirrors
`execFullA_refusalA_iff_spec` for the lifecycle-slot audit write. The `→` direction VALIDATES the
executor against the independent spec; the `←` reconstructs the committed state. -/
theorem execFullA_receiptArchiveA_iff_spec (s : RecChainedState) (actor cell : CellId)
    (s' : RecChainedState) :
    execFullA s (.receiptArchiveA actor cell) = some s' ↔ ReceiptArchiveSpec s actor cell s' := by
  rw [execFullA_receiptArchiveA_eq, auditStateStep_iff_spec]
  unfold ReceiptArchiveSpec auditGuard auditCellMap
  rfl

/-! ## §6 — corollaries: the touched component + the balance/cap/lifecycle-side-table frame.

These are the cell-state-audit analogs of `CellStateVK`'s VK-write facts: a committed audit write
sets the audit slot to exactly `1`, leaves the conserved balance untouched (regime balance-Δ=0),
leaves the cap-graph untouched (no authority amplification), and leaves the `lifecycle` SIDE-TABLE
untouched (so liveness is preserved). Each is a clean read off the `…_iff_spec` theorems. -/

/-- **`refusalA_slotWritten` — the `"refusal"` slot is set to exactly `1`.** -/
theorem refusalA_slotWritten {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.refusalA actor cell) = some s') :
    fieldOf refusalField (s'.kernel.cell cell) = 1 := by
  have hspec := (execFullA_refusalA_iff_spec s actor cell s').mp h
  rw [hspec.2.1]
  exact (auditCellWrite_correct s.kernel cell refusalField (by decide)).1

/-- **`receiptArchiveA_slotWritten` — the `"lifecycle"` RECORD slot is set to exactly `1`.** -/
theorem receiptArchiveA_slotWritten {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    fieldOf lifecycleField (s'.kernel.cell cell) = 1 := by
  have hspec := (execFullA_receiptArchiveA_iff_spec s actor cell s').mp h
  rw [hspec.2.1]
  exact (auditCellWrite_correct s.kernel cell lifecycleField (by decide)).1

/-- **`refusalA_balFrame` — BALANCE LEDGER untouched (the regime balance-Δ=0).** -/
theorem refusalA_balFrame {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.refusalA actor cell) = some s') :
    s'.kernel.bal = s.kernel.bal :=
  ((execFullA_refusalA_iff_spec s actor cell s').mp h).2.2.2.2.2.2.2.2.1

/-- **`refusalA_capFrame` — CAP-GRAPH untouched (no authority amplification).** -/
theorem refusalA_capFrame {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.refusalA actor cell) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  ((execFullA_refusalA_iff_spec s actor cell s').mp h).2.2.2.2.1

/-- **`receiptArchiveA_lifecycleSideTableFrame` — the `lifecycle` SIDE-TABLE untouched.** The audit
write moves only the RECORD slot `"lifecycle"`, NOT the `CellId → Int` liveness discriminant — so the
cell's liveness (`cellLive`) is preserved. This is the load-bearing confirmation that the name
collision hides no frame interaction. -/
theorem receiptArchiveA_lifecycleSideTableFrame {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    s'.kernel.lifecycle = s.kernel.lifecycle :=
  ((execFullA_receiptArchiveA_iff_spec s actor cell s').mp h).2.2.2.2.2.2.2.2.2.2.2.1

/-- **`refusalA_otherCellsFrame` — every OTHER cell's whole record untouched.** -/
theorem refusalA_otherCellsFrame {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.refusalA actor cell) = some s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  have hspec := (execFullA_refusalA_iff_spec s actor cell s').mp h
  intro c hc
  rw [hspec.2.1]
  exact (auditCellWrite_correct s.kernel cell refusalField (by decide)).2.2 c hc

/-- **`refusalA_admits_guard` — a committed refusal write means the guard held.** -/
theorem refusalA_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.refusalA actor cell) = some s') :
    auditGuard s actor cell :=
  ((execFullA_refusalA_iff_spec s actor cell s').mp h).1

/-- **`receiptArchiveA_admits_guard` — a committed archive write means the guard held.** -/
theorem receiptArchiveA_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    (h : execFullA s (.receiptArchiveA actor cell) = some s') :
    auditGuard s actor cell :=
  ((execFullA_receiptArchiveA_iff_spec s actor cell s').mp h).1

/-! ## §7 — NON-VACUITY: the guard REJECTS bad inputs (fail-closed teeth).

A spec the executor meets vacuously (the arm accepts everything) is worthless. These exhibit each
arm as a genuine gate: an unauthorized actor, a non-account `cell`, and a non-Live cell each make the
arm FAIL CLOSED (`= none`), so no spec post-state exists. Both variants share the gate, so we prove
the rejections for `refusalA` and lift `receiptArchiveA` via the same `stateStep` `if_neg`. -/

/-- **`refusalA_rejects_unauthorized`.** If the actor does NOT hold authority over `cell`
(`stateAuthB = false`, the cross-cell SetState refusal authority leg failing), the arm fails closed. -/
theorem refusalA_rejects_unauthorized (s : RecChainedState) (actor cell : CellId)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    execFullA s (.refusalA actor cell) = none := by
  rw [execFullA_refusalA_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨hauth, _, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`refusalA_rejects_nonaccount`.** If `cell` is not a live account, the arm fails closed. -/
theorem refusalA_rejects_nonaccount (s : RecChainedState) (actor cell : CellId)
    (hbad : cell ∉ s.kernel.accounts) :
    execFullA s (.refusalA actor cell) = none := by
  rw [execFullA_refusalA_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, hmem, _⟩; exact hbad hmem

/-- **`refusalA_rejects_nonlive`.** If `cell`'s lifecycle does NOT admit effects
(sealed/destroyed — the R6 gate), the arm fails closed: a refusal commitment cannot be stamped into a
dead cell. -/
theorem refusalA_rejects_nonlive (s : RecChainedState) (actor cell : CellId)
    (hbad : cellLive s.kernel cell = false) :
    execFullA s (.refusalA actor cell) = none := by
  rw [execFullA_refusalA_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, _, hlive⟩
  rw [hbad] at hlive; exact absurd hlive (by simp)

/-- **`receiptArchiveA_rejects_unauthorized`.** -/
theorem receiptArchiveA_rejects_unauthorized (s : RecChainedState) (actor cell : CellId)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    execFullA s (.receiptArchiveA actor cell) = none := by
  rw [execFullA_receiptArchiveA_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨hauth, _, _⟩
  rw [hbad] at hauth; exact absurd hauth (by simp)

/-- **`receiptArchiveA_rejects_nonlive`.** A receipt-archive commitment cannot be stamped
into a sealed/destroyed cell. -/
theorem receiptArchiveA_rejects_nonlive (s : RecChainedState) (actor cell : CellId)
    (hbad : cellLive s.kernel cell = false) :
    execFullA s (.receiptArchiveA actor cell) = none := by
  rw [execFullA_receiptArchiveA_eq]
  unfold stateStep
  rw [if_neg]
  rintro ⟨_, _, hlive⟩
  rw [hbad] at hlive; exact absurd hlive (by simp)

/-! ## §8 — Concrete #guard witnesses: a GOOD audit write commits to the spec'd slot; BAD ones reject.

Cell 0 is a live self-owned account (actor 0 = cell 0, so `stateAuthB` passes by ownership; lifecycle
side-table `0` = Live, so `cellLive` passes). A refusal/archive write to cell 0 commits and the slot
reads back `1`. The unauthorized actor (9 owns nothing) is fail-closed REJECTED. -/

/-- A concrete pre-state: one live account (cell 0), empty caps (authority by ownership), empty log,
default lifecycle side-table (`0` = Live everywhere). -/
def sAUD0 : RecChainedState :=
  { kernel :=
      { accounts := {0}
        cell := fun _ => .record [("balance", .int 42)]
        caps := fun _ => [] }
    log := [] }

-- the executor COMMITS the good self-authored refusal write (actor 0 owns cell 0, cell 0 Live):
#guard (execFullA sAUD0 (.refusalA 0 0)).isSome  -- true
-- ...and the committed `"refusal"` slot reads back exactly 1:
#guard
  (match execFullA sAUD0 (.refusalA 0 0) with
   | some s' => decide (fieldOf "refusal" (s'.kernel.cell 0) = 1)
   | none    => false)  -- true
-- the balance slot is untouched (still 42 — balance-Δ=0):
#guard
  (match execFullA sAUD0 (.refusalA 0 0) with
   | some s' => decide (fieldOf "balance" (s'.kernel.cell 0) = 42)
   | none    => false)  -- true

-- the executor COMMITS the good self-authored receipt-archive write:
#guard (execFullA sAUD0 (.receiptArchiveA 0 0)).isSome  -- true
-- ...and the committed `"lifecycle"` RECORD slot reads back exactly 1:
#guard
  (match execFullA sAUD0 (.receiptArchiveA 0 0) with
   | some s' => decide (fieldOf "lifecycle" (s'.kernel.cell 0) = 1)
   | none    => false)  -- true

-- an UNAUTHORIZED actor (9 owns nothing, no cap over cell 0) is REJECTED for BOTH variants:
#guard (execFullA sAUD0 (.refusalA 9 0)).isNone         -- true
#guard (execFullA sAUD0 (.receiptArchiveA 9 0)).isNone  -- true

/-! ## §9 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}` — no `sorryAx`/`admit`/`axiom`/
`native_decide`. -/

#assert_axioms auditCellMap_eq_writeField
#assert_axioms auditCellWrite_correct
#assert_axioms auditStateStep_iff_spec
#assert_axioms execFullA_refusalA_eq
#assert_axioms execFullA_refusalA_iff_spec
#assert_axioms execFullA_receiptArchiveA_eq
#assert_axioms execFullA_receiptArchiveA_iff_spec
#assert_axioms refusalA_slotWritten
#assert_axioms receiptArchiveA_slotWritten
#assert_axioms refusalA_balFrame
#assert_axioms refusalA_capFrame
#assert_axioms receiptArchiveA_lifecycleSideTableFrame
#assert_axioms refusalA_otherCellsFrame
#assert_axioms refusalA_admits_guard
#assert_axioms receiptArchiveA_admits_guard
#assert_axioms refusalA_rejects_unauthorized
#assert_axioms refusalA_rejects_nonaccount
#assert_axioms refusalA_rejects_nonlive
#assert_axioms receiptArchiveA_rejects_unauthorized
#assert_axioms receiptArchiveA_rejects_nonlive

end Dregg2.Circuit.Spec.CellStateAudit
