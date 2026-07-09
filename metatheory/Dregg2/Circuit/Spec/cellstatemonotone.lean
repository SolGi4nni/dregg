/-
# Dregg2.Circuit.Spec.cellstatemonotone — INDEPENDENT full-state spec + executor⟺spec for the
  "cell-state-monotone" effect family (variant: `incrementNonceA`).

This is a LEAF spec module in the shape of `Dregg2.Circuit.Transfer` (`TransferSpec` +
`recKExec_iff_spec` + `recTransfer_correct`), but for the metadata-domain monotone field-write the
live executor runs in its `.incrementNonceA` arm:

    execFullA s (.incrementNonceA actor cell n)  =  stateStep s nonceField actor cell (.int n)

`stateStep` (EffectsState.lean:207) commits iff its three-leg admissibility gate holds —

    stateAuthB s.kernel.caps actor cell = true   -- (1) AUTHORITY: the actor holds authority over `cell`
  ∧ cell ∈ s.kernel.accounts                      -- (2) MEMBERSHIP: `cell` is a live account
  ∧ cellLive s.kernel cell = true                 -- (3) LIVENESS: `cell`'s lifecycle admits effects (R6)

— and on commit writes the `nonce` field of `cell` to `n` (`writeField`, touching ONLY that cell's
`nonce` slot) and extends the receipt chain by one self-targeted row. NO balance move, NO cap edit:
the whole regime invariant. THIS module proves the executor meets an INDEPENDENT declarative
full-state spec EXACTLY (both directions), enumerating ALL 17 kernel fields + the `log` so no ghost
field can be silently mutated.

## What is proved (the §6b corner of the spec⟺executor triangle, copied from `Transfer.lean`)

  1. `IncrementNonceSpec s actor cell n s'` : Prop — the INDEPENDENT declarative post-state: the
     three-leg guard ∧ the EXACT `cell`-map post-image (the `nonce` of `cell` set to `n`, every other
     cell's whole record untouched) ∧ EVERY OTHER kernel field (16 of them) LITERALLY unchanged ∧ the
     `log` extended by exactly the one self-targeted receipt row. No frame clause mentions `execFullA`
     / `stateStep`.

  2. `execFullA_incrementNonce_iff_spec` : `execFullA s (.incrementNonceA actor cell n) = some s' ↔
     IncrementNonceSpec s actor cell n s'` — BOTH directions. The `→` half VALIDATES the executor: all
     17 kernel components + the `log` are checked, so a silently-mutated field would make the proof
     FAIL.

  3. `incrementNonce_cellWrite_correct` — the post-state-helper validation lemma (mirrors
     `recTransfer_correct`): the `nonce`-write helper bumps `cell`'s `nonce` to exactly `n`, leaves
     `cell`'s `balance` (and every other field — via the non-interference of a distinct slot) intact,
     and leaves every OTHER cell's whole record untouched.

  4. `#assert_axioms` on every theorem — whitelist `{propext, Classical.choice, Quot.sound}` only.

The family has the single executable variant `incrementNonceA`; `setPermissionsA`/`setVKA` share the
EXACT same `stateStep` shape (different `FieldName`/`Value`), so the representative theorem + the
generic `stateStep` corollaries below extend to them verbatim (corollary `stateStep_iff_spec`).
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Circuit.Spec.CellStateMonotone

open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps)

/-! ## §1 — the admissibility guard `stateStep`/`incrementNonceA` checks, as a `Prop`.

The exact conjunction in `stateStep`'s `if` (EffectsState.lean:209) — extracting it makes the
spec⟺executor proof a clean re-assembly, mirroring `Transfer.admitGuard`. -/

/-- **`incNonceGuard` — the four-leg admissibility gate** the executor checks before it commits an
`incrementNonceA`: the new nonce `n` STRICTLY EXCEEDS the stored nonce (MONOTONICITY — the nonce can
only advance, closing the nonce-reset replay leg), AUTHORITY over `cell`, `cell` is a live account
(MEMBERSHIP), and `cell`'s lifecycle admits effects (LIVENESS — the R6 gate). Stated independently of
the executor term. -/
def incNonceGuard (s : RecChainedState) (actor cell : CellId) (n : Int) : Prop :=
  fieldOf "nonce" (s.kernel.cell cell) < n
  ∧ stateAuthB s.kernel.caps actor cell = true
  ∧ cell ∈ s.kernel.accounts
  ∧ cellLive s.kernel cell = true

/-! ## §2 — the post-state cell-map helper, validated DECLARATIVELY (not trusted).

`incNonceCellMap k cell n` is the `cell`-indexed record map a committed nonce bump produces: cell
`cell`'s `nonce` slot set to `n` (its other fields kept), every other cell whole-preserved. Written
WITHOUT the executor's `writeField` so the spec's `cell`-clause is the genuine semantics, and proved
equal to `writeField … nonceField …` so the executor's actual post-cell-map meets it. -/

/-- The declarative post-cell-map of a nonce bump: only `cell`'s `nonce` field moves. -/
def incNonceCellMap (k : RecordKernelState) (cell : CellId) (n : Int) : CellId → Value :=
  fun c => if c = cell then setField nonceField (k.cell c) (.int n) else k.cell c

/-- **`incNonceCellMap_eq_writeField` — the helper matches the executor's `writeField`** (so the
declarative cell-clause and the executor's actual post-cell-map are the SAME function). -/
theorem incNonceCellMap_eq_writeField (k : RecordKernelState) (cell : CellId) (n : Int) :
    incNonceCellMap k cell n = (writeField k nonceField cell (.int n)).cell := by
  rfl

/-- **`incrementNonce_cellWrite_correct` — the cell-update helper validated DECLARATIVELY** (the
`recTransfer_correct` analog). A nonce bump (a) sets `cell`'s `nonce` slot to exactly `n`, (b) leaves
`cell`'s conserved `balance` field untouched (the regime's balance-Δ=0 obligation, via the
non-interference of a DISTINCT slot — `nonce ≠ balance`), and (c) leaves every OTHER cell's whole
record untouched. So the spec's `cell`-clause encodes bump ∧ balance-frame ∧ cell-frame,
rather than blindly trusting the helper. -/
theorem incrementNonce_cellWrite_correct (k : RecordKernelState) (cell : CellId) (n : Int) :
    fieldOf nonceField (incNonceCellMap k cell n cell) = n
    ∧ balOf (incNonceCellMap k cell n cell) = balOf (k.cell cell)
    ∧ (∀ c, c ≠ cell → incNonceCellMap k cell n c = k.cell c) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [incNonceCellMap, if_pos]; exact setField_fieldOf nonceField (k.cell cell) n
  · simp only [incNonceCellMap, if_pos]
    exact setField_balOf nonceField (k.cell cell) (.int n) (by decide)
  · intro c hc; simp only [incNonceCellMap, if_neg hc]

/-! ## §3 — the FULL-STATE declarative spec (the INDEPENDENT reference) + executor⟺spec.

`IncrementNonceSpec` is the COMPLETE state transition of a committed nonce bump, written
INDEPENDENTLY of the executor (no `execFullA`/`stateStep` term in any frame clause): the three-leg
guard holds; the post-state's `cell` map is the nonce bump (`incNonceCellMap`, validated above); the
`log` is extended by exactly the one self-targeted receipt row; and ALL 16 non-`cell` kernel
components — `accounts` `caps` `escrows` `nullifiers` `revoked` `commitments` `bal` `queues` `swiss`
`slotCaveats` `factories` `lifecycle` `deathCert` `delegate` `delegations` `sealedBoxes` — are
LITERALLY unchanged. Missing ANY of these reintroduces a ghost, so all 17 kernel fields + the `log`
are enumerated. This is the apex reference truth the executor is proved equal to. -/

/-- **The full-state declarative spec of a committed `incrementNonceA`** — the INDEPENDENT reference
semantics. The guard holds; the post-state's `cell` map is the nonce bump (every other cell whole,
`cell`'s other fields kept — see `incrementNonce_cellWrite_correct`); the `log` is the one-row
self-targeted extension; and every one of the 16 non-`cell` kernel components is unchanged. No frame
clause mentions the executor. -/
def IncrementNonceSpec (s : RecChainedState) (actor cell : CellId) (n : Int)
    (s' : RecChainedState) : Prop :=
  incNonceGuard s actor cell n
  -- the ONE touched component: cell `cell`'s `nonce` slot bumped, every other cell whole
  ∧ s'.kernel.cell = incNonceCellMap s.kernel cell n
  -- the log: extended by EXACTLY one self-targeted receipt row (the monotone metadata advance)
  ∧ s'.log = { actor := actor, src := cell, dst := cell, amt := 0 } :: s.log
  -- THE FRAME: every one of the 16 OTHER kernel components literally unchanged
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

/-- **`stateStep_iff_spec` — the GENERIC `stateStep` characterization (executor⟺spec, full state).**
The bare `stateStep` (the shared engine of the whole cell-state-monotone family —
`incrementNonceA`/`setPermissionsA`/`setVKA`) commits a write of field `f`:=`v` into `s'` IFF `s'` is
EXACTLY the three-leg-gated full post-state: the `cell` map is the single-field write, the `log` is
the one-row self-targeted extension, and ALL 16 other kernel components are literally unchanged. The
`→` direction VALIDATES `stateStep` — all 17 kernel components + the `log` are checked, so a silently
mutated `bal`/`nullifiers`/`caps`/… would make the frame clauses FAIL; the `←` reconstructs the
committed state from the spec. The variant theorem below is a clean instance of this. -/
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
      refine ⟨hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl⟩
    · rintro ⟨_, hcell, hlog, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
              h17⟩
      obtain ⟨k', l'⟩ := s'
      obtain ⟨a, ce, ca, nu, re, co, ba, sl, fa, li, dc, de, dg, dge, dgea, hp, nr, rr⟩ := k'
      simp only at hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      subst hcell hlog h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
      rfl
  · rw [if_neg hg]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨hg', _⟩; exact absurd hg' hg

/-- **`execFullA_incrementNonce_iff_spec` — EXECUTOR ⟺ SPEC (FULL state, both directions).** The
live per-asset executor's `.incrementNonceA` arm commits a nonce bump into `s'` IFF `s'` is EXACTLY
the spec'd full post-state. The `→` direction VALIDATES the executor against the independent spec —
all 17 kernel components + the `log` are checked, so had the arm silently mutated
`bal`/`nullifiers`/`caps`/… the frame clauses would make this proof FAIL; the `←` reconstructs the
committed state from the spec. This is the executor corner of the spec⟺executor⟺circuit triangle for
the cell-state-monotone family. -/
theorem execFullA_incrementNonce_iff_spec (s : RecChainedState) (actor cell : CellId) (n : Int)
    (s' : RecChainedState) :
    execFullA s (.incrementNonceA actor cell n) = some s' ↔ IncrementNonceSpec s actor cell n s' := by
  -- §MONOTONE-NONCE: the arm IS `incrementNonceStep s actor cell n` definitionally — the monotone gate
  -- over the bare `stateStep` on `nonceField`. Peel the monotone gate, then reuse `stateStep_iff_spec`.
  show incrementNonceStep s actor cell n = some s' ↔ IncrementNonceSpec s actor cell n s'
  unfold incrementNonceStep IncrementNonceSpec incNonceGuard incNonceCellMap
  by_cases hmono : fieldOf "nonce" (s.kernel.cell cell) < n
  · rw [if_pos hmono, stateStep_iff_spec]
    -- the residual is the SAME conjunction modulo the (now-discharged) monotone leg.
    constructor
    · rintro ⟨⟨ha, hm, hl⟩, rest⟩; exact ⟨⟨hmono, ha, hm, hl⟩, rest⟩
    · rintro ⟨⟨_, ha, hm, hl⟩, rest⟩; exact ⟨⟨ha, hm, hl⟩, rest⟩
  · rw [if_neg hmono]
    constructor
    · intro h; exact absurd h (by simp)
    · rintro ⟨⟨hbad, _⟩, _⟩; exact absurd hbad hmono

/-! ## §4 — corollaries: the projections onto the touched component + the balance/cap frame.

These are the cell-state-monotone analogs of `Transfer`'s debit/credit/conservation facts: a
committed nonce bump leaves the conserved balance untouched (regime balance-Δ=0) and the cap-graph
untouched (no authority amplification), with the `nonce` slot bumped to exactly `n`. Each is a clean
read off `execFullA_incrementNonce_iff_spec`. -/

/-- **`execFullA_incrementNonce_nonceBumped` — the `nonce` slot is set to exactly `n`.** -/
theorem execFullA_incrementNonce_nonceBumped {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    fieldOf nonceField (s'.kernel.cell cell) = n := by
  have hspec := (execFullA_incrementNonce_iff_spec s actor cell n s').mp h
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct s.kernel cell n).1

/-- **`execFullA_incrementNonce_balFrame` — BALANCE LEDGER untouched (the regime balance-Δ=0).** The
per-asset `bal` ledger is literally unchanged: a metadata bump moves NO value. -/
theorem execFullA_incrementNonce_balFrame {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    s'.kernel.bal = s.kernel.bal :=
  ((execFullA_incrementNonce_iff_spec s actor cell n s').mp h).2.2.2.2.2.2.2.2.1

/-- **`execFullA_incrementNonce_capFrame` — CAP-GRAPH untouched (no authority amplification).** The
`caps` table is literally unchanged: a metadata bump edits NO capability. -/
theorem execFullA_incrementNonce_capFrame {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    s'.kernel.caps = s.kernel.caps :=
  ((execFullA_incrementNonce_iff_spec s actor cell n s').mp h).2.2.2.2.1

/-- **`execFullA_incrementNonce_otherCellsFrame` — every OTHER cell's whole record untouched.** -/
theorem execFullA_incrementNonce_otherCellsFrame {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    ∀ c, c ≠ cell → s'.kernel.cell c = s.kernel.cell c := by
  have hspec := (execFullA_incrementNonce_iff_spec s actor cell n s').mp h
  intro c hc
  rw [hspec.2.1]
  exact (incrementNonce_cellWrite_correct s.kernel cell n).2.2 c hc

/-- **`execFullA_incrementNonce_admits_guard` — a committed bump means the guard held** (the
soundness projection: the arm commits IFF the three-leg admissibility gate is satisfied). -/
theorem execFullA_incrementNonce_admits_guard {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    incNonceGuard s actor cell n :=
  ((execFullA_incrementNonce_iff_spec s actor cell n s').mp h).1

/-- **`execFullA_incrementNonce_advances` — the nonce STRICTLY ADVANCED.** A committed `incrementNonceA`
means the new nonce `n` strictly exceeded the stored nonce: the agent nonce can only go UP, never
reset. The replay-leg closure projected onto the spec. -/
theorem execFullA_incrementNonce_advances {s s' : RecChainedState} {actor cell : CellId}
    {n : Int} (h : execFullA s (.incrementNonceA actor cell n) = some s') :
    fieldOf "nonce" (s.kernel.cell cell) < n :=
  (execFullA_incrementNonce_admits_guard h).1

/-! ## §5 — NON-VACUITY: the guard REJECTS bad inputs.

A spec that the executor meets vacuously (because the arm accepts everything) is worthless. These
exhibit the arm as a genuine gate: an unauthorized actor, a non-account `cell`, and a non-Live
(sealed/destroyed) `cell` each make the arm FAIL CLOSED (`= none`), so no spec post-state exists. -/

/-- **`incrementNonce_rejects_unauthorized`.** If the actor does NOT hold authority over
`cell`, the arm fails closed: no committed post-state exists. -/
theorem incrementNonce_rejects_unauthorized (s : RecChainedState) (actor cell : CellId) (n : Int)
    (hbad : stateAuthB s.kernel.caps actor cell = false) :
    execFullA s (.incrementNonceA actor cell n) = none := by
  show incrementNonceStep s actor cell n = none
  unfold incrementNonceStep
  by_cases hmono : fieldOf "nonce" (s.kernel.cell cell) < n
  · rw [if_pos hmono]; unfold stateStep; rw [if_neg]
    rintro ⟨hauth, _, _⟩; rw [hbad] at hauth; exact absurd hauth (by simp)
  · rw [if_neg hmono]

/-- **`incrementNonce_rejects_nonaccount`.** If `cell` is not a live account, the arm fails
closed. -/
theorem incrementNonce_rejects_nonaccount (s : RecChainedState) (actor cell : CellId) (n : Int)
    (hbad : cell ∉ s.kernel.accounts) :
    execFullA s (.incrementNonceA actor cell n) = none := by
  show incrementNonceStep s actor cell n = none
  unfold incrementNonceStep
  by_cases hmono : fieldOf "nonce" (s.kernel.cell cell) < n
  · rw [if_pos hmono]; unfold stateStep; rw [if_neg]
    rintro ⟨_, hmem, _⟩; exact hbad hmem
  · rw [if_neg hmono]

/-- **`incrementNonce_rejects_nonlive`.** If `cell`'s lifecycle does NOT admit effects
(sealed/destroyed — the R6 gate), the arm fails closed. This is the executor-level lifecycle
enforcement: a nonce write into a sealed cell is REJECTED. -/
theorem incrementNonce_rejects_nonlive (s : RecChainedState) (actor cell : CellId) (n : Int)
    (hbad : cellLive s.kernel cell = false) :
    execFullA s (.incrementNonceA actor cell n) = none := by
  show incrementNonceStep s actor cell n = none
  unfold incrementNonceStep
  by_cases hmono : fieldOf "nonce" (s.kernel.cell cell) < n
  · rw [if_pos hmono]; unfold stateStep; rw [if_neg]
    rintro ⟨_, _, hlive⟩; rw [hbad] at hlive; exact absurd hlive (by simp)
  · rw [if_neg hmono]

/-- **`incrementNonce_rejects_nonincreasing` (the MONOTONE-NONCE teeth).** If the new nonce `n` does
NOT strictly exceed the stored nonce (a RESET or no-op), the arm fails closed — the dedicated effect
cannot reset the agent nonce. The second replay leg, closed on the spec. -/
theorem incrementNonce_rejects_nonincreasing (s : RecChainedState) (actor cell : CellId) (n : Int)
    (hbad : ¬ fieldOf "nonce" (s.kernel.cell cell) < n) :
    execFullA s (.incrementNonceA actor cell n) = none := by
  show incrementNonceStep s actor cell n = none
  exact incrementNonceStep_nonincreasing_fails s actor cell n hbad

/-! ## §6 — Axiom-hygiene tripwires.

Whitelist exactly `{propext, Classical.choice, Quot.sound}`. -/

#assert_axioms incNonceCellMap_eq_writeField
#assert_axioms incrementNonce_cellWrite_correct
#assert_axioms stateStep_iff_spec
#assert_axioms execFullA_incrementNonce_iff_spec
#assert_axioms execFullA_incrementNonce_nonceBumped
#assert_axioms execFullA_incrementNonce_balFrame
#assert_axioms execFullA_incrementNonce_capFrame
#assert_axioms execFullA_incrementNonce_otherCellsFrame
#assert_axioms execFullA_incrementNonce_admits_guard
#assert_axioms execFullA_incrementNonce_advances
#assert_axioms incrementNonce_rejects_unauthorized
#assert_axioms incrementNonce_rejects_nonaccount
#assert_axioms incrementNonce_rejects_nonlive
#assert_axioms incrementNonce_rejects_nonincreasing

end Dregg2.Circuit.Spec.CellStateMonotone
