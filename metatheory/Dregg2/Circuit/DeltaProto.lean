/-
# Dregg2.Circuit.DeltaProto — DEBT-B step 2: THE DELTA DE-RISK (a measured verdict, not a framework).

QUESTION under test (`docs/reference/DELTA-FUTURE.md`): the deployed Lean op `recTransfer` is a nested `if
c = src / c = dst` (`Exec/RecordKernel.lean:517`); the deployed RUST applies validated *relative* deltas
(`cell/src/ledger.rs`: `CellStateDelta.balance_change : i64`, folded by `apply_cell_delta` over
`LedgerDelta.updated : Vec<(CellId, CellStateDelta)>`). The prior `EffectsAsDataProto` measured that the
per-effect `by_cases <touched cells>` SURVIVES (relocates) when reconciling a fold against the nested-`if`.
DELTA-FUTURE's stronger claim: if the Lean deployed op were ITSELF the delta-fold, the reconciliation is
`rfl` and the `by_cases` VANISHES. This file TESTS that, and — the point the prior proto did not separate —
splits the RECURRING per-turn cost from the ONE-TIME per-effect migration cost.

Difference from `EffectsAsDataProto`: there the update datum was an ABSOLUTE `Value` overwrite whose value was
READ FROM THE PRE-STATE (`transferUpdates turn k` mentions `k`). Here the datum mirrors the Rust literally — a
RELATIVE `balanceChange : ℤ`, so `transferDelta turn` is state-INDEPENDENT data (needs no `k`). That is itself
strictly more faithful/composable than the absolute proto.

VERDICT (measured, recorded at §7): the per-effect `by_cases` becomes ZERO in the RECURRING square (§5) the
moment the migration lemma (§4) exists — the recurring cost is `denote_applyDelta` (shared, effect-free) plus
one rewrite. The `by_cases` lives ENTIRELY in the ONE-TIME migration lemma (§4, 2 per-cell `by_cases`), and
that lemma collapses to a guard-only case-split (0 per-cell `by_cases`, §6) if the deployed op is DEFINED as
the fold. So: RECURRING cost is `by_cases`-free; the residue is a ONE-TIME per-effect migration that VANISHES
under redefinition. Contrast the prior proto's "NO, it relocates" — correct for the current op, but it
measured only the reconciliation, never separating it as a one-time cost.

Builds ON the committed R3 (`Circuit/FinKernelStep.lean`, `Exec/RecordKernel.lean`) verbatim; edits NOTHING
committed. `lake build Dregg2.Circuit.DeltaProto` is green, sorry-free.
-/
import Dregg2.Circuit.FinKernelStep
import Mathlib.Logic.Function.Basic

namespace Dregg2.Circuit.DeltaProto

open Dregg2.Exec Dregg2.Authority
open Dregg2.Circuit.FinKernelState

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the RELATIVE delta as DATA (mirror of Rust `CellStateDelta`).

SUBSET MODELED (and why): the Rust `CellStateDelta` has six fields — `field_updates`, `nonce_increment`,
`balance_change`, `permission_changes`, `capability_grants`, `capability_revocations`. Transfer exercises
EXACTLY ONE of them: `balance_change` (`recTransfer` moves only the `balance` field). So `CellDelta` here
carries only `balanceChange : ℤ`. The other five are the footprint of OTHER effects (set-field, nonce, cap
grant/revoke) — modelling them here would be dead weight for the transfer measurement and is deferred to those
effects' lanes. This is the honest minimal subset, said plainly. -/

/-- A per-cell RELATIVE delta — the transfer subset of Rust `CellStateDelta` (`ledger.rs:35`): the signed
`balanceChange`. State-INDEPENDENT (unlike an absolute overwrite): the value it computes is read at APPLY time
from the cell, exactly as `apply_cell_delta` does (`old + delta.balance_change`, `ledger.rs:881`). -/
structure CellDelta where
  /-- signed balance change (Rust `balance_change : i64`); `apply` adds it to the cell's current balance. -/
  balanceChange : ℤ

/-- **`applyCellDelta d v`** — apply the relative delta to a cell record: `setBalance v (balOf v + Δ)`. The
Lean twin of `apply_cell_delta`'s `state.apply_balance_change` (`ledger.rs:881`). Touches ONLY the `balance`
field; every other field of the content-addressed record is preserved (`setBalance`). -/
def applyCellDelta (d : CellDelta) (v : Value) : Value :=
  setBalance v (balOf v + d.balanceChange)

/-- A delta-applied cell is never the `cell` map default `Value.int 0` (so the sparse `insertNZ` accepts it —
the same `setBalance_ne_default` the committed `finTransfer` rides; the map default is `Value.int 0`,
`FinKernelState.cell : CanonMap CellId Value (Value.int 0)`). -/
theorem applyCellDelta_ne_default (d : CellDelta) (v : Value) :
    applyCellDelta d v ≠ Value.int 0 := setBalance_ne_default _ _

/-- **`applyDeltaRec`** — fold a `(CellId × CellDelta)` list into a `RecordKernelState`, each step a
`Function.update` of the total `cell` function (the Rust `for (id, delta) in updated` loop, `ledger.rs:718`). -/
def applyDeltaRec : List (CellId × CellDelta) → RecordKernelState → RecordKernelState
  | [],           k => k
  | (c, d) :: ds, k =>
      applyDeltaRec ds { k with cell := Function.update k.cell c (applyCellDelta d (k.cell c)) }

/-- **`applyDeltaFin`** — fold the SAME list into a `FinKernelState`, each step a sparse `CanonMap.insertNZ`
(the delta value is provably non-default). The finite-map twin of `applyDeltaRec`. -/
def applyDeltaFin : List (CellId × CellDelta) → FinKernelState → FinKernelState
  | [],           f => f
  | (c, d) :: ds, f =>
      applyDeltaFin ds { f with cell := f.cell.insertNZ c (applyCellDelta d (f.cell.get c)) (applyCellDelta_ne_default d (f.cell.get c)) }

/-! ## §2 — THE ONE EFFECT-FREE NATURALITY LEMMA (`denote_applyDelta`).

`denote` intertwines the two folds. It mentions NO effect — only the `insertNZ`↔`Function.update` point-update
bridge (`CanonMap.get_insertNZ`, committed), proved ONCE over the list by induction. This is the shared
machinery; every effect expressed as a delta-list reuses it verbatim. -/

/-- Per-step: a finite `insertNZ` of a delta value denotes to the matching `Function.update`. Effect-free. -/
theorem denote_applyDelta_step (f : FinKernelState) (c : CellId) (d : CellDelta) :
    denote { f with cell := f.cell.insertNZ c (applyCellDelta d (f.cell.get c)) (applyCellDelta_ne_default d (f.cell.get c)) }
      = { denote f with cell := Function.update (denote f).cell c (applyCellDelta d ((denote f).cell c)) } := by
  rw [denote_with_cell]
  refine cell_update_ext f ?_
  funext x
  simp only [CanonMap.get_insertNZ, denote_cell, Function.update_apply]

/-- **`denote_applyDelta` — THE naturality lemma (effect-free).** `denote` commutes the two folds over ANY
delta-list. Induction on the list, using ONLY `denote_applyDelta_step` (hence only the point-update bridge).
Names NO effect. This is the WHOLE recurring machinery the delta architecture bets on. -/
theorem denote_applyDelta (ds : List (CellId × CellDelta)) (f : FinKernelState) :
    denote (applyDeltaFin ds f) = applyDeltaRec ds (denote f) := by
  induction ds generalizing f with
  | nil => rfl
  | cons hd ds ih =>
      obtain ⟨c, d⟩ := hd
      simp only [applyDeltaFin, applyDeltaRec]
      rw [ih, denote_applyDelta_step]

/-! ## §3 — transfer AS DATA (state-independent, mirroring the Rust relative delta). -/

/-- **`transferDelta turn`** — transfer expressed as a relative delta-list: debit `src` by `amt`, credit `dst`
by `amt`. NOTE (a faithfulness win over the prior proto): this needs NO pre-state `k` — the value is computed
at apply time, exactly as Rust's `balance_change` is a relative `i64`, not an absolute overwrite. -/
def transferDelta (turn : Turn) : List (CellId × CellDelta) :=
  [ (turn.src, ⟨-turn.amt⟩), (turn.dst, ⟨turn.amt⟩) ]

/-- Structural `cell`-field ext over a general base (local mirror of the committed `cell_update_ext`, which is
pinned to the `denote f` base; here we need it over an arbitrary `k`). -/
private theorem rec_cell_ext {k : RecordKernelState} {A B : CellId → Value} (h : A = B) :
    ({ k with cell := A } : RecordKernelState) = { k with cell := B } := by rw [h]

/-! ## §4 — MEASURE (a): the ONE-TIME MIGRATION lemma (re-express the deployed op as the fold).

`recKExec_eq_applyDelta` proves the deployed transition equals the delta-fold on its data. This is the
ONE-TIME cost of re-expressing the current nested-`if` op as a delta-fold. Its `by_cases` COUNT is the residue
the prior proto measured — but here it is EXPLICITLY a per-effect migration lemma, proved ONCE, not per turn. -/

/-- The transfer delta-fold reconciled with the deployed nested-`if` op `recTransfer` — **THE per-effect
residue.** MEASURED `by_cases`: **2 per-cell** (`c = src`, `c = dst`). This is exactly the residue
`EffectsAsDataProto` measured, now isolated as a standalone one-time reconciliation lemma. Needs `hne`
(`src ≠ dst`, supplied by the transfer guard): with the delta order `[src, dst]`, reconciling the outer
`Function.update dst` at the `src` cell requires `src ≠ dst`. -/
theorem applyDeltaRec_transfer (turn : Turn) (k : RecordKernelState) (hne : turn.src ≠ turn.dst) :
    applyDeltaRec (transferDelta turn) k
      = { k with cell := recTransfer k.cell turn.src turn.dst turn.amt } := by
  refine rec_cell_ext ?_
  funext c
  unfold recTransfer
  by_cases h1 : c = turn.src
  · subst h1
    simp [applyCellDelta, hne, sub_eq_add_neg]
  · by_cases h2 : c = turn.dst
    · subst h2
      simp [applyCellDelta, h1]
    · simp [applyCellDelta, Function.update_apply, h1, h2]

/-- **MIGRATION lemma (step 4).** A committed `recKExec` equals the transfer delta-fold on the pre-state.
The per-cell `by_cases` residue (2) lives in `applyDeltaRec_transfer` above; this lemma adds ONLY the structural
guard split (`by_cases hg`, present in EVERY executable op — not a per-cell residue) to extract `src ≠ dst` and
the post-state shape. This is the ONE-TIME cost of re-expressing the deployed op as a delta-fold, proved ONCE,
not per turn. -/
theorem recKExec_eq_applyDelta {k k' : RecordKernelState} {turn : Turn}
    (h : recKExec k turn = some k') :
    k' = applyDeltaRec (transferDelta turn) k := by
  have hguard := h
  unfold recKExec at hguard
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · obtain ⟨_, _, _, hne, _, _⟩ := hg
    rw [recKExec_shape h]
    exact (applyDeltaRec_transfer turn k hne).symm
  · rw [if_neg hg] at hguard
    exact absurd hguard (by simp)

/-! ## §5 — MEASURE (b): the RECURRING square (per turn), using ONLY §2 + §4.

`finTransferDelta` is the finite step whose action is the delta-fold. The recurring commuting square is proved
with the shared `denote_applyDelta` (§2) and the migration lemma (§4) — NO per-cell `by_cases` in its body. -/

/-- The finite transfer done as a delta-fold: on the SAME admissibility (evaluated on `denote f`), apply
`transferDelta turn` via `applyDeltaFin`; identity on reject. -/
def finTransferDelta (turn : Turn) (f : FinKernelState) : FinKernelState :=
  match recKExec (denote f) turn with
  | some _ => applyDeltaFin (transferDelta turn) f
  | none   => f

/-- **RECURRING square (step 5).** `denote (finTransferDelta turn f) = (recKExec (denote f) turn).getD …`.
MEASURED `by_cases`: **ZERO** in the body. The only case-split is `cases h : recKExec …` — the none/some GUARD
match (structural, every effect has it), NOT a per-cell `by_cases`. The per-cell residue is entirely absent:
it was paid ONCE in §4. Proof body (quoted in the report): `unfold`; `cases` the guard; `some` arm is
`rw [denote_applyDelta]; exact (recKExec_eq_applyDelta h).symm`. -/
theorem finTransferDelta_denote (turn : Turn) (f : FinKernelState) :
    denote (finTransferDelta turn f) = (recKExec (denote f) turn).getD (denote f) := by
  unfold finTransferDelta
  cases h : recKExec (denote f) turn with
  | none => simp only [Option.getD_none]
  | some k' =>
      simp only [Option.getD_some]
      show denote (applyDeltaFin (transferDelta turn) f) = k'
      rw [denote_applyDelta]
      exact (recKExec_eq_applyDelta h).symm

/-! ## §6 — MEASURE (c'): what §4 costs IF the deployed op is DEFINED as the fold (step-4 becomes `rfl`-ish).

`recKExecDelta` is the hypothetical deployed op with the SAME guard but whose post-state IS `applyDeltaRec
(transferDelta turn) k` — i.e. the delta-fold is the deployment, not a nested-`if`. Its migration-analog
carries **ZERO per-cell `by_cases`** (only the structural guard split, which every op has): the reconciliation
`k' = applyDeltaRec …` is the definitional post-state. This is the measured proof that the §4 residue is a
ONE-TIME cost that VANISHES under redefinition — it does not recur. -/

/-- The deployed transition REDEFINED as the delta-fold (same fail-closed guard). -/
def recKExecDelta (k : RecordKernelState) (turn : Turn) : Option RecordKernelState :=
  if authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts then
    some (applyDeltaRec (transferDelta turn) k)
  else
    none

/-- **Migration-analog under redefinition — ZERO per-cell `by_cases`.** With the op DEFINED as the fold, the
post-state IS the fold: the reconciliation is the guard-only case-split (`by_cases hg`, structural), no
`funext`, no `c = src / c = dst`. Contrast §4's 2 per-cell `by_cases`. This is the measured "step-4 becomes
`rfl`" claim of DELTA-FUTURE, made concrete. -/
theorem recKExecDelta_eq_applyDelta {k k' : RecordKernelState} {turn : Turn}
    (h : recKExecDelta k turn = some k') :
    k' = applyDeltaRec (transferDelta turn) k := by
  unfold recKExecDelta at h
  by_cases hg : authorizedB k.caps turn = true ∧ 0 ≤ turn.amt ∧ turn.amt ≤ balOf (k.cell turn.src)
      ∧ turn.src ≠ turn.dst ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts
  · rw [if_pos hg] at h
    simp only [Option.some.injEq] at h
    exact h.symm
  · rw [if_neg hg] at h
    exact absurd h (by simp)

/-- And the recurring square against the REDEFINED op is the SAME shape as §5, now with §4-analog free. -/
theorem finTransferDelta_denote_redef (turn : Turn) (f : FinKernelState)
    (hdef : ∀ g : FinKernelState, recKExec (denote g) turn = recKExecDelta (denote g) turn) :
    denote (finTransferDelta turn f) = (recKExecDelta (denote f) turn).getD (denote f) := by
  rw [← hdef f]
  exact finTransferDelta_denote turn f

/-! ## §7 — TEETH (`#guard`): the delta-derived square agrees with the deployed step, concretely. -/

section Teeth

private def fT : FinKernelState :=
  { finInit with
    accounts := {0, 1}
    cell := (CanonMap.empty.insertNZ 0 (Value.record [("balance", Value.int 100)]) (by simp)).insertNZ 1
              (Value.record [("balance", Value.int 5)]) (by simp) }

private def tT : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- the DELTA-derived transfer commits to the right balances (70 / 35):
#guard balOf ((denote (finTransferDelta tT fT)).cell 0) == 70
#guard balOf ((denote (finTransferDelta tT fT)).cell 1) == 35
-- and the relative-delta fold applied on the record side agrees at each touched cell:
#guard balOf ((applyDeltaRec (transferDelta tT) (denote fT)).cell 0) == 70
#guard balOf ((applyDeltaRec (transferDelta tT) (denote fT)).cell 1) == 35
-- the untouched cell would be preserved (here there is none besides 0/1; sanity: an absent cell reads default):
#guard balOf ((applyDeltaRec (transferDelta tT) (denote fT)).cell 2) == 0
-- transferDelta is STATE-INDEPENDENT data: same list regardless of the state it is read against:
#guard (transferDelta tT).length == 2

end Teeth

/-! ## §8 — THE VERDICT (measured).

Q1 — does the per-effect `by_cases` become ZERO in the RECURRING square (§5)? **YES.** `finTransferDelta_denote`
has zero per-cell `by_cases`; its only split is the none/some guard match (structural). The recurring per-turn
cost is `denote_applyDelta` (SHARED, effect-free, proved once for ALL effects) + one rewrite + `.symm`.

Q2 — is §4's `by_cases` a ONE-TIME-PER-EFFECT migration cost that VANISHES if the op is redefined as the fold?
**YES.** §4 (`recKExec_eq_applyDelta`) carries 2 per-cell `by_cases` against the CURRENT nested-`if` op. §6
(`recKExecDelta_eq_applyDelta`) shows that the moment the op is DEFINED as `applyDeltaRec (transferDelta turn)`,
the analog has 0 per-cell `by_cases` (guard split only). So the residue does NOT recur: it is either a
one-time reconciliation lemma per effect (keep the nested-`if` op) OR it disappears entirely (redefine).

Q3 — cheaper end-to-end than 28× the per-effect proof? The recurring square is now effect-INDEPENDENT (one
`denote_applyDelta`), so the ~28 remaining effects pay only: (i) a small per-effect delta-footprint definition,
(ii) a one-time migration lemma sized by touched cells/fields IF the nested-`if` ops are kept — OR zero if the
ops are redefined. The redefinition, however, is a large ONE-TIME blast: 149 files mention
`recTransfer`/`recKExec`/`recCreditCell`, and ~119 proof sites actively `unfold`/`simp` them (would need
re-checking). So: delta-refactor is CHEAPER for the RECURRING R3 cluster (a real win — one naturality lemma
replaces per-effect denotation tails), but the ONE-TIME migration is NOT free — it is either 28 small
reconciliation lemmas (nested-`if` kept) or a 119-proof-site redefinition ripple (op redefined).

Contrast with `EffectsAsDataProto` ("NO — it relocates"): that verdict was correct but measured only the
current op and did not separate the one-time reconciliation from the recurring square. Separated here: the
RECURRING cost is genuinely `by_cases`-free; the RESIDUE is one-time and either bounded-per-effect or
vanishing. Net recommendation (measured, not asserted): the delta model is worth adopting for R3-continuation
IF the deployed ops are redefined as folds in the same motion (paying the 119-site ripple once), because that
buys both faithfulness (the Lean op then structurally mirrors `apply_cell_delta`) and a `by_cases`-free
per-effect square. Keeping the nested-`if` ops and only adding delta wrappers buys the shared naturality lemma
but leaves a (one-time, small) reconciliation per effect — still cheaper than 28× the full per-effect tail. -/

end Dregg2.Circuit.DeltaProto
