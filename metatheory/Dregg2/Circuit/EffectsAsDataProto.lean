/-
# Dregg2.Circuit.EffectsAsDataProto — DE-RISK PROTOTYPE (effects-as-data).

QUESTION under test: can each effect's finite/abstract commuting square (`finXxx_denote`, currently a
per-effect `by_cases <which cells>` tail) be made to FALL OUT of ONE shared naturality lemma by expressing
the effect's action as DATA (an update-list), so the per-effect `by_cases` residue VANISHES?

We build it for TWO effects — transfer + mint — reusing the COMMITTED R3 code
(`Circuit/FinKernelStep.lean`, `Exec/RecordKernel.lean`, `Exec/TurnExecutorFull.lean`) verbatim; NOTHING
committed is edited. The VERDICT (a measured yes/no, not a framework) is recorded at the end (§6).

RESULT PREVIEW (honest): **NO — the per-effect `by_cases` does NOT vanish; it RELOCATES.** The shared
naturality lemma `denote_applyUpdates` (§2) genuinely IS effect-free and dissolves the
`CanonMap`↔`Function.update` DENOTATION bridge (`get_insertNZ`/`denote_cell`) — proved ONCE, reused by both
effects. But the deployed abstract ops `recTransfer`/`recCreditCell` are written as nested `if c = src / c =
dst` guards, so reconciling the point-update FOLD (`applyUpdatesRec`) with them
(`applyUpdatesRec_transfer`/`_mint`, §4) still costs exactly one `by_cases` per TOUCHED cell. That residue is
irreducible against the committed ops: it is the semantic content "this effect touches exactly these cells."
-/
import Dregg2.Circuit.FinKernelStep
import Mathlib.Logic.Function.Basic

namespace Dregg2.Circuit.FinKernelState

open Dregg2.Exec Dregg2.Authority
open Dregg2.Exec.TurnExecutorFull (recKMint recCreditCell)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the update as DATA.

An update is a per-cell overwrite of the `cell` field to a NEW `Value` computed from the pre-state. We must
carry the proof `val ≠ default` INSIDE the datum: the finite side writes with `CanonMap.insertNZ`, whose
non-default proof obligation cannot be discharged by `DecidableEq Value` (there is none in-tree) — so the
proof rides along as a (proof-irrelevant) field. This is still DATA: a `List CellUpdate`. -/

/-- A single cell overwrite: set cell `key`'s record to `val` (proven non-default so `insertNZ` accepts it). -/
structure CellUpdate where
  /-- the cell whose record is overwritten. -/
  key : CellId
  /-- the NEW record value (computed from the pre-state). -/
  val : Value
  /-- `val` is not the field default — the sparse-map obligation `insertNZ` needs (proof-irrelevant).
  The `cell` map's default is `Value.int 0` (`FinKernelState.cell : CanonMap CellId Value (Value.int 0)`). -/
  ne  : val ≠ Value.int 0

/-- **`applyUpdatesFin`** — fold the update-list into a `FinKernelState`, each step a `CanonMap.insertNZ`. -/
def applyUpdatesFin : List CellUpdate → FinKernelState → FinKernelState
  | [],      f => f
  | u :: us, f => applyUpdatesFin us { f with cell := f.cell.insertNZ u.key u.val u.ne }

/-- **`applyUpdatesRec`** — fold the SAME update-list into a `RecordKernelState`, each step a
`Function.update` on the `cell` total function. -/
def applyUpdatesRec : List CellUpdate → RecordKernelState → RecordKernelState
  | [],      k => k
  | u :: us, k => applyUpdatesRec us { k with cell := Function.update k.cell u.key u.val }

/-! ## §2 — THE ONE NATURALITY LEMMA (effect-free).

`denote` intertwines the two folds: NO effect is mentioned, only the `insertNZ`↔`Function.update` point-update
bridge (`get_insertNZ`, `denote_cell`, `denote_with_cell`) — proved ONCE, over the update-list by induction. -/

/-- Per-step: a finite `insertNZ` write denotes to a `Function.update` on the record `cell`. Effect-free —
this is the whole DENOTATION content, and it names no effect. -/
theorem denote_insertNZ_step (f : FinKernelState) (u : CellUpdate) :
    denote { f with cell := f.cell.insertNZ u.key u.val u.ne }
      = { denote f with cell := Function.update (denote f).cell u.key u.val } := by
  rw [denote_with_cell]
  refine cell_update_ext f ?_
  funext c
  simp only [CanonMap.get_insertNZ, denote_cell, Function.update_apply]

/-- **`denote_applyUpdates` — THE naturality lemma.** `denote` commutes the two folds over ANY update-list.
Proved by induction on the list using ONLY `denote_insertNZ_step` (hence only the point-update bridge). It
mentions NO effect — transfer, mint, or otherwise. This is the shared machinery the experiment bets on. -/
theorem denote_applyUpdates (us : List CellUpdate) (f : FinKernelState) :
    denote (applyUpdatesFin us f) = applyUpdatesRec us (denote f) := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
      simp only [applyUpdatesFin, applyUpdatesRec]
      rw [ih, denote_insertNZ_step]

/-! ## §3 — the effects AS DATA (transfer + mint), computed from the pre-state via the SAME abstract logic. -/

/-- Transfer as DATA: overwrite `dst` (credited) then `src` (debited), each value the SAME
`setBalance … (balOf … ± amt)` the deployed `recTransfer` computes, read off the pre-state `k`. -/
def transferUpdates (turn : Turn) (k : RecordKernelState) : List CellUpdate :=
  [ { key := turn.dst
      val := setBalance (k.cell turn.dst) (balOf (k.cell turn.dst) + turn.amt)
      ne  := setBalance_ne_default _ _ },
    { key := turn.src
      val := setBalance (k.cell turn.src) (balOf (k.cell turn.src) - turn.amt)
      ne  := setBalance_ne_default _ _ } ]

/-- Mint as DATA: overwrite `cell` (credited), the value the deployed `recCreditCell` computes. -/
def mintUpdates (cell : CellId) (amt : ℤ) (k : RecordKernelState) : List CellUpdate :=
  [ { key := cell
      val := setBalance (k.cell cell) (balOf (k.cell cell) + amt)
      ne  := setBalance_ne_default _ _ } ]

/-! ## §4 — reconciling the FOLD with the deployed abstract ops.

Here is where the per-effect `by_cases` LANDS. `applyUpdatesRec (transferUpdates …)` is a fold of
`Function.update`s; the deployed `recTransfer`/`recCreditCell` are nested `if c = src / c = dst` guards. Proving
them equal is exactly `funext c` + one `by_cases` per touched cell — the SAME residue the original
`finTransfer_denote`/`finMint_denote` carried, just moved one lemma over. It is IRREDUCIBLE against the
committed ops (we may not redefine `recTransfer`). -/

/-- Overwrite-only structural ext for the `cell` field over a general base (mirror of `cell_update_ext`). -/
private theorem rec_cell_ext {k : RecordKernelState} {A B : CellId → Value} (h : A = B) :
    ({ k with cell := A } : RecordKernelState) = { k with cell := B } := by rw [h]

/-- The transfer fold equals the deployed `recTransfer` — **the surviving per-effect `by_cases` (2 cells).**
`rec_cell_ext` unifies the fold (`applyUpdatesRec [dst,src] k`, defeq to a `cell`-only overwrite of `k`) with
`{ k with cell := … }`; the residue is the `funext c` + `by_cases c = src / c = dst`. -/
theorem applyUpdatesRec_transfer (turn : Turn) (k : RecordKernelState) :
    applyUpdatesRec (transferUpdates turn k) k
      = { k with cell := recTransfer k.cell turn.src turn.dst turn.amt } := by
  refine rec_cell_ext ?_
  funext c
  unfold recTransfer
  by_cases h1 : c = turn.src
  · subst h1; simp
  · by_cases h2 : c = turn.dst
    · subst h2; simp [h1]
    · simp [h1, h2]

/-- The mint fold equals the deployed `recCreditCell` — **the surviving per-effect `by_cases` (1 cell).** -/
theorem applyUpdatesRec_mint (cell : CellId) (amt : ℤ) (k : RecordKernelState) :
    applyUpdatesRec (mintUpdates cell amt k) k
      = { k with cell := recCreditCell k.cell cell amt } := by
  refine rec_cell_ext ?_
  funext c
  unfold recCreditCell
  by_cases h1 : c = cell
  · subst h1; simp
  · simp [h1]

/-! ## §5 — THE PAYOFF: `finTransfer_denote`/`finMint_denote` re-derived via the shared naturality lemma.

The per-effect tail is now: `denote_applyUpdates` (SHARED, effect-free) ∘ `applyUpdatesRec_transfer/_mint`
(the RELOCATED residue) ∘ `recKExec_shape`/`recKMint_shape`. Compare each proof body against the committed
original in `FinKernelStep.lean` (§7 there): the `CanonMap` bridge tail is GONE, but the effect still routes
through its own `applyUpdatesRec_*` reconciliation lemma, which carries the `by_cases`. -/

/-- Transfer commutes — re-derived. (Committed original had a `funext c; simp only [bridge]; unfold recTransfer;
by_cases c=src; by_cases c=dst` TAIL; here that tail lives in `applyUpdatesRec_transfer`.) -/
theorem finTransfer_denote' (turn : Turn) (f : FinKernelState) :
    denote (finTransfer turn f) = (recKExec (denote f) turn).getD (denote f) := by
  unfold finTransfer
  cases h : recKExec (denote f) turn with
  | none => simp only [Option.getD_none]
  | some k' =>
      simp only [Option.getD_some]
      show denote (applyUpdatesFin (transferUpdates turn (denote f)) f) = k'
      rw [denote_applyUpdates, applyUpdatesRec_transfer, recKExec_shape h]

/-- Mint commutes — re-derived. (Committed original had a `funext c; simp only [bridge]; unfold recCreditCell;
by_cases c=cell` TAIL; here that tail lives in `applyUpdatesRec_mint`.) -/
theorem finMint_denote' (actor cell : CellId) (amt : ℤ) (f : FinKernelState) :
    denote (finMint actor cell amt f) = (recKMint (denote f) actor cell amt).getD (denote f) := by
  unfold finMint
  cases h : recKMint (denote f) actor cell amt with
  | none => simp only [Option.getD_none]
  | some k' =>
      simp only [Option.getD_some]
      show denote (applyUpdatesFin (mintUpdates cell amt (denote f)) f) = k'
      rw [denote_applyUpdates, applyUpdatesRec_mint, recKMint_shape h]

/-! ## §6 — THE VERDICT (measured).

**Did the per-effect `by_cases <which cells>` vanish for BOTH effects? NO.**

* WHAT DISSOLVED (the real win): the `CanonMap`↔`Function.update` DENOTATION bridge. In the committed proofs,
  every effect's tail repeated `simp only [CanonMap.get_insertNZ, denote_cell, …]` to push `denote` through the
  map writes. Here that content is proved ONCE in the effect-FREE `denote_applyUpdates` (§2) and reused by
  both `finTransfer_denote'` and `finMint_denote'`. Their bodies no longer mention `get_insertNZ` at all.

* WHAT SURVIVED (the residue, relocated not removed): the `by_cases c = src / c = dst / c = cell`. It moved
  out of `finXxx_denote'` and INTO `applyUpdatesRec_transfer` / `applyUpdatesRec_mint` (§4), which reconcile
  the point-update FOLD with the deployed nested-`if` ops `recTransfer` / `recCreditCell`. The count is exactly
  the number of cells the effect touches (transfer 2, mint 1) — identical to the original.

* WHY it is irreducible: the residue IS the equation `fold-of-updates = recTransfer` where `recTransfer` is a
  COMMITTED op written as `fun c => if c = src then … else if c = dst then … else cell c`. Only by REDEFINING
  the deployed op as `applyUpdatesRec (transferUpdates …)` could the `by_cases` disappear — and that would be
  moving the deployment, not dissolving the proof. Per HONEST-VERDICT discipline this counts as SURVIVED: the
  `by_cases` lives in a per-effect helper (`applyUpdatesRec_*`) that itself does the `by_cases`.

So effects-as-data does NOT collapse the 33-effect cluster to "data + one lemma." It DOES factor the shared
half (the denotation bridge) into one reusable lemma, leaving each effect a small `applyUpdatesRec_<eff> =
<deployed-op>` reconciliation (a `funext` + `by_cases`-per-touched-cell). Net for the remaining ~31 effects and
the RestFrameDecodes2*/DeployedFaithful* families: the win is a UNIFORM denotation tail (delete the repeated
`simp only [bridge]`), NOT elimination of per-effect case analysis — each effect keeps a reconciliation lemma
whose size tracks how many cells/fields it writes. (Effects touching `caps`/`bal`/other fields would need a
per-FIELD `applyUpdates*` + naturality instance, since `CellUpdate` here is `cell`-only.) -/

/-! ## §7 — TEETH (`#guard`): the re-derived squares agree with the deployed step, concretely. -/

section Teeth

private def fT : FinKernelState :=
  { finInit with
    accounts := {0, 1}
    cell := (CanonMap.empty.insertNZ 0 (Value.record [("balance", Value.int 100)]) (by simp)).insertNZ 1
              (Value.record [("balance", Value.int 5)]) (by simp) }

private def tT : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- the DATA-derived transfer commits to the right balances (70 / 35):
#guard balOf ((denote (finTransfer tT fT)).cell 0) == 70
#guard balOf ((denote (finTransfer tT fT)).cell 1) == 35
-- and the update-list applied on the record side agrees at each touched cell:
#guard balOf ((applyUpdatesRec (transferUpdates tT (denote fT)) (denote fT)).cell 0) == 70
#guard balOf ((applyUpdatesRec (transferUpdates tT (denote fT)) (denote fT)).cell 1) == 35
-- mint credits the single cell:
#guard balOf ((applyUpdatesRec (mintUpdates 0 50 (denote fT)) (denote fT)).cell 0) == 150

end Teeth

end Dregg2.Circuit.FinKernelState
