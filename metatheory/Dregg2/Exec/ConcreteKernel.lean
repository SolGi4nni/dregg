/-
# Dregg2.Exec.ConcreteKernel — the l4v-style DATA-REFINEMENT layer.

`Exec/RecordKernel.lean` is the verified ABSTRACT spec. Its hot fields are FUNCTION-based —
`cell : CellId → Value`, `bal : CellId → AssetId → ℤ`, `accounts : Finset CellId`, and the
nullifier/revoked/commitment SETS as `List Nat`. That representation is PROOF-FRIENDLY (every
soundness lemma lives there: `recTransfer_balanceSum_conserve`, `recKExecAsset_conserves_per_asset`,
`recKExec_frame`, …) but it is NOT node-grade: a function-update is a closure (`fun c => if … then …`),
so a long turn-stream grows an unbounded closure chain and every read walks it — O(n)/op.

This module is the **data refinement** (the core l4v property the maintainer was preserving): a
CONCRETE state `ConcreteKernelState` mirroring `RecordKernelState` but with EFFICIENT persistent
structures — `Std.HashMap CellId Value` for `cell`, `Std.HashMap (CellId × AssetId) ℤ` for `bal`,
`Std.HashSet Nat` for the nullifier/revoked/commitment sets — plus a `toAbstract` refinement map and
CONCRETE operations whose ABSTRACTION equals the abstract op (the COMMUTING SQUARE). The whole point:
an abstract theorem about `recTransfer`/`writeField` transfers to its concrete corollary PURELY from
the square — the abstract reasoning is never redone. We validate that on the two hot paths the prompt
names: **transfer** (`concreteTransfer` ⟹ `recTransfer`) and **setField** (`concreteWriteField` ⟹
`writeField`), then DERIVE the concrete conservation corollary from the abstract keystone + the square.

`CellId = Label = Nat` carries `LawfulBEq` + `LawfulHashable`, so `Std.HashMap.getD_insert`'s
`if k == a then …` collapses to the abstract `if c = src then …` cleanly — the representation does NOT
fight the refinement. Real squares, real transfer.

Imports `Exec.RecordKernel` (the abstract spec) and `Exec.EffectsState` (for `setField`/`writeField`).
-/
import Dregg2.Exec.RecordKernel
import Dregg2.Exec.EffectsState
import Std.Data.HashMap
import Std.Data.HashSet

namespace Dregg2.Exec

open Dregg2.Authority Dregg2.Execution
open Dregg2.Exec.EffectsState (setField fieldOf writeField setField_balOf setField_fieldOf)
open scoped BigOperators

-- Make `RecordKernelState` extensional so a square that touches ONLY the `cell` field discharges the
-- other ~17 fields by `rfl` (they ride through `toAbstract` / `{ … with … }` unchanged).
attribute [ext] RecordKernelState

/-! ## §1 — The CONCRETE efficient state.

We mirror `RecordKernelState`'s hot fields with persistent maps/sets and KEEP the cold side-tables
(escrows/queues/swiss/factories/lifecycle/…) exactly as the abstract spec carries them, so the
refinement focuses the hot path. `accounts` is kept as an explicit `Finset CellId` (NOT recovered as
`cellMap.keys.toFinset`) — that deliberately sidesteps the `Finset`-vs-map-keys obstruction: the
membership gate reads it directly, and abstraction is the IDENTITY on it. -/

/-- **`ConcreteKernelState`** — the node-grade twin of `RecordKernelState`. The hot per-cell state is
a `Std.HashMap CellId Value` (O(1)-ish lookup/update, no closure growth); the per-asset ledger is a
`Std.HashMap (CellId × AssetId) ℤ`; the nullifier/revoked/commitment SETS are `Std.HashSet Nat`. The
account set + cap table + all cold side-tables ride along unchanged so the refinement square is local
to the hot path. -/
structure ConcreteKernelState where
  /-- Live cells (kept explicit — abstraction is the identity, dodging the map-keys/Finset friction). -/
  accounts    : Finset CellId
  /-- The efficient per-cell record store — replaces `cell : CellId → Value`. -/
  cellMap     : Std.HashMap CellId Value
  /-- The capability table (identical to the abstract spec — authority is rep-independent). -/
  caps        : Caps
  /-- The efficient per-asset ledger — replaces `bal : CellId → AssetId → ℤ`. -/
  balMap      : Std.HashMap (CellId × AssetId) ℤ
  /-- Efficient nullifier set — replaces `nullifiers : List Nat`. -/
  nullifiers  : Std.HashSet Nat := ∅
  /-- Efficient revocation registry — replaces `revoked : List Nat`. -/
  revoked     : Std.HashSet Nat := ∅
  /-- Efficient commitment set — replaces `commitments : List Nat`. -/
  commitments : Std.HashSet Nat := ∅
  -- Cold side-tables, carried verbatim from the abstract spec (not the refinement focus):
  escrows     : List EscrowRecord := []
  queues      : List QueueRecord := []
  swiss       : List SwissRecord := []
  factories   : List (Nat × FactoryEntry) := []
  sealedBoxes : List SealedBoxRecord := []
  slotCaveats : CellId → List SlotCaveat := fun _ => []
  lifecycle   : CellId → Nat := fun _ => 0
  deathCert   : CellId → Nat := fun _ => 0
  delegate    : CellId → Option CellId := fun _ => none
  delegations : CellId → List Cap := fun _ => []

/-! ## §2 — The REFINEMENT MAP `toAbstract`.

Each concrete map becomes its lookup FUNCTION (`getD … default`), each concrete set its `List` view
(membership-equivalent), and `accounts`/`caps`/cold-tables ride as the identity. This is the l4v
abstraction relation, here a total FUNCTION (a deterministic refinement), which is exactly what makes
the commuting square an EQUATION rather than a relation. -/

/-- The l4v abstraction: read each efficient structure back into the abstract spec's function/`List`
representation. `cell := fun c => cellMap.getD c default`, `bal := fun c a => balMap.getD (c,a) 0`, and
the sets become their key-lists. -/
def toAbstract (cs : ConcreteKernelState) : RecordKernelState where
  accounts    := cs.accounts
  cell        := fun c => cs.cellMap.getD c default
  caps        := cs.caps
  bal         := fun c a => cs.balMap.getD (c, a) 0
  nullifiers  := cs.nullifiers.toList
  revoked     := cs.revoked.toList
  commitments := cs.commitments.toList
  escrows     := cs.escrows
  queues      := cs.queues
  swiss       := cs.swiss
  factories   := cs.factories
  sealedBoxes := cs.sealedBoxes
  slotCaveats := cs.slotCaveats
  lifecycle   := cs.lifecycle
  deathCert   := cs.deathCert
  delegate    := cs.delegate
  delegations := cs.delegations

/-- Reading the abstract `cell` of `toAbstract cs` at `c` is exactly the concrete map lookup. The
definitional bridge the squares rewrite by. -/
@[simp] theorem toAbstract_cell (cs : ConcreteKernelState) (c : CellId) :
    (toAbstract cs).cell c = cs.cellMap.getD c default := rfl

@[simp] theorem toAbstract_bal (cs : ConcreteKernelState) (c : CellId) (a : AssetId) :
    (toAbstract cs).bal c a = cs.balMap.getD (c, a) 0 := rfl

@[simp] theorem toAbstract_accounts (cs : ConcreteKernelState) :
    (toAbstract cs).accounts = cs.accounts := rfl

@[simp] theorem toAbstract_caps (cs : ConcreteKernelState) :
    (toAbstract cs).caps = cs.caps := rfl

/-! ## §3 — The CONCRETE operations over the efficient maps.

`concreteTransfer` debits `src` and credits `dst` in `cellMap` with two `insert`s (O(1)-ish each);
`concreteWriteField` writes one field of one cell with a single `insert`. NO closure growth — a long
turn-stream stays flat. -/

/-- The concrete transfer: read `src`/`dst`'s current records, rewrite their `balance` fields, and
INSERT the two updated records back. Two HashMap inserts — the node-grade twin of `recTransfer`'s
function-update (which would chain two closures). -/
def concreteTransfer (cs : ConcreteKernelState) (src dst : CellId) (amt : ℤ) :
    ConcreteKernelState :=
  let oldSrc := cs.cellMap.getD src default
  let oldDst := cs.cellMap.getD dst default
  { cs with
    cellMap := (cs.cellMap.insert src (setBalance oldSrc (balOf oldSrc - amt))).insert dst
                 (setBalance oldDst (balOf oldDst + amt)) }

/-- The concrete field write: read `target`'s current record, write field `f`, INSERT it back. One
HashMap insert — the node-grade twin of `writeField`'s function-update. -/
def concreteWriteField (cs : ConcreteKernelState) (f : FieldName) (target : CellId) (v : Value) :
    ConcreteKernelState :=
  { cs with cellMap := cs.cellMap.insert target (setField f (cs.cellMap.getD target default) v) }

/-! ## §4 — THE COMMUTING SQUARES (the refinement proofs).

`toAbstract (concreteOp cs …) = abstractOp (toAbstract cs) …`. Both sides are `RecordKernelState`s; we
peel to the only changed field (`cell`) and prove the two lookup-functions agree pointwise via `funext`
+ `Std.HashMap.getD_insert`, whose `if k == a` collapses to the abstract `if c = src` because
`CellId = Nat` is `LawfulBEq`. -/

/-- **THE TRANSFER SQUARE — PROVED.** Abstracting the concrete transfer equals the abstract transfer.
This is the heart of the refinement: the efficient two-insert update, read back through `toAbstract`,
is LITERALLY the abstract `recTransfer` function — so every abstract fact about `recTransfer` holds of
the concrete op verbatim. -/
theorem toAbstract_concreteTransfer (cs : ConcreteKernelState) (src dst : CellId) (amt : ℤ)
    (hne : src ≠ dst) :
    toAbstract (concreteTransfer cs src dst amt)
      = { (toAbstract cs) with
          cell := recTransfer (toAbstract cs).cell src dst amt } := by
  unfold concreteTransfer toAbstract
  -- only the `cell` field differs; reduce to the underlying functions.
  ext c
  all_goals try rfl
  simp only []
  -- expand both inserts' lookup at `c`, then the abstract `recTransfer` at `c`.
  rw [Std.HashMap.getD_insert, Std.HashMap.getD_insert]
  unfold recTransfer
  -- `c == dst` / `c == src` collapse to `c = dst` / `c = src` (Nat is LawfulBEq);
  -- the abstract uses `if c = src … else if c = dst …`, the concrete (insert-order) is
  -- `if dst == c … else if src == c …` — reconcile via the disjointness `src ≠ dst`.
  by_cases hsrc : c = src
  · subst hsrc
    have hcd : (dst == c) = false := by
      simpa [beq_eq_false_iff_ne] using (Ne.symm hne)
    rw [hcd, beq_self_eq_true]
    simp only [Bool.false_eq_true, if_false, if_true, if_neg hne]
  · by_cases hdst : c = dst
    · subst hdst
      rw [beq_self_eq_true]
      simp only [if_true, if_neg hsrc]
    · have h1 : (dst == c) = false := by simpa [beq_eq_false_iff_ne] using (Ne.symm hdst)
      have h2 : (src == c) = false := by simpa [beq_eq_false_iff_ne] using (Ne.symm hsrc)
      rw [h1, h2]
      simp only [Bool.false_eq_true, if_false, if_neg hsrc, if_neg hdst]

/-- **THE SETFIELD SQUARE — PROVED.** Abstracting the concrete field write equals the abstract
`writeField`. The setField hot path refines exactly as cleanly as transfer. -/
theorem toAbstract_concreteWriteField (cs : ConcreteKernelState) (f : FieldName)
    (target : CellId) (v : Value) :
    toAbstract (concreteWriteField cs f target v)
      = writeField (toAbstract cs) f target v := by
  unfold concreteWriteField writeField toAbstract
  ext c
  all_goals try rfl
  simp only []
  rw [Std.HashMap.getD_insert]
  by_cases h : c = target
  · subst h; rw [beq_self_eq_true]; simp only [if_true]
  · have hb : (target == c) = false := by simpa [beq_eq_false_iff_ne] using (Ne.symm h)
    rw [hb]; simp only [Bool.false_eq_true, if_false, if_neg h]

/-! ## §5 — PROOF TRANSFER: the concrete corollary FALLS OUT of the square + the abstract keystone.

This is the deliverable l4v property. We do NOT redo conservation reasoning over HashMaps — we
INVOKE the abstract `recTransfer_balanceSum_conserve` and merely REWRITE along the commuting square.
The concrete state's abstracted balance-total is conserved purely because (a) abstraction commutes
with the op, and (b) the abstract op conserves. The hard math stays in the abstract layer, untouched. -/

/-- The conserved measure read off the CONCRETE state (its abstraction's balance total). -/
def concreteTotal (cs : ConcreteKernelState) : ℤ := recTotal (toAbstract cs)

/-- **PROOF TRANSFER — the concrete conservation corollary, PROVED FROM THE SQUARE.** A concrete
transfer between two distinct live accounts conserves the (abstracted) total balance. Notice the
proof body: it `rw`s the commuting square `toAbstract_concreteTransfer` and then hands the goal to the
abstract keystone `recTransfer_balanceSum_conserve` — ZERO new reasoning about HashMaps or conservation.
THIS is what "proofs transfer" means: the abstract theorem is the only mathematics; the square does the
rest. -/
theorem concreteTransfer_conserves (cs : ConcreteKernelState) (src dst : CellId) (amt : ℤ)
    (hsrc : src ∈ cs.accounts) (hdst : dst ∈ cs.accounts) (hne : src ≠ dst) :
    concreteTotal (concreteTransfer cs src dst amt) = concreteTotal cs := by
  unfold concreteTotal recTotal
  -- abstraction of the concrete op = the abstract op (the SQUARE).
  rw [toAbstract_concreteTransfer cs src dst amt hne]
  -- now it is LITERALLY the abstract conservation statement; invoke the abstract keystone.
  show (∑ c ∈ (toAbstract cs).accounts,
          balOf (recTransfer (toAbstract cs).cell src dst amt c))
        = ∑ c ∈ (toAbstract cs).accounts, balOf ((toAbstract cs).cell c)
  exact recTransfer_balanceSum_conserve (toAbstract cs).accounts (toAbstract cs).cell
    src dst amt hsrc hdst hne

/-- **PROOF TRANSFER (setField frame), PROVED FROM THE SQUARE.** A concrete field write to a field
`f ≠ balance` leaves the (abstracted) total balance UNCHANGED — derived from the square +
`EffectsState.setField_balOf` (the abstract non-interference keystone), with no HashMap reasoning. -/
theorem concreteWriteField_balOf_unchanged (cs : ConcreteKernelState) (f : FieldName)
    (target : CellId) (v : Value) (hf : f ≠ balanceField) (c : CellId) :
    balOf ((toAbstract (concreteWriteField cs f target v)).cell c)
      = balOf ((toAbstract cs).cell c) := by
  rw [toAbstract_concreteWriteField]
  -- now purely the abstract `writeField`; reuse the abstract non-interference lemma.
  unfold writeField
  simp only []
  by_cases h : c = target
  · subst h; rw [if_pos rfl]; exact setField_balOf f _ v hf
  · rw [if_neg h]

/-! ## §6 — EFFICIENCY SHAPE: O(1)-ish concrete lookups/updates (the win is real).

These `#guard`s confirm the concrete ops are persistent-map ops (insert/lookup) — not closure growth.
A function-update spec, after N transfers, reads through an N-deep closure chain; the concrete state
reads through ONE HashMap probe regardless of N. -/

/-- A starter concrete state: cells 0 and 1, each a `balance`-record. -/
def demoCS : ConcreteKernelState where
  accounts := {0, 1}
  cellMap  := (∅ : Std.HashMap CellId Value).insert 0 (.record [(balanceField, .int 100)])
                |>.insert 1 (.record [(balanceField, .int 5)])
  caps     := default
  balMap   := ∅

-- After transferring 30 from cell 0 to cell 1, cell 0 reads 70 and cell 1 reads 35 — via HashMap
-- probes, not a closure walk. (`balOf` of the abstracted post-state at each cell.)
#guard balOf ((toAbstract (concreteTransfer demoCS 0 1 30)).cell 0) == 70
#guard balOf ((toAbstract (concreteTransfer demoCS 0 1 30)).cell 1) == 35
#guard balOf ((toAbstract (concreteTransfer demoCS 0 1 30)).cell 2) == 0  -- untouched cell defaults 0

-- A 100-transfer stream stays a flat sequence of HashMap inserts (no closure tower). The final
-- lookups are still single probes; conservation holds by `concreteTransfer_conserves` at each step.
def demoStream (n : Nat) (cs : ConcreteKernelState) : ConcreteKernelState :=
  match n with
  | 0 => cs
  | k + 1 => demoStream k (concreteTransfer cs 0 1 1)

-- After 50 unit transfers 0→1: cell 0 = 100-50 = 50, cell 1 = 5+50 = 55 — ONE probe each, no
-- 50-deep closure to walk.
#guard balOf ((toAbstract (demoStream 50 demoCS)).cell 0) == 50
#guard balOf ((toAbstract (demoStream 50 demoCS)).cell 1) == 55

-- setField writes one field via one insert; balance untouched when f ≠ "balance".
#guard fieldOf "owner" ((toAbstract (concreteWriteField demoCS "owner" 0 (.int 7))).cell 0) == 7
#guard balOf ((toAbstract (concreteWriteField demoCS "owner" 0 (.int 7))).cell 0) == 100

/-! ## §7 — AXIOM CLEANLINESS: the refinement rests only on `propext`/`Classical.choice`/`Quot.sound`.

No `sorryAx` — the squares and the proof-transfer corollary are genuine (the prompt's hard gate). -/

#print axioms toAbstract_concreteTransfer
#print axioms toAbstract_concreteWriteField
#print axioms concreteTransfer_conserves
#print axioms concreteWriteField_balOf_unchanged

end Dregg2.Exec
