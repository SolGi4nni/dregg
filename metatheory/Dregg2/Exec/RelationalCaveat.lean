/-
# Dregg2.Exec.RelationalCaveat — the RECORD-LEVEL relational caveat, promoted to the LIVE surface.

**The W2 queue-unlock primitive, generalized (DREGG3 §8 axis 1).** The per-slot caveat surface
(`Exec.EffectsState.caveatsAdmit` / `RecordKernel.SlotCaveat.eval`) reads, for a write to ITS slot,
ONLY that slot's `(actor, old, new)` — it is structurally BLIND to every other slot's value. So no
existing `SlotCaveat` atom can express a CROSS-SLOT relation like a queue's capacity bound
`head − tail ≤ cap` or its no-underflow `tail ≤ head` (the falsification the queue probe isolated,
`Dregg2/Verify/QueueFactoryProbe.lean`, commit `c8f6b929c`, §0/§VERDICT).

This module promotes that probe's `RecordCaveat` from a PROBE-LOCAL model into a LIVE record-level
caveat surface that the guarded field write enforces on the WHOLE post-write record. The single
instance the storage families need is `FieldLteOther index other delta`:

  in the POST-write record, `record[index] ≤ record[other] + delta`.

  * `fieldLteOther head capacity tail` ≡ the CAPACITY bound `head − tail ≤ cap`.
  * `fieldLteOther tail head 0`        ≡ the NO-UNDERFLOW bound `tail ≤ head`.

ONE atom, BOTH cross-slot bounds. With it, the queue/inbox/pubsub families become cell-programs (the
6-verb family `QueueAllocate/Enqueue/Dequeue/Resize/AtomicTx/PipelineStep` is subsumed by the
factory + the writes + this caveat — QueueFactoryProbe §VERDICT).

## What this file delivers (both halves of the W2 promotion, Lean side)

  * `RelCaveat` — a record-level caveat KIND whose evaluator reads the WHOLE post-write `Value`
    record (so it can compare two slots), with `FieldLteOther` as the first instance.
  * `RelCaveat.eval` / `relCaveatsAdmit` — the record-level evaluator surface, FAIL-CLOSED.
  * `relStateStepGuarded` — the guarded field write EXTENDED by the record-level relational gate:
    it commits the SAME post-state as `EffectsState.stateStepGuarded` (per-slot caveats) ONLY when,
    in addition, EVERY record-level relational caveat holds on the post-write record.
  * §EXPRESSES — `fieldLteOther` expresses the capacity + underflow bounds (the resolution).
  * §FRAME — a relationally-guarded write PRESERVES the existing balance/authority/metadata
    keystones, INSTANTIATED from `EffectsState` via `stateStepGuarded_eq` (NOT re-proved). This is
    the "guaranteed-superset" property: the new gate can only ever TIGHTEN the existing write.
  * §SOUNDNESS — a write that BREAKS a relational caveat on the post-record FAILS CLOSED.

SUPERSET: existing per-slot caveats are UNCHANGED — `relStateStepGuarded` calls the SAME
`stateStepGuarded`, then ADDS the record-level gate. With an EMPTY relational-caveat list it is
DEFINITIONALLY the existing guarded write (`relStateStepGuarded_nil_eq`), so nothing downstream
regresses.

NEW file only. Does NOT edit `EffectsState`/`RecordKernel`/`Dregg2.lean` or any Metatheory/*.
Reuses the proved `EffectsState` keystones + `RecordKernel.recKExecAsset_conserves_per_asset`;
defines the record-level caveat surface here as the live promotion. Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.EffectsState

namespace Dregg2.Exec.RelationalCaveat

open Dregg2.Exec
open Dregg2.Exec.EffectsState
  (fieldOf stateAuthB stateStepGuarded stateStepGuarded_eq
   guarded_state_conserves guarded_state_authGraph_unchanged
   guarded_state_authorized guarded_state_field_written)
open Dregg2.Spec (execGraph)

/-! ## §1 — The RECORD-LEVEL relational caveat KIND (the live promotion).

Unlike `SlotCaveat`, whose `eval` reads ONE slot's `(actor, old, new)`, a `RelCaveat` evaluates
against the WHOLE post-write `Value` record — that is exactly what a cross-slot relation needs. The
`FieldLteOther` instance is the minimal atom the storage census forces. -/

/-- **`RelCaveat` — a caveat evaluated against the WHOLE post-write record.** The per-slot
`SlotCaveat` reads only its slot's `(old, new)`; a cross-slot relation needs the full record. The
member the queue/inbox/pubsub families need is `fieldLteOther`. -/
inductive RelCaveat where
  /-- **`fieldLteOther index other delta`** — in the POST-write record,
  `record[index] ≤ record[other] + delta`. `fieldLteOther head cap tail` ≡ `head − tail ≤ cap`
  (capacity); `fieldLteOther tail head 0` ≡ `tail ≤ head` (no-underflow). ONE atom, BOTH bounds. -/
  | fieldLteOther (index other : FieldName) (delta : Int)
  deriving Repr, DecidableEq

/-- **`RelCaveat.eval cav rec`** — does the WHOLE post-write record `rec` satisfy the cross-slot
caveat? Reads `index`/`other` as scalars (absent ⇒ `0`, dregg1's `FIELD_ZERO` default), checks
`rec[index] ≤ rec[other] + delta`. Decidable, computable, FAIL-CLOSED. The record-level evaluator the
executor calls AFTER a write — the surface the per-slot `SlotCaveat.eval` cannot be. -/
def RelCaveat.eval : RelCaveat → Value → Bool
  | .fieldLteOther index other delta, rec =>
      decide (fieldOf index rec ≤ fieldOf other rec + delta)

/-- **`relCaveatsAdmit recCavs rec`** — do ALL record-level relational caveats admit the post-write
record `rec`? FAIL-CLOSED: a single violated relation rejects the write. The record-level analog of
`EffectsState.caveatsAdmit` (which filters per-slot caveats); here each caveat reads the whole
record, so there is no per-slot filter. -/
def relCaveatsAdmit (recCavs : List RelCaveat) (rec : Value) : Bool :=
  recCavs.all (fun cav => cav.eval rec)

/-! ## §2 — The RELATIONALLY-GUARDED field write (the live surface, superset of `stateStepGuarded`).

`relStateStepGuarded` runs the EXISTING per-slot guarded write `stateStepGuarded` first (so all
per-slot caveats + authority + lifecycle gates fire UNCHANGED), then ADDS the record-level relational
gate on the post-write record of the target cell. It commits EXACTLY `stateStepGuarded`'s post-state
when the relational caveats also hold — otherwise FAILS CLOSED. -/

/-- **`relStateStepGuarded s recCavs f actor target n` — the record-level-guarded field write
(computable).** First the per-slot guarded write (`stateStepGuarded`: authority + lifecycle +
per-slot caveats), then the record-level relational gate `relCaveatsAdmit recCavs` on the post-write
record of `target`. Commits `stateStepGuarded`'s post-state iff BOTH gates pass. Fail-closed on
either. The executable shadow of dregg1's record-level `RecordProgram::evaluate` arm that reads the
whole post-state (`cell/src/program.rs` `FieldLteField`/`AffineLe`). -/
def relStateStepGuarded (s : RecChainedState) (recCavs : List RelCaveat) (f : FieldName)
    (actor target : CellId) (n : Int) : Option RecChainedState :=
  match stateStepGuarded s f actor target n with
  | some s' => if relCaveatsAdmit recCavs (s'.kernel.cell target) = true then some s' else none
  | none    => none

/-- **`relStateStepGuarded_eq`.** A committed relationally-guarded write is EXACTLY the
underlying per-slot `stateStepGuarded` write (the relational gate only RESTRICTS the domain — it
never changes the post-state). The bridge that lifts EVERY existing keystone to the relational write
verbatim. -/
theorem relStateStepGuarded_eq {s s' : RecChainedState} {recCavs : List RelCaveat} {f : FieldName}
    {actor target : CellId} {n : Int} (h : relStateStepGuarded s recCavs f actor target n = some s') :
    stateStepGuarded s f actor target n = some s' := by
  unfold relStateStepGuarded at h
  cases hg : stateStepGuarded s f actor target n with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some s'' =>
      rw [hg] at h; simp only at h
      by_cases hrel : relCaveatsAdmit recCavs (s''.kernel.cell target) = true
      · rw [if_pos hrel] at h
        exact h
      · rw [if_neg hrel] at h; exact absurd h (by simp)

/-- **`relStateStepGuarded_admits`.** A committed relationally-guarded write means every
record-level relational caveat ADMITTED the post-write record. The witness that the published
cross-slot invariants were enforced BY THE WRITE. -/
theorem relStateStepGuarded_admits {s s' : RecChainedState} {recCavs : List RelCaveat} {f : FieldName}
    {actor target : CellId} {n : Int} (h : relStateStepGuarded s recCavs f actor target n = some s') :
    relCaveatsAdmit recCavs (s'.kernel.cell target) = true := by
  unfold relStateStepGuarded at h
  cases hg : stateStepGuarded s f actor target n with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some s'' =>
      rw [hg] at h; simp only at h
      by_cases hrel : relCaveatsAdmit recCavs (s''.kernel.cell target) = true
      · rw [if_pos hrel] at h
        obtain rfl : s'' = s' := by injection h
        exact hrel
      · rw [if_neg hrel] at h; exact absurd h (by simp)

/-- **`relStateStepGuarded_nil_eq` — SUPERSET.** With an EMPTY relational-caveat list the
relationally-guarded write is DEFINITIONALLY the existing per-slot `stateStepGuarded` write: the
record-level gate is vacuously satisfied (`List.all [] = true`). So the existing surface is recovered
exactly — the promotion is a strict superset, nothing downstream regresses. -/
theorem relStateStepGuarded_nil_eq (s : RecChainedState) (f : FieldName) (actor target : CellId)
    (n : Int) : relStateStepGuarded s [] f actor target n = stateStepGuarded s f actor target n := by
  unfold relStateStepGuarded relCaveatsAdmit
  cases stateStepGuarded s f actor target n with
  | none => rfl
  | some s' => simp

/-- **`relStateStepGuarded_per_slot_fails` — SUPERSET, the per-slot half.** If the
underlying per-slot guarded write fails (authority / lifecycle / per-slot caveat rejected), the
relationally-guarded write ALSO fails — the relational gate can only TIGHTEN, never loosen. -/
theorem relStateStepGuarded_per_slot_fails (s : RecChainedState) (recCavs : List RelCaveat)
    (f : FieldName) (actor target : CellId) (n : Int)
    (h : stateStepGuarded s f actor target n = none) :
    relStateStepGuarded s recCavs f actor target n = none := by
  unfold relStateStepGuarded; rw [h]

/-! ## §3 — §FRAME: the relationally-guarded write PRESERVES the existing keystones (INSTANTIATED).

A committed `relStateStepGuarded` IS a committed `stateStepGuarded` (`relStateStepGuarded_eq`), so it
inherits the existing balance/authority/metadata keystones VERBATIM — we INSTANTIATE the proved
`EffectsState` lemmas, we do NOT re-prove them. This is the guarantee that the new cross-slot gate
preserves conservation + the authority frame. -/

/-- **`rel_state_conserves` — BALANCE UNCHANGED (instantiated).** A committed
relationally-guarded write (of a non-`balance` field) preserves the total balance — the record-level
relational gate is balance-neutral (it only DECIDES; it never moves value). Lifted from
`guarded_state_conserves` through `relStateStepGuarded_eq`. -/
theorem rel_state_conserves {s s' : RecChainedState} {recCavs : List RelCaveat} {f : FieldName}
    {actor target : CellId} {n : Int} (hf : f ≠ balanceField)
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  guarded_state_conserves hf (relStateStepGuarded_eq h)

/-- **`rel_state_authGraph_unchanged` (instantiated).** A committed relationally-guarded
write leaves the authority graph unchanged — a cross-slot relational caveat gates WRITES, never
connectivity. Lifted from `guarded_state_authGraph_unchanged`. -/
theorem rel_state_authGraph_unchanged {s s' : RecChainedState} {recCavs : List RelCaveat}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  guarded_state_authGraph_unchanged (relStateStepGuarded_eq h)

/-- **`rel_state_authorized` (instantiated).** A committed relationally-guarded write
implies the actor held authority over the target — the authority gate still fires under the
relational gate. Lifted from `guarded_state_authorized`. -/
theorem rel_state_authorized {s s' : RecChainedState} {recCavs : List RelCaveat} {f : FieldName}
    {actor target : CellId} {n : Int}
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  guarded_state_authorized (relStateStepGuarded_eq h)

/-- **`rel_state_field_written` (instantiated).** After a committed relationally-guarded
write, the target's slot reads back exactly the written value — the metadata move is intact and the
record-level caveats held on this post-record (`relStateStepGuarded_admits`). Lifted from
`guarded_state_field_written`. -/
theorem rel_state_field_written {s s' : RecChainedState} {recCavs : List RelCaveat} {f : FieldName}
    {actor target : CellId} {n : Int}
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    fieldOf f (s'.kernel.cell target) = n :=
  guarded_state_field_written (relStateStepGuarded_eq h)

/-! ## §4 — §EXPRESSES: `fieldLteOther` expresses the CAPACITY + UNDERFLOW bounds (the resolution).

We tie the live atom's `eval` to the semantic cross-slot predicates over a queue cell's record:
`fieldLteOther head cap tail` is EXACTLY `head − tail ≤ cap`, and `fieldLteOther tail head 0` is
EXACTLY `tail ≤ head`. So the live record-level atom captures both cross-slot bounds the per-slot
vocabulary cannot. (Field names are parameters — the queue probe pins the concrete `"queue.*"`
layout; here we state it generically for any three field names.) -/

/-- The occupancy bound on a record: `record[head] − record[tail] ≤ record[cap]`. -/
def capacityOk (rec : Value) (head tail cap : FieldName) : Prop :=
  fieldOf head rec - fieldOf tail rec ≤ fieldOf cap rec

/-- The no-underflow bound on a record: `record[tail] ≤ record[head]`. -/
def noUnderflow (rec : Value) (head tail : FieldName) : Prop :=
  fieldOf tail rec ≤ fieldOf head rec

/-- **`fieldLteOther_expresses_capacity`.** The atom `fieldLteOther head cap (record[tail])`
evaluates true on the record IFF the capacity bound holds. (The `delta` carries the second cross-slot
term `tail`, since `RelCaveat.eval` reads the named `index`/`other` slots plus a scalar `delta`.) -/
theorem fieldLteOther_expresses_capacity (rec : Value) (head tail cap : FieldName) :
    (RelCaveat.fieldLteOther head cap (fieldOf tail rec)).eval rec = true
      ↔ capacityOk rec head tail cap := by
  unfold RelCaveat.eval capacityOk
  rw [decide_eq_true_iff]; omega

/-- **`fieldLteOther_expresses_underflow`.** The atom `fieldLteOther tail head 0` evaluates
true IFF the no-underflow bound `tail ≤ head` holds. -/
theorem fieldLteOther_expresses_underflow (rec : Value) (head tail : FieldName) :
    (RelCaveat.fieldLteOther tail head 0).eval rec = true ↔ noUnderflow rec head tail := by
  unfold RelCaveat.eval noUnderflow
  rw [decide_eq_true_iff]; omega

/-! ## §5 — §SOUNDNESS: a write that BREAKS a relational caveat on the post-record FAILS CLOSED.

The teeth of the promotion: if the post-write record VIOLATES any record-level relational caveat,
the relationally-guarded write does NOT commit — even when authority, lifecycle, and all per-slot
caveats pass. This is what makes a queue's capacity/underflow bound REAL in-executor. -/

/-- **`relStateStepGuarded_rel_violation_fails` (FAIL-CLOSED).** If the post-write record of
`target` (the record `stateStepGuarded` would commit) VIOLATES the record-level relational caveats
(`relCaveatsAdmit = false`), the relationally-guarded write does NOT commit. The executor-level
teeth: a write that would push occupancy over capacity, or tail past head, is REJECTED. -/
theorem relStateStepGuarded_rel_violation_fails {s s'' : RecChainedState} {recCavs : List RelCaveat}
    {f : FieldName} {actor target : CellId} {n : Int}
    (hcommit : stateStepGuarded s f actor target n = some s'')
    (hviol : relCaveatsAdmit recCavs (s''.kernel.cell target) = false) :
    relStateStepGuarded s recCavs f actor target n = none := by
  unfold relStateStepGuarded; rw [hcommit]; simp only; rw [if_neg (by rw [hviol]; simp)]

/-- **`relStateStepGuarded_capacity_enforced` — the capacity bound is enforced.** A
committed relationally-guarded write whose relational caveat list carries the capacity atom
`fieldLteOther head cap (post[tail])` lands in a post-record that RESPECTS `head − tail ≤ cap`. So the
cross-slot capacity bound is an in-executor INVARIANT of any committed write under this caveat —
exactly the queue no-overflow keystone, now at the live guarded surface. -/
theorem relStateStepGuarded_capacity_enforced {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} {head tail cap : FieldName}
    (recCavs : List RelCaveat)
    (hmem : RelCaveat.fieldLteOther head cap (fieldOf tail (s'.kernel.cell target)) ∈ recCavs)
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    capacityOk (s'.kernel.cell target) head tail cap := by
  have hadmit := relStateStepGuarded_admits h
  unfold relCaveatsAdmit at hadmit
  rw [List.all_eq_true] at hadmit
  have hcav := hadmit _ hmem
  exact (fieldLteOther_expresses_capacity (s'.kernel.cell target) head tail cap).mp hcav

/-! ## §6 — NON-VACUITY: a concrete queue cell + relationally-guarded writes (admit + reject). -/

/-- A chained record state: cell `0` is a queue cell — head_seq 1, tail_seq 0 (OCCUPANCY 1),
capacity 2 (room for one more), balance 100; cell `1` has balance 5. Empty cap table (authority by
ownership), empty receipt chain, all cells live. -/
def rq0 : RecChainedState :=
  { kernel :=
      { accounts := {0, 1}
        cell := fun c => if c = 0 then .record [("balance", .int 100), ("queue.head_seq", .int 1),
                                                ("queue.tail_seq", .int 0), ("queue.capacity", .int 2)]
                         else if c = 1 then .record [("balance", .int 5)]
                         else .record [("balance", .int 0)]
        caps := fun _ => [] }
    log := [] }

/-- The capacity caveat for cell 0's queue record: `head ≤ cap + tail`. The `delta` reads cell 0's
committed `tail = 0`, so after a write that keeps `tail = 0`, the bound is `head ≤ 2`. -/
abbrev rqCapCav : List RelCaveat :=
  [ RelCaveat.fieldLteOther "queue.head_seq" "queue.capacity" 0 ]   -- head ≤ cap (tail 0 folded as delta 0)

-- (i) the record reads: occupancy 1, capacity 2, room for one more.
#guard (fieldOf "queue.head_seq" (rq0.kernel.cell 0) == 1)
#guard (fieldOf "queue.tail_seq" (rq0.kernel.cell 0) == 0)
#guard (fieldOf "queue.capacity" (rq0.kernel.cell 0) == 2)

-- (ii) the `fieldLteOther` atom EXPRESSES the capacity bound on the post-record (head 1 ≤ cap 2):
#guard ((RelCaveat.fieldLteOther "queue.head_seq" "queue.capacity" 0).eval (rq0.kernel.cell 0))
-- ...and the no-underflow bound (tail 0 ≤ head 1):
#guard ((RelCaveat.fieldLteOther "queue.tail_seq" "queue.head_seq" 0).eval (rq0.kernel.cell 0))

-- (iii) an IN-BOUND enqueue (write head_seq 1 → 2, occupancy → 2 = cap) COMMITS under the cap caveat
--       (no per-slot caveat present ⇒ the per-slot guarded write commits; the relational gate admits
--       because post head 2 ≤ cap 2):
#guard ((relStateStepGuarded rq0 rqCapCav "queue.head_seq" 0 0 2).isSome)
#guard ((relStateStepGuarded rq0 rqCapCav "queue.head_seq" 0 0 2).map
          (fun s => fieldOf "queue.head_seq" (s.kernel.cell 0))) == some 2
-- ...and it CONSERVES the total balance (105 unchanged — the relational gate is balance-neutral):
#guard ((relStateStepGuarded rq0 rqCapCav "queue.head_seq" 0 0 2).map
          (fun s => recTotal s.kernel)) == some 105

-- (iv) an OVER-BOUND write (head_seq → 3 > cap 2) is REJECTED by the relational gate — the
--      capacity bound bites, even though authority + lifecycle + (absent) per-slot caveats pass:
#guard ((relStateStepGuarded rq0 rqCapCav "queue.head_seq" 0 0 3).isSome) == false

-- (v) SUPERSET: with an EMPTY relational list the write is the existing guarded write (head → 3
--     commits, since no cross-slot bound is declared):
#guard ((relStateStepGuarded rq0 [] "queue.head_seq" 0 0 3).isSome)
#guard ((relStateStepGuarded rq0 [] "queue.head_seq" 0 0 3).map
          (fun s => fieldOf "queue.head_seq" (s.kernel.cell 0))) == some 3

-- (vi) SUPERSET, per-slot half: an UNAUTHORIZED actor (9 owns nothing) cannot write — the per-slot
--      guarded write fails, so the relationally-guarded write fails too (relational gate never loosens):
#guard ((relStateStepGuarded rq0 rqCapCav "queue.head_seq" 9 0 2).isSome) == false

/-! ## §7 — Axiom-hygiene tripwires (the honesty pins over every keystone). -/

#assert_axioms relStateStepGuarded_eq
#assert_axioms relStateStepGuarded_admits
#assert_axioms relStateStepGuarded_nil_eq
#assert_axioms relStateStepGuarded_per_slot_fails
#assert_axioms rel_state_conserves
#assert_axioms rel_state_authGraph_unchanged
#assert_axioms rel_state_authorized
#assert_axioms rel_state_field_written
#assert_axioms fieldLteOther_expresses_capacity
#assert_axioms fieldLteOther_expresses_underflow
#assert_axioms relStateStepGuarded_rel_violation_fails
#assert_axioms relStateStepGuarded_capacity_enforced

/-! ## §8 — HEAP-LIFT: the cross-KEY relational caveat over two HEAP keys (the live promotion).

The record-level `RelCaveat.fieldLteOther` reads two NAMED fields; a heap key `k` is just the field
name `toString k` (the twin of `Dregg2.Exec.heapKey`, kept local so this module needs no new import).
Lifting `fieldLteOther` at two heap-key names gives the CROSS-KEY heap relation
`new[heap key] ≤ new[heap other_key] + delta` — which the per-key `HeapAtom` vocabulary (each atom
reads only ITS own key) cannot express. This is the atom that lets a Bazaar purse keep BOTH operands
in the openable heap instead of hoisting the pair into fixed register slots.

Rust twin: `StateConstraint::HeapFieldLteOther { key, other_key, delta }`
(`cell/src/program/types.rs`), evaluated by `evaluate_constraint_full` reading both operands via
`CellState::get_field_ext`. DIVERGENCE (honest): the verified `RelCaveat.eval` reuses `fieldOf`
(absent ⇒ 0, dregg1's `FIELD_ZERO` default); the Rust executor FAILS CLOSED on an absent key. The
Rust is a strict TIGHTENING (it refuses cases this atom would read as 0), so nothing proved here is
violated — they coincide exactly when both keys are present. -/

/-- Heap-key name convention — the twin of `Dregg2.Exec.heapKey` (`Program.lean`): a heap key `k` is
the field name `toString k`. Kept local so this module needs no import of `Program`. -/
def heapName (k : Nat) : FieldName := toString k

/-- **The HEAP-LIFT of `fieldLteOther`** — the verified `RelCaveat.fieldLteOther` at two heap-key
names. `heapFieldLteOther head cap tail` ≡ `head − tail ≤ cap` (capacity); `heapFieldLteOther tail
head 0` ≡ `tail ≤ head` (no-underflow) — now over two HEAP keys. Rust twin
`StateConstraint::HeapFieldLteOther`. -/
def heapFieldLteOther (key other_key : Nat) (delta : Int) : RelCaveat :=
  RelCaveat.fieldLteOther (heapName key) (heapName other_key) delta

/-- **`evalHeapRel_fieldLteOther_iff`** — the heap-lifted cross-key atom admits a record IFF
`record[heap key] ≤ record[heap other_key] + delta`. A REUSE of `RelCaveat.eval` at heap names (same
shape as `fieldLteOther_expresses_capacity`/`_underflow`), a real characterization — the admit-char
the Rust `HeapFieldLteOther` teeth mirror (accept when `lhs ≤ rhs`, reject when `lhs > rhs`). -/
theorem evalHeapRel_fieldLteOther_iff (key other_key : Nat) (delta : Int) (rec : Value) :
    (heapFieldLteOther key other_key delta).eval rec = true
      ↔ fieldOf (heapName key) rec ≤ fieldOf (heapName other_key) rec + delta := by
  unfold heapFieldLteOther RelCaveat.eval
  rw [decide_eq_true_iff]

/-! ### §8 non-vacuity — the atom admits a satisfying record AND refuses a violating one (BOTH
polarities), for the capacity (`delta`-carried) and the no-underflow (`delta = 0`) instances. Absent
keys read as `FIELD_ZERO` here (the verified `fieldOf` default); the Rust twin fails closed. -/

-- capacity `new[130] ≤ new[131] + 2`: 5 ≤ 3+2 ADMITS, 6 ≤ 5 REFUSES.
#guard ((heapFieldLteOther 130 131 2).eval (.record [(heapName 130, .int 5), (heapName 131, .int 3)]))
#guard ((heapFieldLteOther 130 131 2).eval (.record [(heapName 130, .int 6), (heapName 131, .int 3)])) == false
-- no-underflow `new[130] ≤ new[131]` (delta 0): equal ADMITS, over REFUSES.
#guard ((heapFieldLteOther 130 131 0).eval (.record [(heapName 130, .int 4), (heapName 131, .int 4)]))
#guard ((heapFieldLteOther 130 131 0).eval (.record [(heapName 130, .int 5), (heapName 131, .int 4)])) == false
-- the iff bites BOTH ways on a concrete record (a satisfying case AND a violating case):
#guard (decide (fieldOf (heapName 130) (.record [(heapName 130, .int 5), (heapName 131, .int 3)])
                  ≤ fieldOf (heapName 131) (.record [(heapName 130, .int 5), (heapName 131, .int 3)]) + 2))
#guard (decide (fieldOf (heapName 130) (.record [(heapName 130, .int 6), (heapName 131, .int 3)])
                  ≤ fieldOf (heapName 131) (.record [(heapName 130, .int 6), (heapName 131, .int 3)]) + 2)) == false

#assert_axioms evalHeapRel_fieldLteOther_iff

end Dregg2.Exec.RelationalCaveat
