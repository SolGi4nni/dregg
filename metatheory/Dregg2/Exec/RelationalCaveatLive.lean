/-
# Dregg2.Exec.RelationalCaveatLive — the Rust↔Lean live-path CORRESPONDENCE for the
record-level relational caveat `FieldLteOther`.

`Dregg2.Exec.RelationalCaveat` already promotes the cross-slot caveat onto the LIVE guarded
write (`relStateStepGuarded` calls the real `EffectsState.stateStepGuarded`, then ADDS the
record-level relational gate, with every keystone proved + `#assert_axioms`-pinned). That file
is the live Lean surface.

This NEW file pins the OTHER half of "live": the Lean evaluator's decision matches, ARM FOR ARM,
the semantics the running Rust executor now enforces. The Rust arm wired into
`cell/src/program.rs` `evaluate_constraint_full` is:

    StateConstraint::FieldLteOther { index, other, delta } =>
        let lhs = field_to_u64(new[index]) as i128;
        let rhs = field_to_u64(new[other]) as i128 + delta as i128;
        if lhs > rhs { violated } else { Ok }              -- i.e. ACCEPT ⟺ lhs ≤ rhs

The Lean evaluator `RelCaveat.eval (.fieldLteOther index other delta) rec` decides
`fieldOf index rec ≤ fieldOf other rec + delta`. This file proves those are the SAME predicate
(`relCaveat_eval_iff_le`), so the Rust transcription is faithful to the verified atom — the
executor's enforcement and the proved model agree on admit AND reject.

It also instantiates the live capacity/underflow enforcement (`relStateStepGuarded`) at the
concrete queue field layout, so the cross-slot bounds are pinned as in-executor invariants of a
committed guarded write under the corresponding caveat.

NEW file only. Does NOT edit `RelationalCaveat`/`EffectsState`/`Dregg2.lean` or any Metatheory/*.
Imports + reuses the proved surface; every result `#assert_axioms`-pinned to
`{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`.
-/
import Dregg2.Exec.RelationalCaveat

namespace Dregg2.Exec.RelationalCaveatLive

open Dregg2.Exec
open Dregg2.Exec.EffectsState (fieldOf stateStepGuarded)
open Dregg2.Exec.RelationalCaveat

/-! ## §1 — The Rust↔Lean evaluator CORRESPONDENCE (admit ⟺ `lhs ≤ rhs`).

The single fact that makes the Rust arm a faithful transcription: the Lean evaluator accepts a
record IFF the cross-slot inequality `record[index] ≤ record[other] + delta` holds — exactly the
`lhs ≤ rhs` the Rust executor decides. -/

/-- **`relCaveat_eval_iff_le`.** The Lean evaluator `RelCaveat.eval` accepts `rec` IFF
`fieldOf index rec ≤ fieldOf other rec + delta`. This is the EXACT predicate the running Rust
`evaluate_constraint_full` arm decides (`lhs ≤ rhs`, `rhs = other + delta`). The two transcriptions
agree on admit and reject. -/
theorem relCaveat_eval_iff_le (index other : FieldName) (delta : Int) (rec : Value) :
    (RelCaveat.fieldLteOther index other delta).eval rec = true
      ↔ fieldOf index rec ≤ fieldOf other rec + delta := by
  unfold RelCaveat.eval
  rw [decide_eq_true_iff]

/-- **`relCaveat_reject_iff_gt`.** The contrapositive face the executor's fail-closed
branch takes: the Lean evaluator REJECTS `rec` IFF `fieldOf index rec > fieldOf other rec + delta`
— exactly the Rust `lhs > rhs` violation branch. -/
theorem relCaveat_reject_iff_gt (index other : FieldName) (delta : Int) (rec : Value) :
    (RelCaveat.fieldLteOther index other delta).eval rec = false
      ↔ fieldOf other rec + delta < fieldOf index rec := by
  rw [← Bool.not_eq_true, relCaveat_eval_iff_le]
  omega

/-! ## §2 — The live enforcement, pinned at the concrete queue field layout.

`relStateStepGuarded_capacity_enforced` (in `RelationalCaveat`) already proves that a committed
relationally-guarded write under the capacity atom lands in a record respecting `head − tail ≤ cap`.
Here we instantiate it at the canonical `"queue.*"` field names, so the storage-family layout the
Rust executor uses has the cross-slot bound pinned as an in-executor invariant. -/

/-- The canonical queue field names (mirrors `cell/tests/relational_caveat.rs` `HEAD/TAIL/CAP`). -/
abbrev qHead : FieldName := "queue.head_seq"
abbrev qTail : FieldName := "queue.tail_seq"
abbrev qCap  : FieldName := "queue.capacity"

/-- **`queue_capacity_enforced_live` (instantiated).** A committed relationally-guarded
write whose caveat list carries the queue capacity atom lands in a post-record respecting the
capacity bound `head − tail ≤ cap`. The cross-slot invariant the Rust executor now enforces, pinned
at the concrete queue layout. -/
theorem queue_capacity_enforced_live {s s' : RecChainedState} {f : FieldName}
    {actor target : CellId} {n : Int} (recCavs : List RelCaveat)
    (hmem : RelCaveat.fieldLteOther qHead qCap (fieldOf qTail (s'.kernel.cell target)) ∈ recCavs)
    (h : relStateStepGuarded s recCavs f actor target n = some s') :
    capacityOk (s'.kernel.cell target) qHead qTail qCap :=
  relStateStepGuarded_capacity_enforced recCavs hmem h

/-- **`queue_underflow_eval_live`.** The no-underflow atom `fieldLteOther tail head 0`
accepts a record IFF `tail ≤ head` — the dual cross-slot bound the Rust executor enforces. -/
theorem queue_underflow_eval_live (rec : Value) :
    (RelCaveat.fieldLteOther qTail qHead 0).eval rec = true ↔ noUnderflow rec qHead qTail :=
  fieldLteOther_expresses_underflow rec qHead qTail

/-! ## §3 — Axiom-hygiene tripwires. -/

#assert_axioms relCaveat_eval_iff_le
#assert_axioms relCaveat_reject_iff_gt
#assert_axioms queue_capacity_enforced_live
#assert_axioms queue_underflow_eval_live

end Dregg2.Exec.RelationalCaveatLive
