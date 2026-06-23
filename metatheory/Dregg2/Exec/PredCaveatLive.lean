/-
# Dregg2.Exec.PredCaveatLive — the reified `CaveatPred` AST, evaluated on the LIVE admission path.

The D6 reification (`Dregg2/Authority/Caveat.lean`) built `CaveatPred` — the introspectable,
printable, structurally-refinable caveat AST — but evaluated it only on the *token* leg
(`Caveat.ok` / `Token.admits`) and in `#guard` demos. This file PROMOTES `CaveatPred` onto the
**live executor field-write admission path** (`EffectsState.stateStepGuarded`, the leg `setFieldA`
runs), following the EXACT pattern `Exec.RelationalCaveat` used to promote `RelCaveat`: run the
existing per-slot guarded write FIRST (so every authority / lifecycle / `SlotCaveat` gate fires
UNCHANGED), then ADD the reified-caveat gate. A `.pred`-reified caveat is now genuinely DECIDED by
the executor on the same `(actor, old, new)` transition the hand-catalog `SlotCaveat` sees.

## The domain bridge (the honest one)

`CaveatPred.eval` denotes over a request `Ctx` through an explicit `view : Ctx → Time` seam. The live
executor's admission unit is the SCALAR TRANSITION `(actor, old, new)`. We make that transition tuple
itself the `Ctx` and supply a `txView` projection — so the SAME tuple `caveatsAdmit`/`SlotCaveat.eval`
read is what `CaveatPred.eval` reads. A `validAfter t` over `txView := (·.new)` is the live floor
`new ≥ t`; a `validUntil t` is the ceiling `new ≤ t`. NO new `SlotCaveat` constructor (that would be
VK-affecting via the witness encoder `CreateCellFromFactoryWitness.lean`), NO change to
`caveatsAdmit`'s signature or its decision on existing inputs (the circuit's `caveatBit` binding is
byte-identical) — a strict, composed SUPERSET, recovered exactly at the empty caveat list
(`predCaveatStateStepGuarded_nil_eq`).

## HONEST FRAMING — expressiveness, NOT soundness

This is a LANGUAGE / expressiveness gain: the live executor now enforces an INSPECTABLE caveat term
(you can print/compare/refine it) where before it enforced an opaque catalog arm. It is NOT a
soundness gain. The circuit still binds the AGGREGATE `caveatsAdmit` decision bit and TRUSTS the
executor; reifying a caveat does not force its policy in-circuit. Making the STARK bind the predicate
TERM (so a light client can't be fooled about WHICH policy gated a write) is the circuit-soundness
apex campaign's descriptor work, out of scope here and neither closed nor regressed by this file.

NEW file only. Does NOT edit `EffectsState`/`RecordKernel`/`Authority.Caveat`/the circuit/any
`TurnExecutorFull` arm. Reuses the proved `stateStepGuarded` keystones via `stateStepGuarded_eq`.
Every keystone `#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.EffectsState
import Dregg2.Authority.Caveat

namespace Dregg2.Exec.PredCaveatLive

open Dregg2.Exec
open Dregg2.Exec.EffectsState
  (fieldOf stateAuthB stateStepGuarded stateStepGuarded_eq
   guarded_state_conserves guarded_state_authGraph_unchanged
   guarded_state_authorized guarded_state_field_written)
open Dregg2.Authority (CaveatPred Time heightView)
open Dregg2.Spec (execGraph)

/-! ## §1 — The TRANSITION context: the live tuple a `CaveatPred` is evaluated against.

`CaveatPred.eval` is parametric in `(view : Ctx → Time)`. The executor's admission unit is the
SCALAR TRANSITION `(actor, old, new)` — so we instantiate `Ctx := TxCtx` and read `Time` off it.
A `CaveatPred` evaluated under `txViewNew` is a caveat ON THE WRITTEN VALUE `new`; under `txViewOld`
it is a caveat on the slot's prior value. The reified AST stays pure DATA; the seam is the projection. -/

/-- The live transition context: the `(actor, old, new)` triple the per-slot caveat surface evaluates
against (`SlotCaveat.eval actor old new` reads exactly this). The `Ctx` a `CaveatPred` denotes over on
the executor leg. -/
structure TxCtx where
  actor : CellId
  old   : Int
  new   : Int
  deriving Repr, DecidableEq

/-- The DEFAULT live view: a temporal `CaveatPred` reads the WRITTEN value `new` as the request time
(`validAfter t` ⇒ `new ≥ t`, a value floor; `validUntil t` ⇒ `new ≤ t`, a value ceiling). The
projection that turns a request-context AST into a transition gate. -/
def txViewNew : TxCtx → Time := fun c => c.new

/-- The prior-value view: a temporal `CaveatPred` reads the slot's committed value `old` (a caveat on
where the slot WAS, not where it's going). The other projection the bundled seam can carry. -/
def txViewOld : TxCtx → Time := fun c => c.old

/-! ## §2 — The live admission decision over a reified `CaveatPred`.

`caveatPredAdmit` is the `caveatsAdmit`-shaped decision for the reified surface: do ALL `CaveatPred`
caveats bound to slot `f` (each carrying its own transition `view`) admit the write of `new` (read
against the committed `fieldOf f (k.cell target)`, defaulting absent to `0` — dregg1's `FIELD_ZERO`)?
A `predCaveat` pairs the field it guards with the reified AST and its view, mirroring `PredCaveat`. -/

/-- A reified caveat bound to the live leg: the slot `field` it guards, the introspectable `pred` AST,
and the `view` projecting the transition context to the AST's `Time` dimension. The reified twin of
`RecordKernel.SlotCaveat` / `PredAlgebra.PredCaveat`. -/
structure ReifiedCaveat where
  field : FieldName
  pred  : CaveatPred
  view  : TxCtx → Time

/-- Evaluate one reified caveat on a scalar write of `new` (committed value `old`) by `actor`: build
the live `TxCtx` and fold the introspectable AST through `CaveatPred.eval`. -/
def ReifiedCaveat.eval (rc : ReifiedCaveat) (actor : CellId) (old new : Int) : Bool :=
  CaveatPred.eval rc.view rc.pred { actor := actor, old := old, new := new }

/-- **`caveatPredAdmit`** — do ALL reified caveats bound to slot `f` admit the scalar write `new` by
`actor` to `target` (against the committed `fieldOf f (k.cell target)`)? The `CaveatPred` analog of
`EffectsState.caveatsAdmit`: same per-slot filter, same `(actor, old, new)` transition, same
fail-closed `List.all`. The reified policy is DECIDED here, on the live leg. -/
def caveatPredAdmit (caveats : List ReifiedCaveat) (k : RecordKernelState) (f : FieldName)
    (actor target : CellId) (new : Int) : Bool :=
  ((caveats.filter (fun rc => rc.field == f)).all
    (fun rc => rc.eval actor (fieldOf f (k.cell target)) new))

/-! ## §3 — The reified-guarded field write (SUPERSET of `stateStepGuarded`).

`predCaveatStateStepGuarded` runs the EXISTING per-slot `stateStepGuarded` FIRST (authority +
lifecycle + every `SlotCaveat` gate, UNCHANGED), then ADDS the reified-caveat gate on the SAME
transition. It commits EXACTLY `stateStepGuarded`'s post-state when the reified caveats also admit —
otherwise FAILS CLOSED. The `RelationalCaveat.relStateStepGuarded` composition, for the reified AST. -/

/-- **`predCaveatStateStepGuarded` — the reified-`CaveatPred`-gated field write (computable).** First
the per-slot guarded write (`stateStepGuarded`), then the reified-caveat gate `caveatPredAdmit` on the
write of `n` to slot `f`. Commits `stateStepGuarded`'s post-state iff BOTH gates pass; fail-closed on
either. The live executor enforcement of the introspectable caveat AST. -/
def predCaveatStateStepGuarded (s : RecChainedState) (caveats : List ReifiedCaveat) (f : FieldName)
    (actor target : CellId) (n : Int) : Option RecChainedState :=
  if caveatPredAdmit caveats s.kernel f actor target n = true then
    stateStepGuarded s f actor target n
  else
    none

/-- **`predCaveatStateStepGuarded_eq` (the safety net).** A committed reified-guarded write is EXACTLY
the underlying per-slot `stateStepGuarded` write — the reified gate only RESTRICTS the domain, never
changes the post-state. Lifts EVERY existing `stateStepGuarded` keystone to the reified write
verbatim. -/
theorem predCaveatStateStepGuarded_eq {s s' : RecChainedState} {caveats : List ReifiedCaveat}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    stateStepGuarded s f actor target n = some s' := by
  unfold predCaveatStateStepGuarded at h
  by_cases hg : caveatPredAdmit caveats s.kernel f actor target n = true
  · rw [if_pos hg] at h; exact h
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predCaveatStateStepGuarded_admits`.** A committed reified-guarded write means every reified
caveat bound to the written slot ADMITTED the transition — the witness that the introspectable policy
was enforced BY THE EXECUTOR on the live leg. -/
theorem predCaveatStateStepGuarded_admits {s s' : RecChainedState} {caveats : List ReifiedCaveat}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    caveatPredAdmit caveats s.kernel f actor target n = true := by
  unfold predCaveatStateStepGuarded at h
  by_cases hg : caveatPredAdmit caveats s.kernel f actor target n = true
  · exact hg
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`predCaveatStateStepGuarded_nil_eq` — SUPERSET (nothing regresses).** With an EMPTY reified-caveat
list the reified-guarded write is DEFINITIONALLY the existing per-slot `stateStepGuarded` write: the
reified gate is vacuously satisfied (`List.all [] = true`). So the existing executor surface is
recovered exactly — the promotion is a strict superset. -/
theorem predCaveatStateStepGuarded_nil_eq (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int) :
    predCaveatStateStepGuarded s [] f actor target n = stateStepGuarded s f actor target n := by
  unfold predCaveatStateStepGuarded caveatPredAdmit
  simp

/-- **`predCaveatStateStepGuarded_per_slot_fails` — SUPERSET, the per-slot half.** If the underlying
per-slot guarded write fails (authority / lifecycle / `SlotCaveat` rejected), the reified-guarded write
ALSO fails — the reified gate can only TIGHTEN, never loosen. NO admission WEAKENING. -/
theorem predCaveatStateStepGuarded_per_slot_fails (s : RecChainedState) (caveats : List ReifiedCaveat)
    (f : FieldName) (actor target : CellId) (n : Int)
    (h : stateStepGuarded s f actor target n = none) :
    predCaveatStateStepGuarded s caveats f actor target n = none := by
  unfold predCaveatStateStepGuarded
  by_cases hg : caveatPredAdmit caveats s.kernel f actor target n = true
  · rw [if_pos hg, h]
  · rw [if_neg hg]

/-- **`predCaveatStateStepGuarded_violation_fails` (FAIL-CLOSED — the core soundness teeth).** If ANY
reified caveat bound to the written slot REJECTS the transition (`caveatPredAdmit = false`), the write
does NOT commit. The proof the new arm does not WEAKEN admission: a `.pred` caveat that should reject
DOES reject, BY THE EXECUTOR. -/
theorem predCaveatStateStepGuarded_violation_fails (s : RecChainedState) (caveats : List ReifiedCaveat)
    (f : FieldName) (actor target : CellId) (n : Int)
    (h : caveatPredAdmit caveats s.kernel f actor target n = false) :
    predCaveatStateStepGuarded s caveats f actor target n = none := by
  unfold predCaveatStateStepGuarded; rw [if_neg (by rw [h]; simp)]

/-! ## §4 — THE WIRING IS SOUND: the live decision IS the `CaveatPred` denotation.

The point of "wiring it live" is that the executor's admission decision over a `.pred` caveat is
EXACTLY the reified AST's denotation — not a re-interpretation. `caveatPredAdmit_single` proves it for
a single-caveat slot: the live `caveatPredAdmit` over a one-element list equals `CaveatPred.eval` on
the live transition context. So the executor decides precisely what the printable AST SAYS. -/

/-- **`caveatPredAdmit_single`** — the live admission over a SINGLE reified caveat on slot `f` IS that
caveat's `CaveatPred.eval` on the live `(actor, old, new)` transition context (read against the
committed `fieldOf f (k.cell target)`). The executor's decision = the AST's denotation, exactly. -/
theorem caveatPredAdmit_single (k : RecordKernelState) (f : FieldName) (actor target : CellId)
    (new : Int) (p : CaveatPred) (view : TxCtx → Time) :
    caveatPredAdmit [{ field := f, pred := p, view := view }] k f actor target new
      = CaveatPred.eval view p { actor := actor, old := fieldOf f (k.cell target), new := new } := by
  unfold caveatPredAdmit ReifiedCaveat.eval
  simp

/-! ## §5 — MUTATION-CONFIRM: a `validAfter t` reified caveat REJECTS before `t`, ADMITS at/after,
THROUGH THE LIVE WRITE. The reified value-floor caveat genuinely gates the executor's field write. -/

/-- A `validAfter 100` reified caveat on slot `"v"`, reading the WRITTEN value as the floor's time
(`new ≥ 100`). The introspectable AST — printable, refinable — bound to the live leg. -/
def vFloor : ReifiedCaveat := { field := "v", pred := .validAfter 100, view := txViewNew }

/-- A minimal demo kernel for the mutation-confirm `#guard`s: cell `0` holds `("v", 0)`, every
default elsewhere. (A value-floor over `txViewNew` reads `new`, so the committed value is irrelevant —
this just provides a concrete `RecordKernelState`.) -/
def demoKernel : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("v", .int 0)], caps := fun _ => [] }

-- The admission decision, in isolation (committed value irrelevant to a value-floor on `new`).
#guard caveatPredAdmit [vFloor] demoKernel "v" 0 0 150          -- 150 ≥ 100 ⇒ admit
#guard caveatPredAdmit [vFloor] demoKernel "v" 0 0 50 == false  -- 50 < 100 ⇒ REJECT

/-- The live admission MUTATION-CONFIRM at the `by decide` layer: `validAfter 100` admits `150`
and rejects `50` — through the SAME `caveatPredAdmit` the guarded write consults. -/
theorem vFloor_admits_after :
    caveatPredAdmit [vFloor] demoKernel "v" 0 0 150 = true := by decide

theorem vFloor_rejects_before :
    caveatPredAdmit [vFloor] demoKernel "v" 0 0 50 = false := by decide

/-- **`vFloor_live_rejects_before` (FAIL-CLOSED through the LIVE write).** A write of `50` to the
`validAfter 100`-floored slot does NOT commit — the reified caveat rejected it ON THE LIVE
`predCaveatStateStepGuarded` path (not a demo). The mutation confirmed end-to-end: rejects-before. -/
theorem vFloor_live_rejects_before (s : RecChainedState) (actor target : CellId)
    (h : caveatPredAdmit [vFloor] s.kernel "v" actor target 50 = false) :
    predCaveatStateStepGuarded s [vFloor] "v" actor target 50 = none :=
  predCaveatStateStepGuarded_violation_fails s [vFloor] "v" actor target 50 h

/-- **`vFloor_live_admits_after` (ADMITS through the LIVE write).** When the per-slot gates pass AND
the reified floor admits (`150 ≥ 100`), the write COMMITS exactly `stateStepGuarded`'s post-state —
the reified caveat did not block an admissible write. The mutation confirmed: admits-after. -/
theorem vFloor_live_admits_after (s s' : RecChainedState) (actor target : CellId)
    (hadm : caveatPredAdmit [vFloor] s.kernel "v" actor target 150 = true)
    (hcommit : stateStepGuarded s "v" actor target 150 = some s') :
    predCaveatStateStepGuarded s [vFloor] "v" actor target 150 = some s' := by
  unfold predCaveatStateStepGuarded; rw [if_pos hadm, hcommit]

/-! ### A composed reified window on the live leg — `validAfter 100 ∧ validUntil 300`, both bounds now
INSPECTABLE atoms (the D6 beachhead left the ceiling an opaque escape hatch). The live admission
narrows to `[100, 300]` on the written value, decided from the printable AST. -/

/-- A reified WINDOW caveat: the written value must lie in `[100, 300]`, authored in the AST's
connectives over the shared `txViewNew` seam. -/
def vWindow : ReifiedCaveat :=
  { field := "v", pred := .and (.validAfter 100) (.validUntil 300), view := txViewNew }

#guard caveatPredAdmit [vWindow] demoKernel "v" 0 0 150          -- in [100,300] ⇒ admit
#guard caveatPredAdmit [vWindow] demoKernel "v" 0 0 50 == false  -- below floor ⇒ reject
#guard caveatPredAdmit [vWindow] demoKernel "v" 0 0 350 == false -- above ceiling ⇒ reject
example : caveatPredAdmit [vWindow] demoKernel "v" 0 0 150 = true  := by decide
example : caveatPredAdmit [vWindow] demoKernel "v" 0 0 350 = false := by decide

/-! ## §6 — §FRAME: the reified-guarded write PRESERVES the existing keystones (INSTANTIATED).

A committed `predCaveatStateStepGuarded` IS a committed `stateStepGuarded` (`…_eq`), so it inherits
balance/authority/metadata VERBATIM — INSTANTIATED, not re-proved. The new gate preserves
conservation + the authority frame; the language uplift moves no value and edits no caps. -/

/-- **`pred_state_conserves` — BALANCE UNCHANGED (instantiated).** -/
theorem pred_state_conserves {s s' : RecChainedState} {caveats : List ReifiedCaveat} {f : FieldName}
    {actor target : CellId} {n : Int} (hf : f ≠ balanceField)
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    recTotal s'.kernel = recTotal s.kernel :=
  guarded_state_conserves hf (predCaveatStateStepGuarded_eq h)

/-- **`pred_state_authGraph_unchanged` (instantiated).** -/
theorem pred_state_authGraph_unchanged {s s' : RecChainedState} {caveats : List ReifiedCaveat}
    {f : FieldName} {actor target : CellId} {n : Int}
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    execGraph s'.kernel.caps = execGraph s.kernel.caps :=
  guarded_state_authGraph_unchanged (predCaveatStateStepGuarded_eq h)

/-- **`pred_state_authorized` (instantiated).** -/
theorem pred_state_authorized {s s' : RecChainedState} {caveats : List ReifiedCaveat} {f : FieldName}
    {actor target : CellId} {n : Int}
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    stateAuthB s.kernel.caps actor target = true :=
  guarded_state_authorized (predCaveatStateStepGuarded_eq h)

/-- **`pred_state_field_written` (instantiated).** After a committed reified-guarded write the target's
slot reads back exactly the written value — the metadata move is intact and the reified caveats held on
this transition (`predCaveatStateStepGuarded_admits`). -/
theorem pred_state_field_written {s s' : RecChainedState} {caveats : List ReifiedCaveat} {f : FieldName}
    {actor target : CellId} {n : Int}
    (h : predCaveatStateStepGuarded s caveats f actor target n = some s') :
    fieldOf f (s'.kernel.cell target) = n :=
  guarded_state_field_written (predCaveatStateStepGuarded_eq h)

#assert_axioms caveatPredAdmit_single
#assert_axioms predCaveatStateStepGuarded_eq
#assert_axioms predCaveatStateStepGuarded_admits
#assert_axioms predCaveatStateStepGuarded_nil_eq
#assert_axioms predCaveatStateStepGuarded_per_slot_fails
#assert_axioms predCaveatStateStepGuarded_violation_fails
#assert_axioms vFloor_admits_after
#assert_axioms vFloor_rejects_before
#assert_axioms vFloor_live_rejects_before
#assert_axioms vFloor_live_admits_after
#assert_axioms pred_state_conserves

end Dregg2.Exec.PredCaveatLive
