/-
# Dregg2.Circuit.Emit.EffectLowerCore — the logic compiler's BACK END, on its own.

The normalizer (`exprToHead`), the constraint lowering (`lowerConstraint`), the Phase-2 leg
lowerings (`lowerLookupLeg` / `lowerWindowLeg` / `lowerPiPinLeg` / `lowerRangeLeg`, and the
`refuseConstraints` REFUSAL), the assembler, and the bare-AIR entry point `lowerAir`.

## Why it is a separate module (2026-08-01 — THE FIRST RAIL FUSION)

`EffectLower.lean` carries this back end AND transfer's `EffectSpec2` differential, so it imports
`Inst/transfer.lean`, `EffectCommit2` and `WitnessExtract`. That is fine for a module that MODELS a
deployed descriptor beside its hand-written twin — and impossible for one a deployed descriptor is
DEFINED BY. `DfaRoutingTableEmit`'s `tableRoutingDesc` is now literally `lowerAir` of an
`EffectAir` source (`DfaRoutingTableEmit.lean` §2), which means the compiler has to sit BELOW the
descriptor, not above it.

So the back end lives here — `AirBuilder` + `EffectAirIR` + `DescriptorIR2` and nothing else — and
`EffectLower.lean` keeps the full-state entry (`lowerCS`/`lowerEffect`, which need the framework's
`PIBindsDigests` surface) plus the transfer differential. Same namespace
(`Dregg2.Circuit.Emit.EffectLower`), so every existing name resolves unqualified and no consumer
moved.

⚑ House law #1 in its endpoint form: the AIR is Lean-authored, and now the Lean is a COMPILER. A
descriptor that imports this module has no hand-written `VmConstraint2` list to drift from.

## Axiom hygiene

Every theorem here is `#assert_axioms`-clean in `EffectLower.lean` §10 (the tripwires stayed with
the rest of the pass so one file still names the whole surface).
-/
import Dregg2.Circuit
import Dregg2.Circuit.EffectAirIR
import Dregg2.Circuit.Emit.AirBuilder

namespace Dregg2.Circuit.Emit.EffectLower

open Dregg2.Circuit
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv VmRange)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.EffectAirIR
  (EffectAir AirLeg ChalLeg BindLeg LookupLeg WindowLeg RangeLeg PiPinLeg LimbsLeg exprIsOne
   chalReadsNext)
open Dregg2.Circuit.TableAirIR (BusOp RowSel readsNext)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The BabyBear modulus the deployed row denotation reduces against. -/
abbrev P : ℤ := 2013265921

/-! ## §1 — the polynomial normalizer `Expr → AirBuilder.Head`.

`Circuit.Expr` is an arbitrary var/const/+/× tree; `AirBuilder.Head` is the flat builder normal
form `Σ (coeff, cols) + const`. The `mul` case is the only real content: a distribute over both
term lists plus the two constant cross-terms. `evalH_mulHead` is its semantic bridge, and
`evalH_exprToHead` composes the four cases into "the head means what the expression meant". -/

/-- Multiply two heads: distribute term×term, then each side's terms against the other's constant,
then the constant product.

⚑ **THE CONSTANT CROSS-PRODUCTS ARE GUARDED ON A NONZERO CONSTANT** (2026-08-01, the Phase-3
re-emission). Unguarded, `(D) * (D_inv)` — two pure-term heads with constant `0` — distributed to
THREE terms: the genuine `1·D·D_inv` plus `0·D` and `0·D_inv`, and those rendered into the wire
bytes of every product gate the compiler emits. They are not the author's terms and they are not
implied by the source: multiplying by a zero constant contributes nothing. Dropping them is NOT the
zero-coefficient elision the corpus invariant forbids (`AirNormalForm` rule 3, which is about a term
the SOURCE wrote); it is the normalizer declining to INVENT one. `evalH_mulHead` still holds
unconditionally — the guarded branches are exactly the ones whose value is `0`. -/
def mulHead (h o : Head) : Head :=
  { terms := (h.terms.flatMap fun t => o.terms.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List Nat))
             ++ (if o.const = 0 then [] else h.terms.map fun t => ((t.1 * o.const, t.2) : ℤ × List Nat))
             ++ (if h.const = 0 then [] else o.terms.map fun u => ((h.const * u.1, u.2) : ℤ × List Nat))
  , const := h.const * o.const }

private theorem sum_scaleR (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    ((ts.map fun t => ((t.1 * k, t.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * k := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm]
    ring

private theorem sum_scaleL (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    ((ts.map fun t => ((k * t.1, t.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = k * (ts.map (evalTerm a)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm]
    ring

private theorem sum_crossOne (a : Assignment) (x : ℤ × List Nat) (us : List (ℤ × List Nat)) :
    ((us.map fun u => ((x.1 * u.1, x.2 ++ u.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = evalTerm a x * (us.map (evalTerm a)).sum := by
  induction us with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, ih, evalTerm, List.map_append, List.prod_append]
    ring

private theorem sum_cross (a : Assignment) (ts us : List (ℤ × List Nat)) :
    ((ts.flatMap fun t =>
        us.map fun u => ((t.1 * u.1, t.2 ++ u.2) : ℤ × List Nat)).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * (us.map (evalTerm a)).sum := by
  induction ts with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, ih, sum_crossOne,
      List.map_cons, List.sum_cons]
    ring

/-- The guarded right cross-product still sums to `Σ · k` — the dropped branch is exactly `k = 0`. -/
private theorem sum_scaleR_guard (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    (((if k = 0 then ([] : List (ℤ × List Nat))
        else ts.map fun t => ((t.1 * k, t.2) : ℤ × List Nat))).map (evalTerm a)).sum
      = (ts.map (evalTerm a)).sum * k := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, sum_scaleR]

/-- …and the guarded left cross-product. -/
private theorem sum_scaleL_guard (a : Assignment) (k : ℤ) (ts : List (ℤ × List Nat)) :
    (((if k = 0 then ([] : List (ℤ × List Nat))
        else ts.map fun u => ((k * u.1, u.2) : ℤ × List Nat))).map (evalTerm a)).sum
      = k * (ts.map (evalTerm a)).sum := by
  by_cases hk : k = 0
  · simp [hk]
  · simp only [if_neg hk, sum_scaleL]

/-- **The multiplication bridge**: the distributed head means the product of the two heads.
UNCONDITIONAL — the zero-constant guards above drop only branches whose value is `0`. -/
theorem evalH_mulHead (a : Assignment) (h o : Head) :
    evalH (mulHead h o) a = evalH h a * evalH o a := by
  simp only [evalH, mulHead, List.map_append, List.sum_append, sum_cross,
    sum_scaleR_guard, sum_scaleL_guard]
  ring

/-- **`exprToHead`** — normalize a framework gate expression into the `AirBuilder` head vocabulary. -/
def exprToHead : Expr → Head
  | .var v     => Head.lin 1 v
  | .const k   => Head.c k
  | .add e₁ e₂ => (exprToHead e₁).append (exprToHead e₂)
  | .mul e₁ e₂ => mulHead (exprToHead e₁) (exprToHead e₂)

/-- **THE NORMALIZER IS MEANING-PRESERVING.** The head evaluates to exactly what the source
expression evaluated to — so nothing is lost between `EffectSpec2`'s gate algebra and the
builder's normal form. -/
theorem evalH_exprToHead (a : Assignment) (e : Expr) : evalH (exprToHead e) a = e.eval a := by
  induction e with
  | var v => simp [exprToHead, Expr.eval]
  | const k => simp [exprToHead, Expr.eval]
  | add e₁ e₂ ih₁ ih₂ => simp [exprToHead, Expr.eval, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ => simp [exprToHead, Expr.eval, evalH_mulHead, ih₁, ih₂]

/-! ## §2 — lowering a constraint, and the descriptor assembly. -/

/-- The RESIDUAL head of a flat `lhs = rhs` constraint: `lhs − rhs`, the polynomial an AIR gate
asserts vanishes. -/
def constraintHead (c : Constraint) : Head :=
  (exprToHead c.lhs).append ((exprToHead c.rhs).scale (-1))

theorem evalH_constraintHead (a : Assignment) (c : Constraint) :
    evalH (constraintHead c) a = c.lhs.eval a - c.rhs.eval a := by
  simp only [constraintHead, evalH_append, evalH_scale, evalH_exprToHead]
  ring

/-- **`lowerConstraint`** — one framework constraint as a live-IR row gate, emitted THROUGH
`AirBuilder.cgH` (not a raw `.base (.gate …)` literal), so `headToExpr_eval` carries the
semantics. -/
def lowerConstraint (c : Constraint) : VmConstraint2 := cgH (constraintHead c)

/-! ## §2b — ⚑ PHASE 2: lowering the WIDENED vocabulary (`Circuit/EffectAirIR.lean`).

Phase 1 measured that `EffectSpec2`'s flat `ConstraintSystem` reaches 12 of 76 deployed
descriptors and that **51 of the 76 carry a lookup/table leg the source could not name**. These
are the lowerings of the legs `EffectAir` adds. Three of them are total translations; the fourth
is a REFUSAL, and the refusal is the load-bearing part. -/

/-- ⚑ **THE REFUSAL.** A leg the deployed MAIN rail cannot express lowers to a descriptor that
CANNOT BE SATISFIED, never to silence.

Dropping the leg would be the fail-open move: a descriptor missing a constraint accepts strictly
MORE, and no byte-golden and no `Holds`-style denotation can see the loss
(`TableAirIR.rowHolds_of_sublist` is that direction stated as a theorem). Emitting `1 = 0` on BOTH
boundary rows makes it impossible to prove anything about a witness — every non-empty trace has a
first row and a last row, so at least one fires whatever the trace length.

⚠ It is a `.boundary` pair and NOT a `.gate`: `EffectVmEmit.holdsVm_gate_true` makes a `.gate`
VACUOUS on the last row, so a `.gate (const 1)` refusal would be satisfiable by a one-row trace —
a refusal that cannot go red. -/
def refuseConstraints : List VmConstraint2 :=
  [ .base (.boundary VmRow.first (.const 1))
  , .base (.boundary VmRow.last  (.const 1)) ]

/-- **THE REFUSAL BITES.** No row window satisfies both refusal constraints — on a first row the
first fires, on a last row the second does, and every row of a non-empty trace is one or the
other or both. A refusal that some assignment satisfies would be decoration. -/
theorem refuse_bites (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (h : isFirst = true ∨ isLast = true) :
    ¬ (∀ vc ∈ refuseConstraints, vc.holdsAt hash tf env isFirst isLast) := by
  intro hall
  rcases h with h | h
  · have hb := hall _ (List.mem_cons_self)
    have : (1 : ℤ) ≡ 0 [ZMOD P] := hb h
    revert this; decide
  · have hb := hall _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have : (1 : ℤ) ≡ 0 [ZMOD P] := hb h
    revert this; decide

/-- **A LOOKUP leg → the main rail's `Lookup`**, with the tuple carried from the framework's own
gate AST by `CircuitEmit.emitExpr` (structure-preserving, `emitExpr_eval`-faithful) rather than
through the `Head` normalizer: a lookup tuple is not a polynomial asserted to vanish, it is the
tuple looked up, and normalizing it would change the wire bytes without changing its meaning.

⚠ `mainRailOk` REFUSES a non-unit multiplicity and any side but `.query`: `DescriptorIR2.Lookup`
carries neither field, because `Ir2Air::Main` pushes every declared lookup at multiplicity 1. That
is not a hole in this pass — it is the seam where a padded/served leg belongs to a `TableAir`. -/
def lowerLookupLeg (l : LookupLeg) : List VmConstraint2 :=
  if l.mainRailOk then [.lookup ⟨l.table, l.tuple.map emitExpr⟩] else refuseConstraints

/-- **A `WindowExpr` read against the CURRENT ROW ONLY**, or `none` when it reads the next row.
`VmConstraint.boundary`'s body is an `EmittedExpr` evaluated at `env.loc`; there is no next-row
leaf in that target at all, so the conversion is genuinely partial and says so. -/
def windowToLocal? : WindowExpr → Option EmittedExpr
  | .loc c   => some (.var c)
  | .nxt _   => none
  | .const k => some (.const k)
  | .add a b =>
      match windowToLocal? a, windowToLocal? b with
      | some x, some y => some (.add x y)
      | _, _ => none
  | .mul a b =>
      match windowToLocal? a, windowToLocal? b with
      | some x, some y => some (.mul x y)
      | _, _ => none

/-- **The row-local conversion is MEANING-PRESERVING.** When it succeeds, the boundary body
evaluates against `env.loc` to exactly what the window expression evaluated to — so a `.first`/
`.last` leg's lowered form denotes its source. -/
theorem windowToLocal_eval (env : VmRowEnv) :
    ∀ (w : WindowExpr) (e : EmittedExpr), windowToLocal? w = some e →
      e.eval env.loc = w.eval env := by
  intro w
  induction w with
  | loc c => intro e h; simp only [windowToLocal?, Option.some.injEq] at h; subst h; rfl
  | nxt c => intro e h; simp [windowToLocal?] at h
  | const k => intro e h; simp only [windowToLocal?, Option.some.injEq] at h; subst h; rfl
  | add a b iha ihb =>
      intro e h
      simp only [windowToLocal?] at h
      cases h1 : windowToLocal? a with
      | none => rw [h1] at h; simp at h
      | some x =>
        cases h2 : windowToLocal? b with
        | none => rw [h1, h2] at h; simp at h
        | some y =>
          rw [h1, h2] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [EmittedExpr.eval, WindowExpr.eval, iha x h1, ihb y h2]
  | mul a b iha ihb =>
      intro e h
      simp only [windowToLocal?] at h
      cases h1 : windowToLocal? a with
      | none => rw [h1] at h; simp at h
      | some x =>
        cases h2 : windowToLocal? b with
        | none => rw [h1, h2] at h; simp at h
        | some y =>
          rw [h1, h2] at h
          simp only [Option.some.injEq] at h
          subst h
          simp only [EmittedExpr.eval, WindowExpr.eval, iha x h1, ihb y h2]

/-- **A ROW-SELECTED gate leg → its main-rail form.** The four-way `RowSel` meets a target that has
only TWO shapes, and the dispatch is the whole content:

* `.transition` → `windowGate ⟨body, true⟩` — the only scope where `nxt` is the genuine successor.
* `.all`        → `windowGate ⟨body, false⟩`, but only for a body that does NOT read `nxt`
  (`TableAirIR`'s refusal: on the last row p3's `next` is the WRAP row).
* `.first`/`.last` → `.base (.boundary VmRow.first/last body)` at the row-local body.

⚑ A `.all → .transition` re-scope is byte-identical algebra that accepts STRICTLY MORE
(`TableAirIR.TableGate.transition_weakens` + `transition_strictly_weaker`), which is why the
selector is carried in the source at all rather than inferred from the body. -/
def lowerWindowLeg (w : WindowLeg) : List VmConstraint2 :=
  match w.sel with
  | .transition => [.windowGate ⟨w.body, true⟩]
  | .all =>
      match windowToLocal? w.body with
      | some _ => [.windowGate ⟨w.body, false⟩]
      | none   => refuseConstraints
  | .first =>
      match windowToLocal? w.body with
      | some b => [.base (.boundary VmRow.first b)]
      | none   => refuseConstraints
  | .last =>
      match windowToLocal? w.body with
      | some b => [.base (.boundary VmRow.last b)]
      | none   => refuseConstraints

/-- **A PI-PIN leg → the boundary pin.** `AirBuilder.pinPi` covers only the FIRST row; the deployed
boundary contracts pin both ends, which is capability (d). -/
def lowerPiPinLeg (p : PiPinLeg) : VmConstraint2 := .base (.piBinding p.row p.col p.idx)

/-- **A RANGE leg → the v1 range carrier** the row denotation evaluates (`VmRange.holds`). -/
def lowerRangeLeg (r : RangeLeg) : VmRange := ⟨r.wire, r.bits⟩

/-- ⚑ **A LIMBED-QUANTITY leg → ONE range lookup PER LIMB**, against the leg's declared table.

This is the whole lowering, and its shape is the point: a limbed quantity is not one wider check, it
is `k` checks at a width the field can actually enforce. `LimbsLeg.mainRailOk` refuses an empty
vector (which would check nothing while denoting `0`) and any limb width above the wrap-free ceiling
29 — the class `RangeFieldContainment` found three shipped descriptors sitting in — and an ill-formed
leg lowers to the UNSATISFIABLE pair, never to silence. -/
def lowerLimbsLeg (l : LimbsLeg) : List VmConstraint2 :=
  if l.mainRailOk then l.cols.map (fun c => .lookup ⟨l.table, [.var c]⟩) else refuseConstraints

/-- ⚑ **A CHALLENGE leg → the target's `chalGate`** (2026-08-05). `.transition` and `.all` map onto
the target's `onTransition` flag; `.first`/`.last` have NO image (the target's challenge form is
two-row only) and lower to the UNSATISFIABLE pair rather than being quietly relocated to an
every-row gate. `ChalLeg.mainRailOk` is the same verdict, decidable, one stage earlier. -/
def lowerChalLeg (c : ChalLeg) : List VmConstraint2 :=
  match c.sel with
  | .transition => [.chalGate ⟨c.body, true⟩]
  | .all        => if chalReadsNext c.body then refuseConstraints else [.chalGate ⟨c.body, false⟩]
  | .first      => refuseConstraints
  | .last       => refuseConstraints

/-- ⚑ **A RECURSION-BIND leg → the target's `proofBind`** (2026-08-05). The lane vectors are emitted
lane by lane through `emitExpr` — the same wire form every gate body takes — and the declared pins
travel as they are. A leg `BindLeg.mainRailOk` refuses lowers to the UNSATISFIABLE pair rather than
being emitted: that covers the `ProofBind.isDeclarative` shape (pins neither program nor
commitment, so its existential quantifies over every program), a seam NARROWER than
`PROOF_BIND_MIN_LANES` (a limb tie, `2^31`), and a pin that names fewer lanes than the vector it
pins. A compiled descriptor can declare none of the three. -/
def lowerBindLeg (b : BindLeg) : List VmConstraint2 :=
  if b.mainRailOk then
    [.proofBind ⟨emitExpr b.guard, b.commit.map emitExpr, b.vk.map emitExpr, b.vkPin,
                 b.bound.map emitExpr⟩]
  else refuseConstraints

/-- **One leg → its main-rail constraints.** A gate goes through the SAME `Head` normalizer the
spec's own `guardGates` do — the source has one gate language, not two. -/
def lowerLeg : AirLeg → List VmConstraint2
  | .gate c   => [lowerConstraint c]
  | .lookup l => lowerLookupLeg l
  | .window w => lowerWindowLeg w
  | .pin p    => [lowerPiPinLeg p]
  | .limbs l  => lowerLimbsLeg l
  | .chal c   => lowerChalLeg c
  | .bind b   => lowerBindLeg b

/-- **The air block's constraints, IN THE ORDER THE SOURCE DECLARED THEM.**

⚑ The order is the source's, not a fixed gate/lookup/window/pin sequence: the target's
`constraints` is one ordered array and the deployed descriptors interleave
(`merkle-membership-depth2.json` is lookup · lookup · gate · pi_binding · boundary). Emitting a
fixed sequence would make the source unable to say what the target admits — measured at **4 of the
76 by-name descriptors byte-reachable with a fixed order against 8 with this one.** -/
def lowerAirLegs (air : EffectAir) : List VmConstraint2 := air.legs.flatMap lowerLeg

/-- One leg contributes AT LEAST one constraint — so a leg can never vanish silently, and the
emitted length is a real pin on the leg list. -/
theorem lowerLeg_ne_nil (l : AirLeg) : lowerLeg l ≠ [] := by
  cases l with
  | gate c => simp [lowerLeg]
  | pin p => simp [lowerLeg]
  | bind b =>
      by_cases h : b.mainRailOk <;> simp [lowerLeg, lowerBindLeg, h, refuseConstraints]
  | lookup l =>
      by_cases h : l.mainRailOk <;> simp [lowerLeg, lowerLookupLeg, h, refuseConstraints]
  | limbs l =>
      -- ⚑ A limbed quantity contributes ONE LOOKUP PER LIMB, and `mainRailOk` already refuses the
      -- empty vector — so the "at least one constraint" floor holds on both branches, and an
      -- emptied limb list cannot slip through as a leg that checks nothing.
      by_cases h : l.mainRailOk
      · have hne : l.cols ≠ [] := by
          intro hc
          rw [LimbsLeg.mainRailOk, hc] at h
          simp at h
        simp [lowerLeg, lowerLimbsLeg, h, hne]
      · simp [lowerLeg, lowerLimbsLeg, h, refuseConstraints]
  | chal c =>
      -- ⚑ The CHALLENGE leg (2026-08-05). Every branch of `lowerChalLeg` is non-empty by
      -- construction: `.transition` and the reads-next-free `.all` emit one `chalGate`, and the
      -- three refusing branches emit the two-element `refuseConstraints`. So the floor holds
      -- without any hypothesis, and a challenge leg cannot be the one that vanishes silently.
      cases hs : c.sel
      case transition => simp [lowerLeg, lowerChalLeg, hs]
      case all =>
        by_cases h : chalReadsNext c.body <;>
          simp [lowerLeg, lowerChalLeg, hs, h, refuseConstraints]
      case first => simp [lowerLeg, lowerChalLeg, hs, refuseConstraints]
      case last => simp [lowerLeg, lowerChalLeg, hs, refuseConstraints]
  | window w =>
      cases hs : w.sel
      case all =>
        cases hb : windowToLocal? w.body <;>
          simp [lowerLeg, lowerWindowLeg, hs, hb, refuseConstraints]
      case first =>
        cases hb : windowToLocal? w.body <;>
          simp [lowerLeg, lowerWindowLeg, hs, hb, refuseConstraints]
      case last =>
        cases hb : windowToLocal? w.body <;>
          simp [lowerLeg, lowerWindowLeg, hs, hb, refuseConstraints]
      case transition => simp [lowerLeg, lowerWindowLeg, hs]

/-- The EMPTY air block contributes nothing — the additivity fact every existing `EffectSpec2`
instance rides on. -/
theorem lowerAirLegs_empty : lowerAirLegs {} = [] := rfl

/-- **The descriptor assembler**, shared by both entry points. `cs` is normalized through the
`Head` builder; the air legs are lowered by §2b; `framePins` is whatever commitment surface the
caller adds on top (the full-state entry adds `PIBindsDigests`, the bare-AIR entry adds nothing). -/
def assemble (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem) (air : EffectAir)
    (framePins : List VmConstraint2) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := traceWidth
  , piCount     := piCount
  , tables      := air.tables
  , constraints := cs.map lowerConstraint ++ lowerAirLegs air ++ framePins
  , hashSites   := []
  , ranges      := air.ranges.map lowerRangeLeg }

/-- **`lowerAir` — the BARE-AIR entry point (Phase 2).** A descriptor that is NOT a full-state
effect: gates + the widened air block, and no `EffectCommit2` commitment surface at all.

⚑ This is the honest entry for a deployed descriptor that has no digest wires. Adding the
framework's six `PIBindsDigests` pins to `dregg-dfa-routing-table::exact-public-v1` would not make
the lowering better; it would make it emit a descriptor nobody deployed. What the shared code
guarantees is that `lowerAir` and `lowerEffect` differ ONLY in that surface — same normalizer, same
leg lowerings, same emission order. -/
def lowerAir (name : String) (traceWidth piCount : Nat) (cs : ConstraintSystem) (air : EffectAir) :
    EffectVmDescriptor2 :=
  assemble name traceWidth piCount cs air []

/-! ## §3 — two-sided faithfulness of the pass.

The deployed row denotation is mod-`p` (`VmConstraint.holdsVm` on a `.gate` asserts
`body ≡ 0 [ZMOD 2013265921]`); the framework's is ℤ equality. So the two directions are NOT
symmetric and we do not pretend they are: the emission direction is free, the soundness direction
carries the deployed canonicality envelope. -/

theorem sub_modEq_zero_iff {x y : ℤ} : (x - y ≡ 0 [ZMOD P]) ↔ (x ≡ y [ZMOD P]) := by
  constructor
  · intro h; simpa using Int.ModEq.add_right y h
  · intro h; simpa using Int.ModEq.sub_right y h

/-- The deployed range discipline lifts a mod-`p` congruence to ℤ equality. Same shape (and same
`omega` step) as `EffectVmEmitTransfer.not_modEq_zero_of_canon`. -/
theorem eq_of_modEq_canon {x y : ℤ} (hx0 : 0 ≤ x) (hx1 : x < P) (hy0 : 0 ≤ y) (hy1 : y < P)
    (h : x ≡ y [ZMOD P]) : x = y := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  -- `P` is an `abbrev`; restate at the literal so `omega` sees the coefficient.
  have hx1' : x < 2013265921 := hx1
  have hy1' : y < 2013265921 := hy1
  have hk' : y - x = 2013265921 * k := hk
  omega

/-- A lowered gate on a TRANSITION row IS the source constraint, read mod `p`. This is the whole
content of the lowering, and it is proved once here rather than per effect. -/
theorem lowerConstraint_holdsAt_iff (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst : Bool) (c : Constraint) :
    (lowerConstraint c).holdsAt hash tf env isFirst false
      ↔ (c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD P]) := by
  show ((headToExpr (constraintHead c)).eval env.loc ≡ 0 [ZMOD P]) ↔ _
  rw [headToExpr_eval, evalH_constraintHead, sub_modEq_zero_iff]

end Dregg2.Circuit.Emit.EffectLower
