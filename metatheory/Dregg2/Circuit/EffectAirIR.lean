/-
# `Dregg2.Circuit.EffectAirIR` — the vocabulary `EffectSpec2` was missing.

## The measured finding this file answers

Phase 1 (`Dregg2/Circuit/Emit/EffectLower.lean`, `docs/LOGIC-COMPILER-ASSESSMENT.md` §P1.5) built
`lowerEffect : EffectSpec2 → EffectVmDescriptor2` and then MEASURED that its output reaches only
**12 of the 76** checked-in `circuit/descriptors/by-name/*.json`, because `EffectSpec2` carries
exactly one kind of arithmetic — a flat `ConstraintSystem` of `lhs = rhs` over `Circuit.Expr` — and
the deployed descriptors carry five kinds. The capability ladder, cumulative, over those 76:

    gate + first-row PI                    12 / 76      ← what `EffectSpec2` could say
    + window / boundary / last-row PI       25 / 76
    + LOOKUPS and declared TABLES           76 / 76      ← +51, the whole unlock

**51 of the 76 carry a lookup/table leg and `EffectSpec2` had no name for one.** The gap was never
in the emitter; it was that the SOURCE LANGUAGE could not say the thing. This file is the
vocabulary, and `EffectSpec2` gains ONE field (`air : EffectAir := {}`) that carries it.

## It is TableAirIR's vocabulary, deliberately — not a fourth private copy

`Dregg2/Circuit/TableAirIR.lean` cured the identical disease one layer down (the shared auxiliary
tables had no IR, so every one was hand-authored Rust algebra). Its four hard-won distinctions are
REUSED here rather than re-derived:

  * **`RowSel`** (`.all/.first/.last/.transition`) — the p3 row filter a gate is asserted under.
    `TableGate.transition_weakens` proves re-scoping is a REAL weakening, invisible to any check
    that reads the body alone.
  * **`WindowExpr`** — the current-AND-next-row leaf. ⚠ With TableAirIR's refusal: a `nxt` read is
    only meaningful under `.transition`.
  * **The multiplicity EXPRESSION on a bus interaction** — `Ir2Air::Main` hardcodes multiplicity
    `1`; a padded or conditional query cannot be said without one.
  * **`BusOp.provide` vs `.query`** — the two SIDES of a lookup bus. A table that queries what it
    should serve is unsatisfiable one way and vacuous the other, so this is a constructor, never a
    negated `query`.

## ⚑ WHAT THE MAIN RAIL REFUSES, AND WHY THAT IS THE POINT

`EffectAir` can SAY strictly more than `EffectVmDescriptor2`'s main-instance constraint set can
take, and the two gaps are named here rather than silently dropped:

  1. **A non-unit multiplicity.** `DescriptorIR2.Lookup` is `⟨table, tuple⟩` — no `mult` field at
     all, because `Ir2Air::Main` pushes every declared lookup at multiplicity 1 (a main row is
     unconditionally real). A `LookupLeg` with `mult ≠ 1` has no main-rail image.
  2. **The serving side.** `.provide`/`.receive`/`.send` are the shared-TABLE side of a bus. A main
     descriptor only ever QUERIES. A `LookupLeg` with `op ≠ .query` has no main-rail image.
  3. **A `nxt` read outside `.transition`.** Under `.all` this is TableAirIR's refusal verbatim (on
     the last row p3's `next` is the WRAP row). Under `.first`/`.last` the reason is STRONGER and
     rail-specific: those lower to `VmConstraint.boundary`, whose body is an `EmittedExpr` read
     against `env.loc` ONLY — the target constructor cannot read the next row at all.

`EffectAir.mainRailOk` is the DECIDABLE verdict, so "this spec is expressible on the deployed main
rail" is a `decide`-able claim about the emitted object rather than a sentence a reader checks by
eye. `EffectLower` lowers an ill-formed leg to an UNSATISFIABLE boundary pair — a descriptor that
REFUSES rather than one that quietly asserts less. That direction is the whole discipline: dropping
a leg accepts strictly more, which is the failure a byte-golden cannot see.

The legs that a main descriptor refuses are exactly the legs a `TableAir` takes. That is not a hole
in this file; it is the seam between the two rails, and it is where a padded shared table goes.

## What this file does NOT claim

It is SYNTAX. `EffectAir` has no denotation here: a lookup leg's meaning is the LogUp multiset
balance of the assembled instance (`Satisfied2`'s table legs), a range leg's is `VmRange.holds`, a
window leg's is `WindowConstraint.holdsAt`. All three live with the target IR, and the lowering in
`EffectLower` is where a leg acquires meaning. Carrying a leg does not make an AIR right; it makes
the AIR SAYABLE from the spec, which is the thing that was missing.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Imports read-only; ADDITIVE (the one consumer edit is
`EffectSpec2`'s new defaulted field, which leaves every existing instance compiling).
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.EffectAirIR

open Dregg2.Circuit (Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (TableId TableDef WindowExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.TableAirIR (BusOp RowSel readsNext)

set_option autoImplicit false

/-! ## §1 — the four leg shapes, and the ORDERED list that carries them. -/

/-- **A LOOKUP leg** — the +51 capability. The queried table, the tuple (expressions in the
framework's OWN gate AST `Circuit.Expr`, so a spec author writes the same language the guard gates
are written in), the per-row MULTIPLICITY expression, and which SIDE of the bus this is.

`mult` and `op` are TableAirIR's two fields, carried here even though the deployed MAIN rail takes
neither: a source language that cannot say "this query is conditional" cannot describe a padded
row, and the honest response is a REFUSAL at the lowering (`mainRailOk`), not a vocabulary that
pretends the distinction does not exist. -/
structure LookupLeg where
  table : TableId
  tuple : List Expr
  /-- Per-row multiplicity. `.const 1` is the unconditional case the main rail hardcodes. -/
  mult  : Expr := .const 1
  /-- Which side of the bus. A main descriptor only ever `.query`s. -/
  op    : BusOp := .query

/-- **A ROW-SELECTED gate leg** — TableAirIR's `RowSel` over its `WindowExpr`. This is the (c)
capability: `EffectSpec2` was single-row, so `.transition` continuity, first/last-row boundary
fixes, and two-row window gates were all unsayable. -/
structure WindowLeg where
  sel  : RowSel
  body : WindowExpr

/-- **A RANGE leg** — the (b) capability: a wire pinned into `[0, 2^bits)`. The field-soundness
tooth (`VmRange.holds`); transfer's deployed v1 descriptor carries two and `EffectSpec2` could name
neither. -/
structure RangeLeg where
  wire : Nat
  bits : Nat
  deriving Repr, DecidableEq

/-- **A PI-PIN leg** — the (d) capability. `EffectSpec2`'s lowering could pin only FIRST-row PIs
(the `PIBindsDigests` surface); a deployed boundary contract pins both ends. -/
structure PiPinLeg where
  row : VmRow
  col : Nat
  idx : Nat
  deriving Repr, DecidableEq

/-- **One leg of an effect's AIR** — ⚑ ONE ORDERED LIST, not four parallel ones.

`EffectVmDescriptor2.constraints` is a SINGLE ordered `List VmConstraint2`, and the deployed
descriptors interleave freely (`merkle-membership-depth2.json` is lookup · lookup · gate ·
pi_binding · boundary). A source that held four parallel lists could only ever emit
gates-then-lookups-then-windows-then-pins, so it could not say what the target admits — the same
class of defect this whole phase exists to close, one level down. Measured over the 76 by-name
descriptors: **4 are byte-reachable with parallel lists, 8 with this ordered list.**

`gate` rides here too (not only in the spec's own `guardGates`) so a spec can place a gate
BETWEEN two lookups. -/
inductive AirLeg where
  /-- A flat `lhs = rhs`, lowered through the `Head` NORMALIZER like every other spec gate. -/
  | gate   (c : Constraint)
  | lookup (l : LookupLeg)
  | window (w : WindowLeg)
  | pin    (p : PiPinLeg)

/-- **`EffectAir` — the AIR block an `EffectSpec2` carries beyond its flat guard gates.**

`legs` is ordered because the target's constraint array is. `tables` and `ranges` are separate
because the target's `tables` and `ranges` are separate JSON arrays, not constraints.

Every field defaults to empty, which is what makes the widening ADDITIVE: an existing
`EffectSpec2` instance that names none of these is unchanged, and `lowerEffect` on it emits
byte-identically to Phase 1 (`EffectLower.lowerEffect_air_empty`). -/
structure EffectAir where
  /-- Tables this effect DECLARES (an `exactPublicRows` roster, a chip, a range limb table…). -/
  tables  : List TableDef := []
  /-- The constraint legs, IN EMISSION ORDER. -/
  legs    : List AirLeg   := []
  ranges  : List RangeLeg := []
  /-- PI slots this air block claims BEYOND the framework's own `PIBindsDigests` surface. -/
  extraPi : Nat           := 0

/-! ## §2 — the DECIDABLE main-rail verdict.

Three refusals, each naming the target constructor that cannot hold the source leg. -/

/-- Is this expression the literal constant `1`? (The one multiplicity `Ir2Air::Main` implements.) -/
def exprIsOne : Expr → Bool
  | .const k => k == 1
  | _        => false

/-- ⚑ **The main rail's verdict on ONE lookup leg.** `DescriptorIR2.Lookup` is `⟨table, tuple⟩`:
there is no multiplicity field and no side field, so a leg with either is not expressible. -/
def LookupLeg.mainRailOk (l : LookupLeg) : Bool :=
  (l.op == BusOp.query) && exprIsOne l.mult

/-- ⚑ **The main rail's verdict on ONE window leg**, and the two reasons are different:

* `.transition` — the ONLY scope where `nxt` is the genuine successor. Anything goes.
* `.all` — TableAirIR's refusal: on the last row p3's `next` is the WRAP row.
* `.first` / `.last` — these lower to `VmConstraint.boundary`, whose body evaluates against
  `env.loc` alone. The target has no next-row leaf at all. -/
def WindowLeg.mainRailOk (w : WindowLeg) : Bool :=
  match w.sel with
  | .transition => true
  | .all        => !readsNext w.body
  | .first      => !readsNext w.body
  | .last       => !readsNext w.body

/-- ⚑ **The main rail's verdict on ONE leg.** A `gate` and a `pin` always have an image; a
`lookup` and a `window` may not. -/
def AirLeg.mainRailOk : AirLeg → Bool
  | .gate _   => true
  | .pin _    => true
  | .lookup l => l.mainRailOk
  | .window w => w.mainRailOk

/-- Every declared PI pin indexes a slot the descriptor actually declares. A pin past `piCount`
is a wire-format defect the Rust decoder would read as an out-of-range public input. -/
def EffectAir.pinsFit (air : EffectAir) (piCount : Nat) : Bool :=
  air.legs.all (fun l => match l with | .pin p => p.idx < piCount | _ => true)

/-- **`EffectAir.mainRailOk`** — the decidable verdict that this air block is expressible as
constraints of a deployed MAIN `EffectVmDescriptor2`. -/
def EffectAir.mainRailOk (air : EffectAir) : Bool := air.legs.all AirLeg.mainRailOk

/-! ## §3 — shape counts, so a re-emission that DROPS a leg moves a number.

`TableAirIR.busCount`/`gateCountSel` exist for exactly this reason: a lost bus leg is invisible to
a denotation that quantifies over gates only. Same discipline, same shape. -/

/-- The leg's kind tag — the discriminator the per-kind counts filter on. -/
def AirLeg.kind : AirLeg → String
  | .gate _ => "gate" | .lookup _ => "lookup" | .window _ => "window" | .pin _ => "pin"

/-- Kind tags are collision-free: the tag determines the constructor's arm. -/
theorem AirLeg.kind_of (l : AirLeg) :
    (l.kind = "gate") ∨ (l.kind = "lookup") ∨ (l.kind = "window") ∨ (l.kind = "pin") := by
  cases l <;> simp [AirLeg.kind]

def EffectAir.kindCount   (air : EffectAir) (k : String) : Nat :=
  (air.legs.filter (fun l => l.kind == k)).length
def EffectAir.lookupCount (air : EffectAir) : Nat := air.kindCount "lookup"
def EffectAir.windowCount (air : EffectAir) : Nat := air.kindCount "window"
def EffectAir.gateCount   (air : EffectAir) : Nat := air.kindCount "gate"
def EffectAir.pinCount    (air : EffectAir) : Nat := air.kindCount "pin"
def EffectAir.rangeCount  (air : EffectAir) : Nat := air.ranges.length
def EffectAir.tableCount  (air : EffectAir) : Nat := air.tables.length

/-- The window legs under a given selector — so a pin names WHICH scope lost a gate
(`TableAirIR.gateCountSel`'s counterpart). -/
def EffectAir.windowCountSel (air : EffectAir) (s : RowSel) : Nat :=
  (air.legs.filter (fun l => match l with | .window w => w.sel == s | _ => false)).length

/-- The PI pins on a given row — first-row and last-row pins are different contracts. -/
def EffectAir.pinCountRow (air : EffectAir) (r : VmRow) : Nat :=
  (air.legs.filter (fun l => match l with | .pin p => p.row == r | _ => false)).length

/-- Total legs plus the two separately-carried arrays. `0` exactly on the empty air block. -/
def EffectAir.legCount (air : EffectAir) : Nat :=
  air.legs.length + air.rangeCount + air.tableCount

/-- Per-kind counts never exceed the leg total: a per-kind pin is a refinement of the whole. -/
theorem EffectAir.kindCount_le (air : EffectAir) (k : String) :
    air.kindCount k ≤ air.legs.length := by
  simpa [EffectAir.kindCount] using (air.legs.length_filter_le (fun l => l.kind == k))

/-- **The DEFAULT air block is empty** — the additivity fact the widening rests on. Every
`EffectSpec2` instance that names no air legs carries this, so its lowering is unchanged. -/
theorem EffectAir.default_legCount : ({} : EffectAir).legCount = 0 := rfl

/-- …and the empty block is trivially main-rail expressible (no leg, no refusal). -/
theorem EffectAir.default_mainRailOk : ({} : EffectAir).mainRailOk = true := rfl

/-! ## §4 — tripwires. Both polarities of every refusal, on the EMITTED predicate. -/

/-- An unconditional query — the shape a main descriptor takes. -/
def demoQuery : LookupLeg := ⟨.custom 30, [.var 0, .var 1, .var 2], .const 1, .query⟩

/-- The SAME tuple served rather than asked. No main-rail image: `Lookup` has no side field. -/
def demoProvide : LookupLeg := { demoQuery with op := .provide }

/-- The same query at a CONDITIONAL multiplicity (a padded row sends nothing). No main-rail
image: `Ir2Air::Main` hardcodes multiplicity 1. -/
def demoConditional : LookupLeg := { demoQuery with mult := .var 3 }

#guard demoQuery.mainRailOk == true
#guard demoProvide.mainRailOk == false
#guard demoConditional.mainRailOk == false

/-- A transition continuity leg reading the next row — the legal `nxt` scope. -/
def demoCont : WindowLeg := ⟨.transition, .add (.nxt 0) (.mul (.const (-1)) (.loc 2))⟩

/-- The SAME body re-scoped to `.all`. Byte-identical algebra, and REFUSED: on the last row p3's
`next` is the wrap row. This is `TableGate.transition_weakens` seen from the source side. -/
def demoContAll : WindowLeg := { demoCont with sel := .all }

/-- A row-local boundary fix — no `nxt`, so `.last` is fine. -/
def demoLastFix : WindowLeg := ⟨.last, .add (.loc 5) (.mul (.const (-1)) (.loc 4))⟩

#guard demoCont.mainRailOk == true
#guard demoContAll.mainRailOk == false
#guard demoLastFix.mainRailOk == true
#guard (WindowLeg.mk .first (.nxt 0)).mainRailOk == false

/-- An air block exercising every leg kind, with a `gate` INTERLEAVED between two lookups — the
shape four parallel lists could not express. -/
def demoAir : EffectAir :=
  { tables  := [⟨.custom 30, "dfa_transition_table", 3, .exactPublicRows [[0, 1, 1]]⟩]
  , legs    := [ .lookup demoQuery
                , .gate ⟨.var 4, .const 0⟩
                , .window demoCont
                , .window demoLastFix
                , .pin ⟨.first, 0, 0⟩
                , .pin ⟨.last, 2, 1⟩ ]
  , ranges  := [⟨7, 30⟩]
  , extraPi := 2 }

#guard demoAir.mainRailOk == true
#guard demoAir.legCount == 8
#guard demoAir.legs.length == 6
#guard demoAir.lookupCount == 1
#guard demoAir.gateCount == 1
#guard demoAir.windowCount == 2
#guard demoAir.pinCount == 2
#guard demoAir.windowCountSel .transition == 1
#guard demoAir.windowCountSel .last == 1
#guard demoAir.windowCountSel .all == 0
#guard demoAir.pinCountRow .first == 1
#guard demoAir.pinCountRow .last == 1
#guard demoAir.pinsFit 2 == true
#guard demoAir.pinsFit 1 == false

-- ⚑ THE REFUSAL POLE: one `.provide` leg turns the WHOLE block inexpressible. A verdict that
-- cannot go red is decoration; this is the red.
#guard ({ demoAir with legs := [.lookup demoProvide] } : EffectAir).mainRailOk == false
#guard ({ demoAir with legs := [.window demoContAll] } : EffectAir).mainRailOk == false

-- The default block, both facts, executed rather than asserted.
#guard ({} : EffectAir).legCount == 0
#guard ({} : EffectAir).mainRailOk == true

#assert_axioms AirLeg.kind_of
#assert_axioms EffectAir.kindCount_le
#assert_axioms EffectAir.default_legCount
#assert_axioms EffectAir.default_mainRailOk

end Dregg2.Circuit.EffectAirIR
