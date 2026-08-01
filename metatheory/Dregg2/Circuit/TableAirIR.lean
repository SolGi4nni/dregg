/-
# `Dregg2.Circuit.TableAirIR` — the missing tool: a TABLE AIR, authored in Lean.

## What was missing, stated exactly

`DescriptorIR2` emits the MAIN instance: `EffectVmDescriptor2` carries the per-row algebra of one
effect's own trace, and `Ir2Air::Main` interprets it. Everything else the deployed prover runs —
`Ir2Air::{Chip, ChipState16, ByteTable, Memory, MemBoundary, MapOps, UMemory, UMemBoundary,
UMemBoundaryCohort}` — is a SECOND kind of AIR: a shared auxiliary TABLE with its own width, its
own column space, and its own bus interactions, whose rows are not the effect's rows. IR-v2 has no
vocabulary for that object, so every one of those AIRs was hand-authored Rust algebra and law #1
(`metatheory/README.md`: *"circuits are emitted from Lean; Rust only INTERPRETS"*) was false of
them.

This file is the vocabulary. A `TableAir` is:

  * a WIDTH (its own column space, indexed from 0 — `WindowExpr.loc c` is column `c` OF THIS
    TABLE, not of the main trace; that is the whole "sub-descriptor at a column offset" content,
    and it is why the interpreter can be a different `Ir2Air` arm rather than a splice), and
  * a list of GATES — each a `WindowExpr` over the current AND next row, carrying the ROW
    SELECTOR it is asserted under, and
  * a list of BUS INTERACTIONS, each carrying a multiplicity EXPRESSION.

## The two fields IR-v2's `Lookup`/`Gate` could not carry

**The multiplicity expression.** `Ir2Air::Main` hardcodes multiplicity `1` on every declared
lookup, because a main row is unconditionally real. A shared table is PADDED — `MapAbsent`'s chip
absorbs ride at multiplicity `is_real`, so a pad row sends zero queries — and a table IR without a
multiplicity expression cannot express the deployed AIR at all.

**The row selector.** ⚑ This is what blocked the other seven and is new in the second pass. Every
remaining shared table is a SORTED or COUNTED table, and every one of them constrains the
relation between ADJACENT rows under a p3 row filter:

```rust
Ir2Air::ByteTable => {
    builder.when_first_row().assert_zero(local[0].into());                     // .first
    builder.when_transition()                                                  // .transition
           .assert_zero(next[0].into() - local[0].into() - AB::Expr::ONE);
    LookupBus::new(BUS_BYTE).table_entry(builder, [local[0]], local[1]);       // .provide
}
```

`MapAbsent` is the ONLY one of the eight that is purely row-local, which is exactly why it was the
one that could be ported against the first-pass IR. `RowSel` and `WindowExpr` (`nxt`) are the
missing halves; `BusOp.provide` is the third.

## The four interaction shapes, named after the Rust calls they lower to

`BusOp` has exactly four constructors so a fifth cannot appear without this file going red:

| `BusOp`   | Rust                                     | meaning                                   |
|-----------|------------------------------------------|-------------------------------------------|
| `.query`  | `LookupBus::lookup_key(b, tuple, mult)`  | ASK: is `tuple` a row of the served table |
| `.provide`| `LookupBus::table_entry(b, tuple, mult)` | SERVE: `tuple` IS a row, consumed `mult`× |
| `.receive`| `PermutationCheckBus::receive(b, t, m)`  | this table CONTRIBUTES `tuple` to a multiset |
| `.send`   | `PermutationCheckBus::send(b, t, m)`     | this table CONSUMES `tuple` from a multiset |

⚠ `.query` and `.provide` are the two SIDES of a `LookupBus` and differ in p3 by the sign of the
count AND by `count_weight` (1 vs 0 — the weight is what makes the served side not itself a
query). A table that `.query`s what it should `.provide` does not merely mis-serve: it makes the
bus unsatisfiable in one direction and vacuous in the other. The distinction is load-bearing and
is why `provide` is a constructor rather than a negated `query`.

⚠ Bus interactions are NOT row-selected. Every deployed table pushes its interactions on the
unfiltered builder (a filtered p3 builder is not an `InteractionBuilder`), and the padding
discipline is carried by the multiplicity EXPRESSION instead. `BusInteraction` therefore has no
`sel` field, and that absence is deliberate.

## What this file does and does not claim

It claims a DENOTATION and a WIRE FORMAT, nothing else. `TableAir.RowHolds` says the gates vanish
on a row window under their selectors; `TableAir.Holds` says that of every row of a trace. The bus
legs are DECLARED, not denoted here: their meaning is the LogUp multiset balance of the whole
batch, which is a property of the assembled instance family and lives with the batch soundness
results, not with one table. That split is deliberate and is the same one `Satisfied2` already
draws between `Gate` and `Lookup` — see the ⚠ in §3. A reader must not take `Holds` for "this
table is sound".

Emitting an AIR from here does not by itself make the AIR right. It makes the AIR's algebra a
Lean object that theorems can be proved ABOUT — which is the thing hand-written Rust cannot be.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.TableAirIR

open Dregg2.Circuit.DescriptorIR2 (WindowExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false

/-! ## §1 — The IR. -/

/-- The bus call shape. Exactly the four the deployed table AIRs use; see the table in the
module doc for the Rust each lowers to. -/
inductive BusOp where
  /-- `LookupBus::lookup_key` — a subset query against a served table. -/
  | query
  /-- `LookupBus::table_entry` — this table SERVES the entry (p3 `count_weight = 0`). -/
  | provide
  /-- `PermutationCheckBus::receive` — a positive multiset contribution. -/
  | receive
  /-- `PermutationCheckBus::send` — a negative multiset contribution. -/
  | send
  deriving Repr, DecidableEq

/-- The stable wire tag. -/
def BusOp.tag : BusOp → String
  | .query => "query" | .provide => "provide" | .receive => "receive" | .send => "send"

/-- Wire tags are collision-free: the JSON tag determines the op. -/
theorem BusOp.tag_injective : Function.Injective BusOp.tag := by
  intro a b h; cases a <;> cases b <;> simp_all [BusOp.tag]

/-- The p3 ROW FILTER a gate is asserted under. Mirrors the four builder forms the deployed
arms use, and nothing else. -/
inductive RowSel where
  /-- Unfiltered `builder.assert_zero` — every row, wrap row included. -/
  | all
  /-- `builder.when_first_row()` — row 0 only. -/
  | first
  /-- `builder.when_last_row()` — the final row only. -/
  | last
  /-- `builder.when_transition()` — every row BUT the last; the only place `nxt` is the
  genuine successor rather than the wrap row. -/
  | transition
  deriving Repr, DecidableEq

/-- The stable wire tag. -/
def RowSel.tag : RowSel → String
  | .all => "all" | .first => "first" | .last => "last" | .transition => "transition"

/-- Wire tags are collision-free: the JSON tag determines the selector. A selector confusion is
the one transcription error that changes WHICH ROWS a gate binds without changing its algebra,
so this is pinned rather than assumed. -/
theorem RowSel.tag_injective : Function.Injective RowSel.tag := by
  intro a b h; cases a <;> cases b <;> simp_all [RowSel.tag]

/-- One bus interaction of a table AIR: the named bus, the call shape, the MULTIPLICITY
expression (evaluated per row — this is what `Lookup` lacks and what a padded shared table
needs), and the tuple. Deliberately carries NO `RowSel`: see the module doc. -/
structure BusInteraction where
  /-- The bus name. Matches the Rust `BUS_*` string constants verbatim; a namespaced string
  rather than a `TableId` because the deployed buses (`ir2_p2`, `ir2_byte`, `ir2_map_log`, …)
  outnumber and cross-cut the five-table `TableId` roster. -/
  bus   : String
  op    : BusOp
  /-- Per-row multiplicity. `.const 1` is the unconditional case `Lookup` hardcodes. -/
  mult  : WindowExpr
  tuple : List WindowExpr
  deriving Repr

/-- One gate of a table AIR: a two-row polynomial and the row filter it is asserted under. -/
structure TableGate where
  sel  : RowSel
  body : WindowExpr
  deriving Repr

/-- **A table AIR, authored in Lean.** `width` is this table's OWN column count; every
`WindowExpr.loc c` / `.nxt c` in `gates`/`interactions` reads column `c` of THIS table's
current / next row. -/
structure TableAir where
  name         : String
  width        : Nat
  /-- Row-filtered gates: each expression must VANISH on every row its selector admits (the
  Rust `builder.<filter>().assert_zero(..)`). -/
  gates        : List TableGate
  interactions : List BusInteraction

/-! ## §2 — Denotation.

A row of a table trace is a WINDOW: the current row, its successor, and the two boundary tags
p3's filters read. `VmRowEnv` (`Emit.EffectVmEmit`) is that window — `loc`/`nxt`/`pub`, with
`pub` unused here because a shared table has no public inputs. -/

/-- The gate holds on one row window, under its selector. The four cases are exactly p3's four
filters: `.all` fires everywhere, `.first`/`.last` only on their boundary row, `.transition`
everywhere but the last (which is the only scope where `nxt` is the genuine successor). -/
def TableGate.holdsAt (g : TableGate) (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  match g.sel with
  | .all        => g.body.eval env ≡ 0 [ZMOD 2013265921]
  | .first      => isFirst = true  → g.body.eval env ≡ 0 [ZMOD 2013265921]
  | .last       => isLast  = true  → g.body.eval env ≡ 0 [ZMOD 2013265921]
  | .transition => isLast  = false → g.body.eval env ≡ 0 [ZMOD 2013265921]

/-- The gates hold on ONE row window. -/
def TableAir.RowHolds (t : TableAir) (env : VmRowEnv) (isFirst isLast : Bool) : Prop :=
  ∀ g ∈ t.gates, g.holdsAt env isFirst isLast

/-- ⚑ **A GATE'S VERDICT ON A CONCRETE WINDOW IS DECIDABLE**, and that is what lets an emitter
exhibit BOTH poles against the EMITTED gate list rather than against a hand-transcribed copy of it.

Without this, a false-pole witness has to be stated over a `structure` of ℤ facts that re-writes
the gate equations by hand — and a re-transcription is exactly the step a cutover is supposed to
delete. Written as a `match` on the literal constructors (not via `unfold` + `split`) so the
instance REDUCES in the kernel, which is what `decide` needs. -/
instance TableGate.instDecidableHoldsAt (g : TableGate) (env : VmRowEnv) (f l : Bool) :
    Decidable (g.holdsAt env f l) :=
  match g with
  | ⟨.all, body⟩ =>
      inferInstanceAs (Decidable (body.eval env ≡ 0 [ZMOD 2013265921]))
  | ⟨.first, body⟩ =>
      inferInstanceAs (Decidable (f = true → body.eval env ≡ 0 [ZMOD 2013265921]))
  | ⟨.last, body⟩ =>
      inferInstanceAs (Decidable (l = true → body.eval env ≡ 0 [ZMOD 2013265921]))
  | ⟨.transition, body⟩ =>
      inferInstanceAs (Decidable (l = false → body.eval env ≡ 0 [ZMOD 2013265921]))

/-- …and therefore so is the whole row verdict, over the emitted gate list. -/
instance TableAir.instDecidableRowHolds (t : TableAir) (env : VmRowEnv) (f l : Bool) :
    Decidable (t.RowHolds env f l) :=
  inferInstanceAs (Decidable (∀ g ∈ t.gates, g.holdsAt env f l))

/-- The gates hold on EVERY row of a trace of `n` row windows: window `i` is FIRST iff `i = 0`
and LAST iff `i + 1 = n`. -/
def TableAir.Holds (t : TableAir) (rows : List VmRowEnv) : Prop :=
  ∀ i, ∀ h : i < rows.length,
    t.RowHolds rows[i] (decide (i = 0)) (decide (i + 1 = rows.length))

/-- ⚑ **COHERENCE — the half `Holds` does not say, and without which every cross-row gate is
worthless.** A `List VmRowEnv` carries an INDEPENDENT `nxt` per window; nothing in `Holds` ties
window `i`'s `nxt` to window `i+1`'s `loc`. p3's trace does tie them (`next` is the row
rotation), so a theorem about a `.transition` gate that omits this hypothesis is about a machine
that does not exist: the prover could satisfy every increment gate with a `nxt` it never commits.

Stated separately rather than folded into `Holds` so that a proof which FORGETS it fails to
apply rather than silently quantifying over incoherent traces. -/
def Coherent (rows : List VmRowEnv) : Prop :=
  ∀ i, ∀ h : i + 1 < rows.length,
    (rows[i]'(Nat.lt_of_succ_lt h)).nxt = rows[i + 1].loc

/-- A table with no gates is satisfied by anything — the shape a vacuity check must exclude. -/
theorem TableAir.rowHolds_of_no_gates (t : TableAir) (h : t.gates = [])
    (env : VmRowEnv) (f l : Bool) : t.RowHolds env f l := by
  intro g hg; rw [h] at hg; cases hg

/-- `RowHolds` is monotone in the gate list: dropping gates cannot turn acceptance into
refusal. The direction a cutover must watch — a re-emission that LOSES a gate accepts strictly
more. -/
theorem TableAir.rowHolds_of_sublist {t u : TableAir} (h : t.gates.Sublist u.gates)
    (env : VmRowEnv) (f l : Bool) (hu : u.RowHolds env f l) : t.RowHolds env f l :=
  fun g hg => hu g (h.mem hg)

/-- ⚑ **A ROW SELECTOR IS A REAL WEAKENING, not bookkeeping.** Re-scoping a gate from `.all` to
`.transition` — the single most likely transcription slip in this cutover, and the one that
leaves the algebra byte-identical — strictly ENLARGES the accepted set: everything the `.all`
gate admits, the `.transition` gate admits too, and (by the refutation below) not conversely.
So a selector drift accepts MORE and cannot be caught by any check that reads the body alone. -/
theorem TableGate.transition_weakens (body : WindowExpr) (env : VmRowEnv) (f l : Bool)
    (h : TableGate.holdsAt ⟨.all, body⟩ env f l) :
    TableGate.holdsAt ⟨.transition, body⟩ env f l := by
  intro _; exact h

/-- …and the weakening is STRICT: on the LAST row a `.transition` gate is vacuous while the
`.all` gate still bites. The witness is the constant-1 body on a last row. -/
theorem TableGate.transition_strictly_weaker :
    ∃ (body : WindowExpr) (env : VmRowEnv) (f l : Bool),
      TableGate.holdsAt ⟨.transition, body⟩ env f l ∧
      ¬ TableGate.holdsAt ⟨.all, body⟩ env f l := by
  refine ⟨.const 1, ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, false, true, ?_, ?_⟩
  · intro h; exact absurd h (by decide)
  · intro h; revert h; unfold TableGate.holdsAt; simp only [WindowExpr.eval]; decide

/-! ## §3 — ⚠ WHAT `Holds` DOES NOT SAY.

`Holds` quantifies over `gates` ONLY. The bus interactions are DECLARED by a `TableAir` and
denoted NOWHERE in this file, because a single interaction has no truth value: its meaning is
the LogUp multiset balance across the WHOLE assembled instance family, which is a property of
the batch (`Satisfied2`'s table legs), not of one AIR.

So `t.Holds rows` is exactly "the row-local algebra vanishes", and a table whose entire content
is bus interactions has a `Holds` that is trivially true. ⚑ That is not hypothetical: the BYTE
table's whole soundness content is one `.provide` leg plus the value-is-the-row-index gates, and
the `.provide` half is invisible to `Holds`. `busCount`/`busCountOn` below make the
non-vacuity question askable rather than leaving it implied. -/

/-- The number of bus interactions a table declares — the count a cutover pins so that a
re-emission dropping a bus leg is visible rather than silently `Holds`-green. -/
def TableAir.busCount (t : TableAir) : Nat := t.interactions.length

/-- The per-bus interaction count, so a pin can name WHICH bus lost a leg. -/
def TableAir.busCountOn (t : TableAir) (b : String) : Nat :=
  (t.interactions.filter (fun i => i.bus == b)).length

/-- The per-OP interaction count. `.query` vs `.provide` is the side of a `LookupBus` a table
sits on; a pin that counts only the bus cannot tell a server from a client. -/
def TableAir.busCountOp (t : TableAir) (b : String) (o : BusOp) : Nat :=
  (t.interactions.filter (fun i => i.bus == b && i.op == o)).length

/-- Interactions on a bus are interactions: the per-bus counts never exceed the total. -/
theorem TableAir.busCountOn_le (t : TableAir) (b : String) : t.busCountOn b ≤ t.busCount := by
  simpa [TableAir.busCountOn, TableAir.busCount] using
    (t.interactions.length_filter_le (fun i => i.bus == b))

/-- The number of gates under a given selector — so a pin names WHICH scope lost a gate. -/
def TableAir.gateCountSel (t : TableAir) (s : RowSel) : Nat :=
  (t.gates.filter (fun g => g.sel == s)).length

/-- Does this expression read column `c`, on either row tag? Decidable, so "no gate reads the
multiplicity column" is a `decide`-able claim about the emitted object rather than a sentence a
reader has to check by eye against 70 constructors. -/
def readsCol : WindowExpr → Nat → Bool
  | .loc c', c => c' == c
  | .nxt c', c => c' == c
  | .const _, _ => false
  | .add a b, c => readsCol a c || readsCol b c
  | .mul a b, c => readsCol a c || readsCol b c

/-- Does this expression read the NEXT row anywhere? The Lean twin of the Rust decoder's
`reads_next`, which is what refuses an `.all`- or `.last`-scoped `nxt` (on the last row p3's
`next` is the WRAP row). -/
def readsNext : WindowExpr → Bool
  | .nxt _ => true
  | .loc _ | .const _ => false
  | .add a b | .mul a b => readsNext a || readsNext b

/-- A table is ROW-LOCAL when no gate reads the next row and every gate is unfiltered — the shape
that needed no selector vocabulary at all, and the property a re-emission of such a table must not
quietly lose (`TableGate.transition_weakens`: a re-scope accepts strictly more). -/
def TableAir.isRowLocal (t : TableAir) : Bool :=
  t.gates.all (fun g => g.sel == .all && !readsNext g.body)

/-! ## §4 — The wire format.

The grammar is `WindowExpr.toJson`'s (`loc`/`nxt`/`const`/`add`/`mul`), which the Rust
`parse_window_expr` already decodes for the main descriptor's `windowGate`. The table AIR adds
the gate wrapper (`sel` + `body`) and the interaction object. The Rust decoder mirrors THIS
renderer, exactly as the v2 decoder mirrors `emitVmJson2`. -/

private def jsonArray {α : Type} (f : α → String) : List α → String
  | []      => "[]"
  | x :: xs => "[" ++ f x ++ (xs.foldl (fun acc y => acc ++ "," ++ f y) "") ++ "]"

/-- Render one gate. -/
def TableGate.toJson (g : TableGate) : String :=
  "{\"sel\":\"" ++ g.sel.tag ++ "\",\"body\":" ++ g.body.toJson ++ "}"

/-- Render one bus interaction. -/
def BusInteraction.toJson (i : BusInteraction) : String :=
  "{\"bus\":\"" ++ i.bus ++ "\",\"op\":\"" ++ i.op.tag ++ "\",\"mult\":" ++ i.mult.toJson ++
  ",\"tuple\":" ++ jsonArray WindowExpr.toJson i.tuple ++ "}"

/-- **`emitTableAirJson`** — the canonical wire string. What the `#guard` golden pins and the
Rust decoder ingests. -/
def emitTableAirJson (t : TableAir) : String :=
  "{\"name\":\"" ++ t.name ++ "\",\"kind\":\"table_air\",\"ir\":2,\"width\":" ++
  toString t.width ++ ",\"gates\":" ++ jsonArray TableGate.toJson t.gates ++
  ",\"interactions\":" ++ jsonArray BusInteraction.toJson t.interactions ++ "}"

/-! ## §5 — Shared authoring sugar.

The shapes every emitter builds. Kept here rather than in one table's file so the second table
to need `a − b` does not re-derive it (`MapAbsentTableEmit` defined these privately in the first
pass; they are hoisted because `ByteTableEmit`, `MemBoundaryTableEmit` and `MemoryTableEmit`
all need them). -/

/-- Current-row column read. -/
def v (c : Nat) : WindowExpr := .loc c
/-- NEXT-row column read. ⚠ Only meaningful under `.transition` (or `.first`); on the last row
p3's `next` is the WRAP row. -/
def n (c : Nat) : WindowExpr := .nxt c
/-- Field constant. -/
def k (z : ℤ) : WindowExpr := .const z
/-- `a − b`, the standard encoding (there is no `sub` node). -/
def eSub (a b : WindowExpr) : WindowExpr := .add a (.mul (.const (-1)) b)
/-- `1 − e`. -/
def eOneMinus (e : WindowExpr) : WindowExpr := eSub (k 1) e
/-- The boolean gate body `c·(c − 1)` — the Rust `x * (x - ONE)`. -/
def gBool (c : Nat) : WindowExpr := .mul (v c) (.add (v c) (k (-1)))

/-- An unfiltered gate. -/
def gAll (e : WindowExpr) : TableGate := ⟨.all, e⟩
/-- A first-row gate. -/
def gFirst (e : WindowExpr) : TableGate := ⟨.first, e⟩
/-- A transition gate. -/
def gTrans (e : WindowExpr) : TableGate := ⟨.transition, e⟩

/-! ## §6 — The byte-limb decomposition gadget, emitted.

This is the Lean author of the Rust `eval_decomp`: `value = Σ limbᵢ·16ⁱ`, the full limbs served
by the shared `[0,16)` byte table and a PARTIAL top limb bound tightly by bit-decomposition.
Parameterised by bit width because the deployed tables use two of them — `MEM_GAP_BITS = 30`
(memory serial gaps and boundary addresses) and `KEY_LO_BITS = 27` (the canonical key split) —
and a per-table copy of this is exactly the drift the first pass warned about. -/

/-- `LIMB_BITS`: the shared limb table is `[0, 16)`, i.e. 4-bit nibbles. -/
def LIMB_BITS : Nat := 4
/-- `2 ^ LIMB_BITS`, the limb weight base. -/
def LIMB_BASE : ℤ := 16

/-- `limb_geom bits = (num_limbs, top_bits)` — the Rust `limb_geom`. -/
def limbGeom (bits : Nat) : Nat × Nat :=
  let m := (bits + LIMB_BITS - 1) / LIMB_BITS
  (m, bits - (m - 1) * LIMB_BITS)

/-- Columns one `bits`-wide decomposition costs — the Rust `decomp_cols`. -/
def decompCols (bits : Nat) : Nat :=
  let (m, top) := limbGeom bits
  m + (if top < LIMB_BITS then top else 0)

-- The two deployed geometries, pinned against the arithmetic that derives them.
#guard limbGeom 30 == (8, 2)
#guard decompCols 30 == 10
#guard limbGeom 27 == (7, 3)
#guard decompCols 27 == 10

/-- `Σ_{i < m} limb_i · 16^i` over the limb block at `limb0`, left-associated exactly as the
Rust `recomposed +=` loop accumulates it (starting from `0`). -/
def recompose (bits : Nat) (limb0 : Nat) : WindowExpr :=
  (List.range (limbGeom bits).1).foldl
    (fun acc i => .add acc (.mul (v (limb0 + i)) (k (LIMB_BASE ^ i))))
    (k 0)

/-- `Σ_{b < top} bit_b · 2^b` over the partial top limb's bit columns, same accumulation. -/
def topRecompose (bits : Nat) (limb0 : Nat) : WindowExpr :=
  (List.range (limbGeom bits).2).foldl
    (fun acc b => .add acc (.mul (v (limb0 + (limbGeom bits).1 + b)) (k (2 ^ b))))
    (k 0)

/-- The GATES of one `bits`-wide decomposition of `ve` over the block at `limb0`: booleans on
the top-limb bits, the top-limb recomposition, then the whole-value recomposition. Emission
order is the Rust loop's. -/
def decompGates (bits : Nat) (ve : WindowExpr) (limb0 : Nat) : List WindowExpr :=
  (List.range (limbGeom bits).2).map (fun b => gBool (limb0 + (limbGeom bits).1 + b)) ++
  [ eSub (topRecompose bits limb0) (v (limb0 + (limbGeom bits).1 - 1))
  , eSub (recompose bits limb0) ve ]

/-- The byte-table QUERIES of one decomposition: the FULL limbs only (the top one is
bit-decomposed instead, which is what makes the bound tight). -/
def decompQueries (bits : Nat) (byteBus : String) (limb0 : Nat) (mult : WindowExpr) :
    List BusInteraction :=
  (List.range ((limbGeom bits).1 - 1)).map
    (fun i => ⟨byteBus, .query, mult, [v (limb0 + i)]⟩)

-- Per-geometry contributions, so a regression names the width rather than the total.
#guard (decompGates 30 (v 0) 100).length == 4
#guard (decompQueries 30 "b" 100 (k 1)).length == 7
#guard (decompGates 27 (v 0) 100).length == 5
#guard (decompQueries 27 "b" 100 (k 1)).length == 6

/-! ## §7 — Tripwires: the grammar golden, and both polarities of `RowHolds`. -/

/-- A tiny table exercising every node of the grammar: gates at three selectors, a next-row
read, all four bus ops, a non-constant multiplicity. -/
def demoTable : TableAir :=
  { name := "demo-table-air"
  , width := 2
  , gates :=
      [ gAll (.mul (v 0) (.add (v 0) (k (-1))))
      , gFirst (v 0)
      , gTrans (eSub (n 0) (.add (v 0) (k 1))) ]
  , interactions :=
      [ ⟨"ir2_byte", .query, k 1, [v 1]⟩
      , ⟨"ir2_byte", .provide, v 1, [v 0]⟩
      , ⟨"ir2_map_log", .receive, v 0, [v 0, v 1]⟩
      , ⟨"ir2_mem_check", .send, .mul (v 0) (v 1), [v 1]⟩ ] }

-- THE WIRE GOLDEN, byte-pinned. The Rust decoder's grammar is THIS string's grammar.
#guard emitTableAirJson demoTable ==
  "{\"name\":\"demo-table-air\",\"kind\":\"table_air\",\"ir\":2,\"width\":2,\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"sel\":\"first\",\"body\":{\"t\":\"loc\",\"c\":0}},{\"sel\":\"transition\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":1}}}}}],\"interactions\":[{\"bus\":\"ir2_byte\",\"op\":\"query\",\"mult\":{\"t\":\"const\",\"v\":1},\"tuple\":[{\"t\":\"loc\",\"c\":1}]},{\"bus\":\"ir2_byte\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":1},\"tuple\":[{\"t\":\"loc\",\"c\":0}]},{\"bus\":\"ir2_map_log\",\"op\":\"receive\",\"mult\":{\"t\":\"loc\",\"c\":0},\"tuple\":[{\"t\":\"loc\",\"c\":0},{\"t\":\"loc\",\"c\":1}]},{\"bus\":\"ir2_mem_check\",\"op\":\"send\",\"mult\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"loc\",\"c\":1}},\"tuple\":[{\"t\":\"loc\",\"c\":1}]}]}"

-- Shape pins: a dropped gate or bus leg moves one of these.
#guard demoTable.gates.length == 3
#guard demoTable.busCount == 4
#guard demoTable.busCountOn "ir2_byte" == 2
#guard demoTable.busCountOp "ir2_byte" .query == 1
#guard demoTable.busCountOp "ir2_byte" .provide == 1
#guard demoTable.gateCountSel .all == 1
#guard demoTable.gateCountSel .transition == 1
-- The two column predicates, both polarities, on a table that exercises `nxt`.
#guard demoTable.isRowLocal == false
#guard readsNext (eSub (n 0) (v 0)) == true
#guard readsNext (gBool 0) == false
#guard readsCol (gBool 0) 0 == true
#guard readsCol (gBool 0) 1 == false

/-- The all-zero window, an interior row (neither first nor last). -/
private def zeroEnv : VmRowEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- NON-VACUITY, the TRUE pole: the boolean gate accepts `0`, and so does the first-row gate;
the transition gate is the one that bites (`nxt 0 = 0 ≠ 0 + 1`), so this row must be read as a
LAST row for the table to accept. -/
theorem demoTable_accepts_zero_at_last : demoTable.RowHolds zeroEnv true true := by
  intro g hg
  simp only [demoTable, gAll, gFirst, gTrans, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> (unfold TableGate.holdsAt; decide)

/-- NON-VACUITY, the FALSE pole — the gate can go RED. A table whose `RowHolds` no assignment
refutes is decoration; this exhibits the refutation. -/
theorem demoTable_refuses_two : ¬ demoTable.RowHolds (⟨fun _ => 2, fun _ => 2, fun _ => 0⟩)
    true true := by
  intro h
  have hx := h ⟨.all, .mul (v 0) (.add (v 0) (k (-1)))⟩ (by simp [demoTable, gAll])
  revert hx
  unfold TableGate.holdsAt
  decide

/-- NON-VACUITY OF THE SELECTOR, the pole a body-only check cannot see: the SAME all-zero
window that the table accepts as a LAST row is REFUSED as an interior row, because the
transition gate then fires. So `RowSel` is load-bearing in this emission, not decoration. -/
theorem demoTable_refuses_zero_at_interior : ¬ demoTable.RowHolds zeroEnv false false := by
  intro h
  have hx := h ⟨.transition, eSub (n 0) (.add (v 0) (k 1))⟩ (by simp [demoTable, gTrans])
  revert hx
  unfold TableGate.holdsAt
  decide

end Dregg2.Circuit.TableAirIR
