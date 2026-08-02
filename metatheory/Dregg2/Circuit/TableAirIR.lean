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

/-- …and a WHOLE CONCRETE TRACE's verdict is decidable too, via `Nat.decidableBallLT`. This is what
lets a multi-row false-pole witness — the shape every cross-row claim needs — be exhibited against
the EMITTED gate list rather than against a transcription of it.

⚠ `Coherent` is NOT decidable and deliberately has no instance: it equates two `Nat → ℤ`
FUNCTIONS, which no `decide` can settle. A witness must discharge it by `rfl`/`funext`, which is
the honest cost of the hypothesis rather than a gap in it. -/
instance TableAir.instDecidableHolds (t : TableAir) (rows : List VmRowEnv) :
    Decidable (t.Holds rows) :=
  inferInstanceAs (Decidable (∀ i, ∀ h : i < rows.length,
    t.RowHolds rows[i] (decide (i = 0)) (decide (i + 1 = rows.length))))

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

/-! ### §6b — The CANONICAL-SPLIT and LEX-COMPARATOR gadgets, emitted.

⚠ **HOISTED, and for the reason §6 already names.** These were `MapAbsentTableEmit`'s private
emitters in the second pass. The universal-memory BOUNDARY is the second table to need them, and a
per-table copy of a comparator is exactly the drift this file exists to prevent — the more so
because the boundary asserts the SAME three branch equations under a DIFFERENT row selector, which
is precisely the transcription a copy would get wrong invisibly (`TableGate.transition_weakens`).

They are the Lean authors of the Rust `eval_canon_decomp` and `eval_lex_lt`, fixed at the deployed
`KEY_LO_BITS = 27` geometry (both consumers use it; the memory tables use the §6 emitter at 30). -/

/-- `KEY_LO_BITS`. -/
def KEY_LO_BITS : Nat := 27
/-- `KEY_HI_BASE = 2 ^ KEY_LO_BITS` — the canonical split base. -/
def KEY_HI_BASE : ℤ := 134217728
/-- `KEY_HI_MAX = 15`: `p − 1 = 15 · 2^27`, which is what makes the split UNIQUE. -/
def KEY_HI_MAX : ℤ := 15
/-- `MA_DECOMP_COLS` — `[hi4, lo27 limbs, is15, inv15]`. -/
def CANON_COLS : Nat := 1 + decompCols KEY_LO_BITS + 2
/-- `MA_CMP_COLS` — `[s, dhi, dlo, dlo limbs]`. -/
def CMP_COLS : Nat := 3 + decompCols KEY_LO_BITS

#guard CANON_COLS == 13
#guard CMP_COLS == 13
#guard KEY_HI_MAX * KEY_HI_BASE == 2013265921 - 1

/-- `hi4` of a canonical-decomposition block. -/
def canonHi (b0 : Nat) : WindowExpr := v b0
/-- `lo27 = value − hi4 · 2^27`. -/
def canonLo (ve : WindowExpr) (b0 : Nat) : WindowExpr :=
  eSub ve (.mul (v b0) (k KEY_HI_BASE))

/-- The gates of one CANONICAL decomposition `value = hi4·2^27 + lo27` over the 13-column block at
`b0`, gated by `gate`. The last is the UNIQUENESS TOOTH `is15 · lo27 = 0`. -/
def canonDecompGates (ve : WindowExpr) (b0 : Nat) (gate : WindowExpr) : List WindowExpr :=
  decompGates KEY_LO_BITS (canonLo ve b0) (b0 + 1) ++
  [ gBool (b0 + 1 + decompCols KEY_LO_BITS)
  , .mul (eSub (v b0) (k KEY_HI_MAX)) (v (b0 + 1 + decompCols KEY_LO_BITS))
  , eSub (.mul (eSub (v b0) (k KEY_HI_MAX)) (v (b0 + 2 + decompCols KEY_LO_BITS)))
         (eSub gate (v (b0 + 1 + decompCols KEY_LO_BITS)))
  , .mul (v (b0 + 1 + decompCols KEY_LO_BITS)) (canonLo ve b0) ]

/-- The queries of one canonical decomposition: the `hi4` nibble, then the low limbs. -/
def canonDecompQueries (byteBus : String) (b0 : Nat) (mult : WindowExpr) : List BusInteraction :=
  ⟨byteBus, .query, mult, [v b0]⟩ :: decompQueries KEY_LO_BITS byteBus (b0 + 1) mult

/-- The ROW-LOCAL half of a lex comparator block: the branch selector's boolean and the `dlo`
range decomposition. Always `.all`-scoped in both consumers. -/
def lexLtRowLocalGates (b0 : Nat) : List WindowExpr :=
  gBool b0 :: decompGates KEY_LO_BITS (v (b0 + 2)) (b0 + 3)

/-- ⚑ The three BRANCH equations of a lex comparator, split out from the row-local half because
the two deployed consumers assert them under DIFFERENT selectors: `MapAbsent` compares two columns
of ONE row (`.all`), the universal boundary compares a row against its SUCCESSOR (`.transition`,
the Rust `transition_only` flag). Keeping them in one list would have forced the second consumer to
re-derive the algebra beside a different filter. -/
def lexLtBranchGates (aHi aLo bHi bLo : WindowExpr) (b0 : Nat) (gate : WindowExpr) :
    List WindowExpr :=
  [ eSub (v (b0 + 1)) (.mul (.mul gate (v b0)) (eSub (eSub bHi aHi) (k 1)))
  , .mul (.mul gate (eOneMinus (v b0))) (eSub bHi aHi)
  , eSub (v (b0 + 2)) (.mul (.mul gate (eOneMinus (v b0))) (eSub (eSub bLo aLo) (k 1))) ]

/-- The gates of one lexicographic STRICT-LT `a < b`, all at one selector — the `MapAbsent` shape.
`s = 1` ⇒ `bHi ≥ aHi + 1` (witness `dhi`, a nibble); `s = 0` ⇒ `bHi = aHi` and `bLo ≥ aLo + 1`
(witness `dlo`, 27-bit). -/
def lexLtGates (aHi aLo bHi bLo : WindowExpr) (b0 : Nat) (gate : WindowExpr) : List WindowExpr :=
  lexLtRowLocalGates b0 ++ lexLtBranchGates aHi aLo bHi bLo b0 gate

/-- The queries of one lex comparator: the `dhi` nibble, then the `dlo` limbs. -/
def lexLtQueries (byteBus : String) (b0 : Nat) (mult : WindowExpr) : List BusInteraction :=
  ⟨byteBus, .query, mult, [v (b0 + 1)]⟩ :: decompQueries KEY_LO_BITS byteBus (b0 + 3) mult

-- Per-gadget contributions, so a regression names the gadget rather than a total.
#guard (canonDecompGates (v 0) 100 (v 1)).length == 9
#guard (canonDecompQueries "b" 100 (k 1)).length == 7
#guard (lexLtRowLocalGates 100).length == 6
#guard (lexLtBranchGates (v 0) (v 1) (v 2) (v 3) 100 (v 4)).length == 3
#guard (lexLtGates (v 0) (v 1) (v 2) (v 3) 100 (v 4)).length == 9
#guard (lexLtQueries "b" 100 (k 1)).length == 7

-- Per-geometry contributions, so a regression names the width rather than the total.
#guard (decompGates 30 (v 0) 100).length == 4
#guard (decompQueries 30 "b" 100 (k 1)).length == 7
#guard (decompGates 27 (v 0) 100).length == 5
#guard (decompQueries 27 "b" 100 (k 1)).length == 6

/-! ### §6c — The CHIP-BUS TUPLE gadgets, emitted.

⚠ **HOISTED, and for the reason §6 and §6b already name.** `group8` / `leafTuple` / `node8Tuple`
were `MapAbsentTableEmit`'s private emitters. `MapOps` is the SECOND table to fold a Merkle path
through the arity-16 `node8` compression, and a per-table copy of a direction-mixed tuple is exactly
the drift this file exists to prevent — the more so because `MapOps` alone folds FOUR paths over TWO
independent sibling/direction blocks, so a copy would have to be right five times rather than once.

These are the Lean authors of the Rust `chip_absorb_tuple` (the `MapOps` arm's local closure, itself
the twin of `DescriptorIR2.chipLookupTuple`) and `node8_lookup_tuple` (`descriptor_ir2.rs`).

⚑ The two chip geometries are taken from `DescriptorIR2` rather than re-declared: a table AIR and a
main descriptor query the SAME chip bus, so a second copy of `CHIP_RATE` here would be a second
authority on what a chip row looks like. -/

/-- `CHIP_OUT_LANES` — the 8-felt digest group every Merkle lane rides at. -/
def LANES : Nat := Dregg2.Circuit.DescriptorIR2.CHIP_OUT_LANES
/-- `CHIP_RATE` — the padded input-lane count of a chip absorb tuple. -/
def RATE : Nat := Dregg2.Circuit.DescriptorIR2.CHIP_RATE
/-- `CHIP_NODE8_ARITY` — the full-width `perm(L8 ‖ R8)` compression arity. -/
def NODE8_ARITY : ℤ := 16

#guard LANES == 8
#guard RATE == 16

/-- The 8-felt digest group at `base`. -/
def group8 (base : Nat) : List WindowExpr := (List.range LANES).map (fun i => v (base + i))

/-- The chip ABSORB tuple `[arity, padTo RATE ins, out0..out7]` (25 wide) — the Lean twin of the
Rust `chip_absorb_tuple`. ⚑ The arity tag is DATA (`ins.length`), not a hardcoded constant: a wider
leaf extends the declared column list and changes NOTHING else here, which is the property the Rust
closure's own doc claims and which a per-table copy would quietly lose.

⚠ `ins.length` must be one of `CHIP_ADMITTED_ARITIES` — the deployed chip's degree-7 admission
product has exactly seven roots and `≤ RATE` is strictly weaker (`DescriptorIR2`, the arity note). -/
def chipAbsorbTuple (ins : List Nat) (digest : Nat) : List WindowExpr :=
  k (ins.length : ℤ) ::
    (ins.map v ++ (List.range (RATE - ins.length)).map (fun _ => k 0) ++ group8 digest)

/-- The arity-16 `node8` compression tuple `[16, L8, R8, out8]` (25 wide), with
`L8 = (1−dir)·cur + dir·sib` and `R8 = (1−dir)·sib + dir·cur` — the Lean twin of the Rust
`node8_lookup_tuple`, and the in-circuit face of `heap_node8` / `recomposeUp8`.

⚠ The direction MIX is what costs the tuple its SECOND degree, and it is why `ir2_degree_budget`
reads 4 rather than 3 on every table that folds a path. -/
def node8Tuple (curBase sibBase outBase dirC : Nat) : List WindowExpr :=
  let d : WindowExpr := v dirC
  k NODE8_ARITY ::
  ((List.range LANES).map (fun i =>
      .add (.mul (eOneMinus d) (v (curBase + i))) (.mul d (v (sibBase + i)))) ++
   (List.range LANES).map (fun i =>
      .add (.mul (eOneMinus d) (v (sibBase + i))) (.mul d (v (curBase + i)))) ++
   group8 outBase)

/-- One level of a Merkle FOLD: the digest group the level reads is the leaf at level 0 and the
chain column block after that; the group it writes is the chain block, except at the last level
where it is the COMMITTED root. Both consumers walk this shape, and stating it once is what makes
`fold_is_a_chain` (below) a property of the emitter rather than of one table's transcription. -/
def foldCurAt (leaf chain0 : Nat) (lvl : Nat) : Nat :=
  if lvl = 0 then leaf else chain0 + LANES * (lvl - 1)

/-- …and the group it WRITES. `depth` is the tree depth; `root` is the committed terminal. -/
def foldOutAt (chain0 root depth : Nat) (lvl : Nat) : Nat :=
  if lvl + 1 = depth then root else chain0 + LANES * lvl

/-- The `depth`-many `node8` queries that fold ONE path from `leaf` to `root`, at multiplicity
`mult`, reading sibling block `sib0` and direction bits `dir0`. -/
def foldQueries (bus : String) (leaf chain0 root sib0 dir0 depth : Nat) (mult : WindowExpr) :
    List BusInteraction :=
  (List.range depth).map (fun lvl =>
    (⟨bus, .query, mult,
      node8Tuple (foldCurAt leaf chain0 lvl) (sib0 + LANES * lvl)
        (foldOutAt chain0 root depth lvl) (dir0 + lvl)⟩ : BusInteraction))

/-- The fold really walks ONE path: level `lvl+1` reads what level `lvl` wrote. A transcription
that short-circuits the path — writing the root early, or re-reading the leaf — is REFUTED by this
rather than merely uncounted. -/
theorem fold_is_a_chain (leaf chain0 root depth lvl : Nat) (h : lvl + 1 < depth) :
    foldOutAt chain0 root depth lvl = foldCurAt leaf chain0 (lvl + 1) := by
  have h0 : ¬ (lvl + 1 = depth) := by omega
  simp [foldOutAt, foldCurAt, h0]

/-- …and it TERMINATES at the committed root. -/
theorem fold_ends_at_root (chain0 root depth : Nat) (h : 0 < depth) :
    foldOutAt chain0 root depth (depth - 1) = root := by
  have : depth - 1 + 1 = depth := by omega
  simp [foldOutAt, this]

/-- …and STARTS at the leaf. -/
theorem fold_starts_at_leaf (leaf chain0 : Nat) : foldCurAt leaf chain0 0 = leaf := by
  simp [foldCurAt]

-- Per-gadget contributions, so a regression names the gadget rather than a total.
#guard (group8 0).length == 8
#guard (chipAbsorbTuple [1, 2, 3] 100).length == 25
#guard (node8Tuple 10 20 30 40).length == 25
#guard (foldQueries "b" 1 2 3 4 5 16 (k 1)).length == 16

/-! ## §7 — ⚠ WHAT THIS TOOL STILL CANNOT EXPRESS: `ExactPublicTable`, PRICED.

Ten of the eleven hand-written `Ir2Air` arms are expressible in the vocabulary above. **One is
not**, and it is priced here rather than discovered mid-port. Measured at source
(`descriptor_ir2.rs`), the arm is:

```rust
Ir2Air::ExactPublicTable { table_id, manifest } => {
    let prep_row = builder.preprocessed().current_slice();
    let entry: Vec<AB::Expr> = prep_row[..manifest.arity].iter().map(|&v| v.into()).collect();
    let pinned: AB::Expr = prep_row[manifest.mult_col()].into();
    let multiplicity: AB::Expr = local[0].into();
    builder.assert_zero(multiplicity.clone() - pinned);
    LookupBus::new(&exact_public_bus_name(*table_id)).table_entry(builder, entry, multiplicity);
}
```

⚑ **The asymmetry is the whole point: that is ONE gate and ONE bus leg — the SMALLEST arm of the
eleven — and it is the one that cannot be ported.** The cost is entirely in the IR, not in the
constraint, which is why it is a tool project rather than a transcription and why starting it
inside a burn-down of transcriptions would have been the wrong shape.

**Four things are missing, in the order they bite.**

1. **A PREPROCESSED-COLUMN LEAF.** `WindowExpr` has `loc`/`nxt` and no `prep c`. ⚠ And
   `WindowExpr` is NOT this file's type — it is `DescriptorIR2`'s, shared with the MAIN
   descriptor's `windowGate`. Adding a constructor there re-reds every match on it on both sides
   (Lean: `eval`, `toJson`, `readsCol`, `readsNext`; Rust: `parse_window_expr`, `eval_expr`,
   `degree`, `max_var`, `window_body_as_local`, `reads_next`), and — because `Ir2Air::Main` has NO
   preprocessed trace — a `prep` leaf reaching a main descriptor must be REFUSED by a new
   fail-closed check, or it panics inside the evaluator. ⓘ **A genuine design fork**, and it should
   be decided before any of the rest: give `TableAir` its OWN expression type (duplicating the
   grammar this file's §5 exists to avoid duplicating) or widen the shared one (poisoning the main
   IR with a leaf it can never serve).

2. **A WAY TO DECLARE THE PREPROCESSED MATRIX.** `check` bounds every column index against `width`;
   a `prep` index lives in a DIFFERENT column space and needs its own declared bound. `TableAir`
   therefore gains a field, the wire format gains a key, and **all six checked-in artifacts
   re-emit** — with `air_fingerprint()` and `verifier_source_closure_fingerprint()` moving, since
   both splice `TABLE_AIR_ARTIFACTS` whole.

3. **PARAMETERIZATION, which the other ten do not need.** This is not one table: it is a FAMILY.
   The arity, the multiplicity column and the bus name (`ir2_exact_public_{table_id}`) all come
   from the DESCRIPTOR, one instance per declared `ExactPublicRows` table, with arity bounded by
   `MAX_EXACT_PUBLIC_ARITY = 64`. So the emitted object is a SCHEMA — `arity → multCol → bus →
   TableAir` — and `Ir2Air::LeanTable(Arc<LeanTableAir>)` must become a variant that carries the
   Lean-authored algebra AND the manifest DATA (`preprocessed_trace` returns a `RowMajorMatrix<F>`
   the manifest materializes; the Lean side authors no values). Emitting 64 fixed artifacts
   instead is not a way out — the bus name still varies with `table_id`.

4. **THE DIFFERENTIAL ORACLE GOES BLIND WITHOUT AN UPGRADE.** ✅ **DONE 2026-08-01, ahead of any
   `prep`-reading emission** — recorded here because the reasoning is what the other three items
   inherit. `table_air_gates_accept` built an EMPTY preprocessed window
   (`RowWindow::from_two_rows(&[], &[])`), and every mutation sweep in this burn-down ran through
   it, so a `prep`-reading table would have been swept against zeros — the instrument reporting a
   clean undetected set while seeing none of the columns the arm is about. ⚑ That is the failure
   this repo's own doctrine names: a gate that cannot go red.

   ⚠ **And the fix is the REFUSAL, not the plumbing.** `descriptor_ir2::ir2_air_gates_accept` now
   takes the preprocessed rows and checks their shape against the AIR's OWN
   `BaseAir::preprocessed_width` — the authority on whether an arm reads them, so a future arm is
   covered without editing the oracle — and REFUSES a mismatch rather than substituting zeros. An
   oracle that zero-filled would not merely be blind: the manifest's first entry is pinned at
   multiplicity 2, so against an all-zero prep row the honest instance reads UNSAT. A substituted
   witness makes BOTH verdicts meaningless, not just one.
   `circuit/tests/ir2_preprocessed_sweep_harness.rs` measures both poles, and it measures the arm
   that already reads preprocessed columns TODAY (`Ir2Air::ExactPublicTable`) rather than a
   hypothetical one — including the fact that every `LeanTableAir` currently declares ZERO
   preprocessed columns, which is what makes the six existing sweeps sound.

**Estimate, said as an estimate and not as a constraint:** one design decision (item 1), a wire
flag day covering seven artifacts and two fingerprints (item 2), and an `Ir2Air` variant reshape
plus a schema-instantiation path (item 3) — item 4 is done. None of it is a reason to leave a
Rust-authored AIR standing — it is the shape of the work, and the work is the next item, not a
deferral. -/

/-! ## §8 — Tripwires: the grammar golden, and both polarities of `RowHolds`. -/

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
