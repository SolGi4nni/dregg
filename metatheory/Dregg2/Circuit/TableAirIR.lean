/-
# `Dregg2.Circuit.TableAirIR` — the missing tool: a TABLE AIR, authored in Lean.

## What was missing, stated exactly

`DescriptorIR2` emits the MAIN instance: `EffectVmDescriptor2` carries the per-row algebra of one
effect's own trace, and `Ir2Air::Main` interprets it. Everything else the deployed prover runs —
`Ir2Air::{Chip, ByteTable, Memory, MemBoundary, MapOps, MapAbsent, UMemory, UMemBoundary}` — is a
SECOND kind of AIR: a shared auxiliary TABLE with its own width, its own column space, and its own
bus interactions, whose rows are not the effect's rows. IR-v2 has no vocabulary for that object,
so every one of those eight AIRs is hand-authored Rust algebra and law #1 (`metatheory/README.md`:
*"circuits are emitted from Lean; Rust only INTERPRETS"*) is false of them.

This file is the vocabulary. A `TableAir` is:

  * a WIDTH (its own column space, indexed from 0 — `EmittedExpr.var c` is column `c` OF THIS
    TABLE, not of the main trace; that is the whole "sub-descriptor at a column offset" content,
    and it is why the interpreter can be a different `Ir2Air` arm rather than a splice), and
  * a list of GATES — each an `EmittedExpr` asserted to vanish on every row, and
  * a list of BUS INTERACTIONS, each carrying a multiplicity EXPRESSION.

The multiplicity expression is the part `Lookup` could not say. `Ir2Air::Main` hardcodes
multiplicity `1` on every declared lookup, because a main row is unconditionally real. A shared
table is PADDED — `MapAbsent`'s chip absorbs ride at multiplicity `is_real`, so a pad row sends
zero queries — and a table IR without a multiplicity expression cannot express the deployed AIR at
all. That is the concrete reason this is a new structure rather than a reuse of `Lookup`.

## The three interaction shapes, named after the Rust calls they lower to

There are exactly three bus call shapes in the deployed table AIRs, and `BusOp` has exactly three
constructors so a fourth cannot appear without this file going red:

| `BusOp`   | Rust                                     | meaning                                   |
|-----------|------------------------------------------|-------------------------------------------|
| `.query`  | `LookupBus::lookup_key(b, tuple, mult)`  | ASK: is `tuple` a row of the served table |
| `.receive`| `PermutationCheckBus::receive(b, t, m)`  | this table CONTRIBUTES `tuple` to a multiset |
| `.send`   | `PermutationCheckBus::send(b, t, m)`     | this table CONSUMES `tuple` from a multiset |

## What this file does and does not claim

It claims a DENOTATION and a WIRE FORMAT, nothing else. `TableAir.RowHolds` says the gates vanish
on a row; `TableAir.Holds` says that of every row. The bus legs are DECLARED, not denoted here:
their meaning is the LogUp multiset balance of the whole batch, which is a property of the
assembled instance family and lives with the batch soundness results, not with one table. That
split is deliberate and is the same one `Satisfied2` already draws between `Gate` and `Lookup` —
see the ⚠ in §3. A reader must not take `Holds` for "this table is sound".

Emitting an AIR from here does not by itself make the AIR right. It makes the AIR's algebra a
Lean object that theorems can be proved ABOUT — which is the thing hand-written Rust cannot be.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. NEW file; imports are read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.TableAirIR

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit (Assignment)

set_option autoImplicit false

/-! ## §1 — The IR. -/

/-- The bus call shape. Exactly the three the deployed table AIRs use; see the table in the
module doc for the Rust each lowers to. -/
inductive BusOp where
  /-- `LookupBus::lookup_key` — a subset query against a served table. -/
  | query
  /-- `PermutationCheckBus::receive` — a positive multiset contribution. -/
  | receive
  /-- `PermutationCheckBus::send` — a negative multiset contribution. -/
  | send
  deriving Repr, DecidableEq

/-- The stable wire tag. -/
def BusOp.tag : BusOp → String
  | .query => "query" | .receive => "receive" | .send => "send"

/-- Wire tags are collision-free: the JSON tag determines the op. -/
theorem BusOp.tag_injective : Function.Injective BusOp.tag := by
  intro a b h; cases a <;> cases b <;> simp_all [BusOp.tag]

/-- One bus interaction of a table AIR: the named bus, the call shape, the MULTIPLICITY
expression (evaluated per row — this is what `Lookup` lacks and what a padded shared table
needs), and the tuple. -/
structure BusInteraction where
  /-- The bus name. Matches the Rust `BUS_*` string constants verbatim; a namespaced string
  rather than a `TableId` because the deployed buses (`ir2_p2`, `ir2_byte`, `ir2_map_log`, …)
  outnumber and cross-cut the five-table `TableId` roster. -/
  bus   : String
  op    : BusOp
  /-- Per-row multiplicity. `.const 1` is the unconditional case `Lookup` hardcodes. -/
  mult  : EmittedExpr
  tuple : List EmittedExpr
  deriving Repr

/-- **A table AIR, authored in Lean.** `width` is this table's OWN column count; every
`EmittedExpr.var c` in `gates`/`interactions` reads column `c` of THIS table's row. -/
structure TableAir where
  name         : String
  width        : Nat
  /-- Row-local gates: each expression must VANISH on every row (the Rust
  `builder.assert_zero(..)`). -/
  gates        : List EmittedExpr
  interactions : List BusInteraction

/-! ## §2 — Denotation. -/

/-- The gates hold on ONE row. (`Assignment` is `Nat → ℤ`; the modulus is the deployed
BabyBear prime, matching `WindowConstraint.holdsAt`.) -/
def TableAir.RowHolds (t : TableAir) (a : Assignment) : Prop :=
  ∀ g ∈ t.gates, g.eval a ≡ 0 [ZMOD 2013265921]

/-- The gates hold on EVERY row of a trace. -/
def TableAir.Holds (t : TableAir) (rows : List Assignment) : Prop :=
  ∀ a ∈ rows, t.RowHolds a

/-- A table with no gates is satisfied by anything — the shape a vacuity check must exclude. -/
theorem TableAir.rowHolds_of_no_gates (t : TableAir) (h : t.gates = []) (a : Assignment) :
    t.RowHolds a := by
  intro g hg; rw [h] at hg; cases hg

/-- `RowHolds` is monotone in the gate list: dropping gates cannot turn acceptance into
refusal. The direction a cutover must watch — a re-emission that LOSES a gate accepts strictly
more. -/
theorem TableAir.rowHolds_of_sublist {t u : TableAir} (h : t.gates.Sublist u.gates)
    (a : Assignment) (hu : u.RowHolds a) : t.RowHolds a :=
  fun g hg => hu g (h.mem hg)

/-! ## §3 — ⚠ WHAT `Holds` DOES NOT SAY.

`Holds` quantifies over `gates` ONLY. The bus interactions are DECLARED by a `TableAir` and
denoted NOWHERE in this file, because a single interaction has no truth value: its meaning is
the LogUp multiset balance across the WHOLE assembled instance family, which is a property of
the batch (`Satisfied2`'s table legs), not of one AIR.

So `t.Holds rows` is exactly "the row-local algebra vanishes", and a table whose entire content
is bus interactions has a `Holds` that is trivially true. `interactionsWitness` below makes that
non-vacuity question askable rather than leaving it implied. -/

/-- The number of bus interactions a table declares — the count a cutover pins so that a
re-emission dropping a bus leg is visible rather than silently `Holds`-green. -/
def TableAir.busCount (t : TableAir) : Nat := t.interactions.length

/-- The per-bus interaction count, so a pin can name WHICH bus lost a leg. -/
def TableAir.busCountOn (t : TableAir) (b : String) : Nat :=
  (t.interactions.filter (fun i => i.bus == b)).length

/-- Interactions on a bus are interactions: the per-bus counts never exceed the total. -/
theorem TableAir.busCountOn_le (t : TableAir) (b : String) : t.busCountOn b ≤ t.busCount := by
  simpa [TableAir.busCountOn, TableAir.busCount] using
    (t.interactions.length_filter_le (fun i => i.bus == b))

/-! ## §4 — The wire format.

The grammar is `EmittedExpr.toJson`'s, extended by the two new nodes. The Rust decoder mirrors
THIS renderer, exactly as the v2 decoder mirrors `emitVmJson2`. -/

private def jsonArray {α : Type} (f : α → String) : List α → String
  | []      => "[]"
  | x :: xs => "[" ++ f x ++ (xs.foldl (fun acc y => acc ++ "," ++ f y) "") ++ "]"

/-- Render one bus interaction. -/
def BusInteraction.toJson (i : BusInteraction) : String :=
  "{\"bus\":\"" ++ i.bus ++ "\",\"op\":\"" ++ i.op.tag ++ "\",\"mult\":" ++ i.mult.toJson ++
  ",\"tuple\":" ++ jsonArray EmittedExpr.toJson i.tuple ++ "}"

/-- **`emitTableAirJson`** — the canonical wire string. What the `#guard` golden pins and the
Rust decoder ingests. -/
def emitTableAirJson (t : TableAir) : String :=
  "{\"name\":\"" ++ t.name ++ "\",\"kind\":\"table_air\",\"ir\":2,\"width\":" ++
  toString t.width ++ ",\"gates\":" ++ jsonArray EmittedExpr.toJson t.gates ++
  ",\"interactions\":" ++ jsonArray BusInteraction.toJson t.interactions ++ "}"

/-! ## §5 — Tripwires: the grammar golden, and both polarities of `RowHolds`. -/

/-- A tiny table exercising every node of the grammar: a gate, all three bus ops, a
non-constant multiplicity. -/
def demoTable : TableAir :=
  { name := "demo-table-air"
  , width := 2
  , gates := [.mul (.var 0) (.add (.var 0) (.const (-1)))]
  , interactions :=
      [ ⟨"ir2_byte", .query, .const 1, [.var 1]⟩
      , ⟨"ir2_map_log", .receive, .var 0, [.var 0, .var 1]⟩
      , ⟨"ir2_mem_check", .send, .mul (.var 0) (.var 1), [.var 1]⟩ ] }

-- THE WIRE GOLDEN, byte-pinned. The Rust decoder's grammar is THIS string's grammar.
#guard emitTableAirJson demoTable ==
  "{\"name\":\"demo-table-air\",\"kind\":\"table_air\",\"ir\":2,\"width\":2,\"gates\":[{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}],\"interactions\":[{\"bus\":\"ir2_byte\",\"op\":\"query\",\"mult\":{\"t\":\"const\",\"v\":1},\"tuple\":[{\"t\":\"var\",\"v\":1}]},{\"bus\":\"ir2_map_log\",\"op\":\"receive\",\"mult\":{\"t\":\"var\",\"v\":0},\"tuple\":[{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1}]},{\"bus\":\"ir2_mem_check\",\"op\":\"send\",\"mult\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":1}},\"tuple\":[{\"t\":\"var\",\"v\":1}]}]}"

-- Shape pins: a dropped gate or bus leg moves one of these.
#guard demoTable.gates.length == 1
#guard demoTable.busCount == 3
#guard demoTable.busCountOn "ir2_byte" == 1

/-- NON-VACUITY, the TRUE pole: the boolean gate accepts `0`. -/
theorem demoTable_accepts_zero : demoTable.RowHolds (fun _ => 0) := by
  intro g hg
  simp only [demoTable, List.mem_cons, List.not_mem_nil, or_false] at hg
  subst hg
  decide

/-- NON-VACUITY, the FALSE pole — the gate can go RED. A table whose `RowHolds` no assignment
refutes is decoration; this exhibits the refutation. -/
theorem demoTable_refuses_two : ¬ demoTable.RowHolds (fun _ => 2) := by
  intro h
  have := h (.mul (.var 0) (.add (.var 0) (.const (-1)))) (by simp [demoTable])
  revert this
  decide

end Dregg2.Circuit.TableAirIR
