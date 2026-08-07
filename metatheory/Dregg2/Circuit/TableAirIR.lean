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

/-! ### §1b — ⚑ `TExpr`: the table grammar, and why it is NOT `WindowExpr`.

The first two passes typed a table's gates at `DescriptorIR2.WindowExpr`, the MAIN descriptor's
`windowGate` type. §7 priced widening it (for a `prep` leaf) against giving `TableAir` its own
grammar and called it a genuine design fork. **It is decided here, and the deciding evidence is a
count plus a fact about `Ir2Air::Main`:**

* `WindowExpr` is named in **120 Lean files / 720 occurrences**, and `windowGate` — the MAIN
  descriptor's constructor — in **110 of them**. The whole table side (this file, the nine
  `*TableEmit.lean`, `Poseidon2RoundGates`) is 213 occurrences across 11 files.
* `Ir2Air::Main` can serve NEITHER of the two leaves a table needs. It has no definition list, so a
  `shr` leaf has nothing to resolve against; it has no preprocessed trace, so a `prep` leaf panics
  inside the evaluator. Widening the shared type therefore puts two permanently-unserviceable
  constructors into a type 110 main-descriptor files construct, and buys a new fail-closed refusal
  on the main decode path for each — a refusal that must then never regress.
* ⚠ And §7's own counter-argument (*"duplicating the grammar this file's §5 exists to avoid
  duplicating"*) does not survive contact: §5/§6 exist to stop TABLES from re-deriving GADGETS from
  each other, and no main-descriptor file imports one. They move with the type in a single edit.

So `TExpr` is `WindowExpr`'s five leaves plus `shr` and `prep`. The wire tags of the shared five are
IDENTICAL, which is what makes the ten existing artifacts re-emit with their gate and interaction
bytes untouched. `WindowExpr` is not modified, and `Ir2Air::Main` never sees this type.

### §1c — ⚑ `prep`: the SECOND leaf the fork was for, and it lands with an emitter.

§7 priced `prep` for `Ir2Air::ExactPublicTable` and DELIBERATELY did not add it, on the rule that *a
constructor with a decoder, a denotation and no emitter is a reference without a referent*. It has
one now: `Emit/ExactPublicTableEmit.lean` emits the whole family and the arm is deleted. `prep c` is
column `c` of THIS ROW of the table's PREPROCESSED matrix — a verifier-RECOMPUTED column space,
disjoint from the committed one, which is why it needs its own declared bound (`TableAir.prepWidth`)
and why `readsCol` — a question about COMMITTED columns — answers `false` on it rather than
conflating the two spaces. -/

/-- **A table AIR's expression.** `loc`/`nxt`/`const`/`add`/`mul` are `WindowExpr`'s, byte for byte
on the wire; `shr i` is the SHARING leaf — the value of the table's `defs[i]`, computed ONCE per row
and reused — and `prep c` reads the PREPROCESSED matrix. -/
inductive TExpr where
  /-- Current-row column `c` of THIS table. -/
  | loc   (c : Nat)
  /-- Next-row column `c` of THIS table. -/
  | nxt   (c : Nat)
  /-- A field constant. -/
  | const (z : ℤ)
  /-- ⚑ **The SHARING leaf**: the already-computed value of `defs[i]`. A `defs` entry may reference
  only STRICTLY EARLIER entries (`TableAir.defsAcyclic`), so the definition list is a topologically
  ordered DAG and one left-to-right pass resolves it. -/
  | shr   (i : Nat)
  /-- ⚑ **The PREPROCESSED leaf**: column `c` of this row of the table's preprocessed matrix.

  A DIFFERENT COLUMN SPACE from `loc`/`nxt`. The preprocessed matrix is not committed by the
  prover — the verifier rebuilds it from the descriptor and commits it itself — so a value read
  here is verifier-known by construction, which is the whole content of an exact-public manifest.
  Bounded by `TableAir.prepWidth`, never by `width`. -/
  | prep  (c : Nat)
  | add   (a b : TExpr)
  | mul   (a b : TExpr)
  deriving Repr

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
  mult  : TExpr
  tuple : List TExpr
  deriving Repr

/-- One gate of a table AIR: a two-row polynomial and the row filter it is asserted under. -/
structure TableGate where
  sel  : RowSel
  body : TExpr
  deriving Repr

/-- **A table AIR, authored in Lean.** `width` is this table's OWN column count; every
`TExpr.loc c` / `.nxt c` in `defs`/`gates`/`interactions` reads column `c` of THIS table's
current / next row. -/
structure TableAir where
  name         : String
  width        : Nat
  /-- ⚑ **THE DECLARED PREPROCESSED WIDTH** — the column count of the matrix `TExpr.prep c` indexes,
  and `0` for a table that reads none.

  It is a SEPARATE bound because it is a separate column space: `width` bounds the committed trace
  the prover writes, `prepWidth` bounds the matrix the VERIFIER rebuilds and commits. Checking a
  `prep` index against `width` would have been a bound in the wrong space — sound-looking on a table
  where the two happen to be close, silently absent where they are not (the exact-public family has
  `width = 1` and `prepWidth = arity + 2`). -/
  prepWidth    : Nat
  /-- ⚑ **THE SHARED DEFINITION LIST** — the sub-expressions computed ONCE per row, which every
  `TExpr.shr i` then reads. Entry `i` may reference only entries `< i`, so the list is a
  topologically ordered DAG rather than a graph needing a fixpoint.

  This is what a tree IR could not say, and it is not a wire optimisation: the deployed
  hand-written arms hold their shared sub-values as `AB::Expr` VALUES (`poseidon2_permute_expr_lanes`
  computes each round's 16 S-box outputs once and the linear layer references them ~35× each), and
  a tree emission of the same polynomial DUPLICATES them — 140,850 nodes against 3,194, measured on
  the chip. `defs` is the vocabulary for the sharing the deployed gadget already has. -/
  defs         : List TExpr
  /-- Row-filtered gates: each expression must VANISH on every row its selector admits (the
  Rust `builder.<filter>().assert_zero(..)`). -/
  gates        : List TableGate
  interactions : List BusInteraction

/-! ## §2 — Denotation.

A row of a table trace is a WINDOW: the current row, its successor, the current row of the
PREPROCESSED matrix, and the two boundary tags p3's filters read.

⚑ **`TRowEnv` REPLACED `VmRowEnv` HERE (2026-08-02), because the third field went from unread to
load-bearing.** The table denotation used `Emit.EffectVmEmit.VmRowEnv` — `loc`/`nxt`/`pub` — with
`pub` documented as unused, since a shared table has no public inputs. The `prep` leaf needs a third
assignment, and reusing the `pub` slot would have been a pun: two names for one field, one of them
wrong, in the type every table theorem is stated over. The field COUNT is unchanged, so an anonymous
`⟨loc, nxt, _⟩` witness reads identically — but the third component now MEANS the preprocessed row
and is READ.

⚑ A table's denotation has TWO stages, and that split IS the sharing: `shareVals` resolves the
definition list ONCE per row window, left to right, and everything else reads the resulting vector.
A gate never re-enters a definition. -/

/-- **A table AIR's row window.** `loc`/`nxt` are this table's COMMITTED current/next row; `prep` is
its PREPROCESSED current row — a disjoint column space the verifier REBUILDS rather than accepts.

⚠ There is deliberately no `prepNxt`. Every deployed preprocessed-reading arm declares
`preprocessed_next_row_columns() == []` and reads `current_slice()` alone, so a next-row
preprocessed leaf would be a constructor with no consumer — the shape §7 item 1 refuses to add. -/
structure TRowEnv where
  /-- This table's COMMITTED current row. -/
  loc  : Assignment
  /-- This table's COMMITTED next row (the WRAP row on the last row of the trace). -/
  nxt  : Assignment
  /-- This table's PREPROCESSED current row — verifier-recomputed, never prover-supplied. -/
  prep : Assignment

/-- Evaluate a `TExpr` against a row window and an ALREADY-RESOLVED definition vector.
`shr i` past the end of `sv` reads `0`; `TableAir.wellFormed` is what rules that out, and the
Rust decoder refuses it rather than substituting. -/
def TExpr.evalWith (sv : Array ℤ) (env : TRowEnv) : TExpr → ℤ
  | .loc c   => env.loc c
  | .nxt c   => env.nxt c
  | .const z => z
  | .shr i   => sv.getD i 0
  | .prep c  => env.prep c
  | .add a b => a.evalWith sv env + b.evalWith sv env
  | .mul a b => a.evalWith sv env * b.evalWith sv env

/-- ⚑ **THE ONE-PASS RESOLUTION.** Definition `i` is evaluated against the vector of definitions
`0 … i−1` and appended, so each is computed EXACTLY ONCE per row however many times it is read.
This is the Lean twin of the Rust interpreter's per-row `Vec<AB::Expr>` prelude, and it is why
`eval_expr` on the Rust side genuinely memoises rather than re-walking a re-expanded DAG. -/
def shareVals (defs : List TExpr) (env : TRowEnv) : Array ℤ :=
  defs.foldl (fun acc d => acc.push (d.evalWith acc env)) (Array.emptyWithCapacity defs.length)

/-- The definition vector of a table at a row window. -/
def TableAir.shareVals (t : TableAir) (env : TRowEnv) : Array ℤ :=
  _root_.Dregg2.Circuit.TableAirIR.shareVals t.defs env

/-- The gate holds on one row window, under its selector, against a resolved definition vector.
The four cases are exactly p3's four filters: `.all` fires everywhere, `.first`/`.last` only on
their boundary row, `.transition` everywhere but the last (which is the only scope where `nxt` is
the genuine successor). -/
def TableGate.holdsAt (g : TableGate) (sv : Array ℤ) (env : TRowEnv) (isFirst isLast : Bool) :
    Prop :=
  match g.sel with
  | .all        => g.body.evalWith sv env ≡ 0 [ZMOD 2013265921]
  | .first      => isFirst = true  → g.body.evalWith sv env ≡ 0 [ZMOD 2013265921]
  | .last       => isLast  = true  → g.body.evalWith sv env ≡ 0 [ZMOD 2013265921]
  | .transition => isLast  = false → g.body.evalWith sv env ≡ 0 [ZMOD 2013265921]

/-- The gates hold against a GIVEN definition vector. Split out from `RowHolds` so the vector is a
single argument that the decidability instance evaluates ONCE — folding `shareVals` into the
quantifier body would recompute it per gate, which is the very cost this node exists to remove. -/
def TableAir.RowHoldsWith (t : TableAir) (sv : Array ℤ) (env : TRowEnv) (isFirst isLast : Bool) :
    Prop :=
  ∀ g ∈ t.gates, g.holdsAt sv env isFirst isLast

/-- The gates hold on ONE row window. -/
def TableAir.RowHolds (t : TableAir) (env : TRowEnv) (isFirst isLast : Bool) : Prop :=
  t.RowHoldsWith (t.shareVals env) env isFirst isLast

/-- ⚑ **A GATE'S VERDICT ON A CONCRETE WINDOW IS DECIDABLE**, and that is what lets an emitter
exhibit BOTH poles against the EMITTED gate list rather than against a hand-transcribed copy of it.

Without this, a false-pole witness has to be stated over a `structure` of ℤ facts that re-writes
the gate equations by hand — and a re-transcription is exactly the step a cutover is supposed to
delete. Written as a `match` on the literal constructors (not via `unfold` + `split`) so the
instance REDUCES in the kernel, which is what `decide` needs. -/
instance TableGate.instDecidableHoldsAt (g : TableGate) (sv : Array ℤ) (env : TRowEnv)
    (f l : Bool) : Decidable (g.holdsAt sv env f l) :=
  match g with
  | ⟨.all, body⟩ =>
      inferInstanceAs (Decidable (body.evalWith sv env ≡ 0 [ZMOD 2013265921]))
  | ⟨.first, body⟩ =>
      inferInstanceAs (Decidable (f = true → body.evalWith sv env ≡ 0 [ZMOD 2013265921]))
  | ⟨.last, body⟩ =>
      inferInstanceAs (Decidable (l = true → body.evalWith sv env ≡ 0 [ZMOD 2013265921]))
  | ⟨.transition, body⟩ =>
      inferInstanceAs (Decidable (l = false → body.evalWith sv env ≡ 0 [ZMOD 2013265921]))

/-- …and therefore so is the whole row verdict, over the emitted gate list. -/
instance TableAir.instDecidableRowHoldsWith (t : TableAir) (sv : Array ℤ) (env : TRowEnv)
    (f l : Bool) : Decidable (t.RowHoldsWith sv env f l) :=
  inferInstanceAs (Decidable (∀ g ∈ t.gates, g.holdsAt sv env f l))

/-- ⚑ …and for the whole table, with the definition vector resolved ONCE. `t.shareVals env` is a
single argument here, so a `decide` evaluates the prelude once and every gate reads the vector. -/
instance TableAir.instDecidableRowHolds (t : TableAir) (env : TRowEnv) (f l : Bool) :
    Decidable (t.RowHolds env f l) :=
  inferInstanceAs (Decidable (t.RowHoldsWith (t.shareVals env) env f l))

/-- The gates hold on EVERY row of a trace of `n` row windows: window `i` is FIRST iff `i = 0`
and LAST iff `i + 1 = n`. -/
def TableAir.Holds (t : TableAir) (rows : List TRowEnv) : Prop :=
  ∀ i, ∀ h : i < rows.length,
    t.RowHolds rows[i] (decide (i = 0)) (decide (i + 1 = rows.length))

/-- …and a WHOLE CONCRETE TRACE's verdict is decidable too, via `Nat.decidableBallLT`. This is what
lets a multi-row false-pole witness — the shape every cross-row claim needs — be exhibited against
the EMITTED gate list rather than against a transcription of it.

⚠ `Coherent` is NOT decidable and deliberately has no instance: it equates two `Nat → ℤ`
FUNCTIONS, which no `decide` can settle. A witness must discharge it by `rfl`/`funext`, which is
the honest cost of the hypothesis rather than a gap in it. -/
instance TableAir.instDecidableHolds (t : TableAir) (rows : List TRowEnv) :
    Decidable (t.Holds rows) :=
  inferInstanceAs (Decidable (∀ i, ∀ h : i < rows.length,
    t.RowHolds rows[i] (decide (i = 0)) (decide (i + 1 = rows.length))))

/-- ⚑ **COHERENCE — the half `Holds` does not say, and without which every cross-row gate is
worthless.** A `List TRowEnv` carries an INDEPENDENT `nxt` per window; nothing in `Holds` ties
window `i`'s `nxt` to window `i+1`'s `loc`. p3's trace does tie them (`next` is the row
rotation), so a theorem about a `.transition` gate that omits this hypothesis is about a machine
that does not exist: the prover could satisfy every increment gate with a `nxt` it never commits.

Stated separately rather than folded into `Holds` so that a proof which FORGETS it fails to
apply rather than silently quantifying over incoherent traces. -/
def Coherent (rows : List TRowEnv) : Prop :=
  ∀ i, ∀ h : i + 1 < rows.length,
    (rows[i]'(Nat.lt_of_succ_lt h)).nxt = rows[i + 1].loc

/-- A table with no gates is satisfied by anything — the shape a vacuity check must exclude. -/
theorem TableAir.rowHolds_of_no_gates (t : TableAir) (h : t.gates = [])
    (env : TRowEnv) (f l : Bool) : t.RowHolds env f l := by
  intro g hg; rw [h] at hg; cases hg

/-- `RowHolds` is monotone in the gate list: dropping gates cannot turn acceptance into
refusal. The direction a cutover must watch — a re-emission that LOSES a gate accepts strictly
more. ⚠ Stated at a SHARED definition vector, so it applies only between tables with the same
`defs` — which is the honest scope: a re-emission that changes the definitions changes what every
`shr` denotes, and that is not a sublist relation. -/
theorem TableAir.rowHoldsWith_of_sublist {t u : TableAir} (h : t.gates.Sublist u.gates)
    (sv : Array ℤ) (env : TRowEnv) (f l : Bool) (hu : u.RowHoldsWith sv env f l) :
    t.RowHoldsWith sv env f l :=
  fun g hg => hu g (h.mem hg)

/-- …and at the same `defs`, that is a statement about `RowHolds` itself. -/
theorem TableAir.rowHolds_of_sublist {t u : TableAir} (h : t.gates.Sublist u.gates)
    (hd : t.defs = u.defs) (env : TRowEnv) (f l : Bool) (hu : u.RowHolds env f l) :
    t.RowHolds env f l := by
  have : t.shareVals env = u.shareVals env := by
    simp [TableAir.shareVals, hd]
  rw [TableAir.RowHolds, this]
  exact TableAir.rowHoldsWith_of_sublist h _ env f l hu

/-- ⚑ **A ROW SELECTOR IS A REAL WEAKENING, not bookkeeping.** Re-scoping a gate from `.all` to
`.transition` — the single most likely transcription slip in this cutover, and the one that
leaves the algebra byte-identical — strictly ENLARGES the accepted set: everything the `.all`
gate admits, the `.transition` gate admits too, and (by the refutation below) not conversely.
So a selector drift accepts MORE and cannot be caught by any check that reads the body alone. -/
theorem TableGate.transition_weakens (body : TExpr) (sv : Array ℤ) (env : TRowEnv) (f l : Bool)
    (h : TableGate.holdsAt ⟨.all, body⟩ sv env f l) :
    TableGate.holdsAt ⟨.transition, body⟩ sv env f l := by
  intro _; exact h

/-- …and the weakening is STRICT: on the LAST row a `.transition` gate is vacuous while the
`.all` gate still bites. The witness is the constant-1 body on a last row. -/
theorem TableGate.transition_strictly_weaker :
    ∃ (body : TExpr) (sv : Array ℤ) (env : TRowEnv) (f l : Bool),
      TableGate.holdsAt ⟨.transition, body⟩ sv env f l ∧
      ¬ TableGate.holdsAt ⟨.all, body⟩ sv env f l := by
  refine ⟨.const 1, #[], ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩, false, true, ?_, ?_⟩
  · intro h; exact absurd h (by decide)
  · intro h; revert h; unfold TableGate.holdsAt; simp only [TExpr.evalWith]; decide

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
reader has to check by eye against 70 constructors.

⚠ This is the `WindowExpr` form, kept for the MAIN rail (`Circuit.EffectAirIR` reuses it). The
table form is `TExpr.readsColIn`, which must chase `shr` through the definitions. -/
def readsCol : WindowExpr → Nat → Bool
  | .loc c', c => c' == c
  | .nxt c', c => c' == c
  | .const _, _ => false
  | .add a b, c => readsCol a c || readsCol b c
  | .mul a b, c => readsCol a c || readsCol b c

/-- Does this expression read the NEXT row anywhere? The Lean twin of the Rust decoder's
`reads_next`, which is what refuses an `.all`- or `.last`-scoped `nxt` (on the last row p3's
`next` is the WRAP row). ⚠ `WindowExpr` form — the MAIN rail's. -/
def readsNext : WindowExpr → Bool
  | .nxt _ => true
  | .loc _ | .const _ => false
  | .add a b | .mul a b => readsNext a || readsNext b

/-! ### §3b — ⚑ The same two predicates on `TExpr`, CHASING `shr`.

A `shr` leaf is opaque to a syntactic scan, and both predicates are load-bearing: `readsNext` is
what refuses an `.all`-scoped next-row read (on the last row p3's `next` is the WRAP row) and
`readsCol` is what a coverage pin reads. A version that stopped at `shr` would report a gate
reading the next row THROUGH a definition as row-local — a silent widening of exactly the shape
`TableGate.transition_weakens` says is invisible in the algebra. So both take the definition list
and resolve through it. The Rust decoder does the same, and refuses rather than guessing. -/

/-- Does this expression read COMMITTED column `c`, given per-definition verdicts already computed?
⚠ An out-of-range `shr` reads `false` — the direction that under-reports coverage rather than
inventing it; `wellFormed` is what rules the case out.

⚠ **`prep` reads `false`, and that is not an omission.** This predicate answers a question about the
COMMITTED column space — "does any gate read the multiplicity column", the shape a coverage pin and
a mutation sweep ask. A preprocessed column with the same index is a different column of a different
matrix, and answering `true` here would make every such pin quietly wrong in whichever direction the
reader happened to assume. The preprocessed space has its own predicate,
`TExpr.readsPrepColWith`. -/
def TExpr.readsColWith (dv : Array Bool) : TExpr → Nat → Bool
  | .loc c', c => c' == c
  | .nxt c', c => c' == c
  | .const _, _ => false
  | .shr i,   _ => dv.getD i false
  | .prep _,  _ => false
  | .add a b, c => TExpr.readsColWith dv a c || TExpr.readsColWith dv b c
  | .mul a b, c => TExpr.readsColWith dv a c || TExpr.readsColWith dv b c

/-- …and the same question in the PREPROCESSED column space. Separate from `readsColWith` because
the two spaces are separate; a single predicate over both would answer a question nobody asks. -/
def TExpr.readsPrepColWith (dv : Array Bool) : TExpr → Nat → Bool
  | .prep c', c => c' == c
  | .loc _, _ | .nxt _, _ | .const _, _ => false
  | .shr i,   _ => dv.getD i false
  | .add a b, c => TExpr.readsPrepColWith dv a c || TExpr.readsPrepColWith dv b c
  | .mul a b, c => TExpr.readsPrepColWith dv a c || TExpr.readsPrepColWith dv b c

/-- Does this expression read the NEXT row, given per-definition verdicts already computed?
⚠ An out-of-range `shr` reads `true` — FAIL-CLOSED, so an unresolvable share is refused by the
`.all`-scoped-`nxt` check rather than waved through.

⚠ `prep` reads `false`: there is no next-row preprocessed leaf (`TRowEnv` has no `prepNxt`), so a
`prep` read is unconditionally a CURRENT-row read and an `.all`-scoped gate reading one is not the
wrap-row hazard this predicate exists to refuse. -/
def TExpr.readsNextWith (dv : Array Bool) : TExpr → Bool
  | .nxt _ => true
  | .loc _ | .const _ | .prep _ => false
  | .shr i => dv.getD i true
  | .add a b | .mul a b => TExpr.readsNextWith dv a || TExpr.readsNextWith dv b

/-- The per-definition next-row verdicts, resolved in one left-to-right pass — the same shape
`shareVals` uses, and correct for the same reason (definition `i` sees only `0 … i−1`). -/
def defsReadNext (defs : List TExpr) : Array Bool :=
  defs.foldl (fun acc d => acc.push (d.readsNextWith acc)) (Array.emptyWithCapacity defs.length)

/-- The per-definition column-`c` verdicts, one pass. -/
def defsReadCol (defs : List TExpr) (c : Nat) : Array Bool :=
  defs.foldl (fun acc d => acc.push (d.readsColWith acc c)) (Array.emptyWithCapacity defs.length)

/-- The per-definition PREPROCESSED-column-`c` verdicts, one pass. -/
def defsReadPrepCol (defs : List TExpr) (c : Nat) : Array Bool :=
  defs.foldl (fun acc d => acc.push (d.readsPrepColWith acc c))
    (Array.emptyWithCapacity defs.length)

/-- Does this expression — resolving `shr` through `defs` — read committed column `c`? -/
def TExpr.readsColIn (defs : List TExpr) (e : TExpr) (c : Nat) : Bool :=
  e.readsColWith (defsReadCol defs c) c

/-- …and the preprocessed one. -/
def TExpr.readsPrepColIn (defs : List TExpr) (e : TExpr) (c : Nat) : Bool :=
  e.readsPrepColWith (defsReadPrepCol defs c) c

/-- Does this expression — resolving `shr` through `defs` — read the NEXT row anywhere? -/
def TExpr.readsNextIn (defs : List TExpr) (e : TExpr) : Bool :=
  e.readsNextWith (defsReadNext defs)

/-- A table is ROW-LOCAL when no gate reads the next row (THROUGH the definitions) and every gate
is unfiltered — the shape that needed no selector vocabulary at all, and the property a re-emission
of such a table must not quietly lose (`TableGate.transition_weakens`: a re-scope accepts strictly
more). -/
def TableAir.isRowLocal (t : TableAir) : Bool :=
  let dv := defsReadNext t.defs
  t.gates.all (fun g => g.sel == .all && !g.body.readsNextWith dv)

/-! ### §3c — ⚑ WELL-FORMEDNESS OF THE DEFINITION LIST.

Two things must hold or the denotation is quietly wrong rather than loudly refused, and neither is
implied by the types:

1. **Acyclicity by ORDER.** `defs[i]` may reference only `defs[j]` with `j < i`. That is what makes
   the one-pass `shareVals` a resolution rather than a guess — a forward or self reference reads a
   not-yet-pushed slot, and `Array.getD` would hand it a `0`. A DAG whose topological order is the
   list order needs no fixpoint and no cycle detection at evaluation time.
2. **Range.** Every `shr` in a gate, a multiplicity or a tuple must name a declared definition.
3. ⚑ **Range IN THE PREPROCESSED SPACE.** Every `prep c` — in a definition, a gate, a multiplicity
   or a tuple — must name a column of the DECLARED `prepWidth`. This is a third obligation and not a
   special case of the second: `width` and `prepWidth` bound different matrices, and the deployed
   exact-public family has `width = 1` against `prepWidth = arity + 2`, so a `prep` index checked
   against `width` would pass nothing and a `loc` index checked against `prepWidth` would pass
   almost anything.

`TableAir.wellFormed` is all three, decidably, on the emitted object; the Rust decoder REFUSES a
table that fails it rather than substituting zeros. -/

/-- The largest `shr` index in an expression, if any. -/
def TExpr.maxShare : TExpr → Option Nat
  | .shr i => some i
  | .loc _ | .nxt _ | .const _ | .prep _ => none
  | .add a b | .mul a b =>
      match a.maxShare, b.maxShare with
      | some x, some y => some (max x y)
      | some x, none   => some x
      | none,   some y => some y
      | none,   none   => none

/-- The largest PREPROCESSED column index in an expression, if any. ⚠ A `shr` contributes NOTHING
here: its `prep` reads are its DEFINITION's, and `defsAcyclic` already forces every definition to be
scanned in its own right, so the whole list is covered without chasing. -/
def TExpr.maxPrep : TExpr → Option Nat
  | .prep c => some c
  | .loc _ | .nxt _ | .const _ | .shr _ => none
  | .add a b | .mul a b =>
      match a.maxPrep, b.maxPrep with
      | some x, some y => some (max x y)
      | some x, none   => some x
      | none,   some y => some y
      | none,   none   => none

/-- Every `shr` in `e` names a definition strictly below `bound`. -/
def TExpr.sharesBelow (e : TExpr) (bound : Nat) : Bool :=
  match e.maxShare with
  | none   => true
  | some m => decide (m < bound)

/-- Every `prep` in `e` names a preprocessed column strictly below `bound`. -/
def TExpr.prepsBelow (e : TExpr) (bound : Nat) : Bool :=
  match e.maxPrep with
  | none   => true
  | some m => decide (m < bound)

/-- ⚑ Definition `i` references only definitions `< i` — the topological order that makes the
one-pass resolution correct. -/
def TableAir.defsAcyclic (t : TableAir) : Bool :=
  t.defs.zipIdx.all (fun p => p.1.sharesBelow p.2)

/-- Every `shr` outside the definition list names a declared definition. -/
def TableAir.sharesInRange (t : TableAir) : Bool :=
  t.gates.all (fun g => g.body.sharesBelow t.defs.length) &&
  t.interactions.all (fun i =>
    i.mult.sharesBelow t.defs.length && i.tuple.all (fun e => e.sharesBelow t.defs.length))

/-- ⚑ Every `prep` ANYWHERE — definitions included — names a declared preprocessed column. -/
def TableAir.prepsInRange (t : TableAir) : Bool :=
  t.defs.all (fun d => d.prepsBelow t.prepWidth) &&
  t.gates.all (fun g => g.body.prepsBelow t.prepWidth) &&
  t.interactions.all (fun i =>
    i.mult.prepsBelow t.prepWidth && i.tuple.all (fun e => e.prepsBelow t.prepWidth))

/-- The decidable well-formedness verdict the Rust decoder mirrors. -/
def TableAir.wellFormed (t : TableAir) : Bool :=
  t.defsAcyclic && t.sharesInRange && t.prepsInRange

/-- The number of shared definitions — a count a re-emission cannot silently drop. -/
def TableAir.defCount (t : TableAir) : Nat := t.defs.length

/-! ### §3d — ⚑ A SHARE-FREE BLOCK IS THE SAME MACHINE IN BOTH TABLES.

A big emitted table is too large for the kernel, so its soundness theorems are decided against
SUB-TABLES built from the same body lists. With a definition list in play that becomes a real
obligation rather than bookkeeping: the sub-table resolves NO definitions while the emitted table
resolves a thousand, and a theorem about the sub-table would be about a different machine unless the
block it covers reads none of them.

`evalWith_of_shareFree` is that hypothesis, discharged rather than assumed — and it is decidable per
gate (`maxShare == none`), so the transport below is a `decide` on the emitted list, not a promise. -/

/-- A share-free expression does not read the definition vector at all. -/
theorem TExpr.evalWith_of_shareFree :
    ∀ (e : TExpr), e.maxShare = none → ∀ (sv sv' : Array ℤ) (env : TRowEnv),
      e.evalWith sv env = e.evalWith sv' env := by
  intro e
  induction e with
  | loc c => intro _ _ _ _; rfl
  | nxt c => intro _ _ _ _; rfl
  | const z => intro _ _ _ _; rfl
  | shr i => intro h; simp [TExpr.maxShare] at h
  | prep c => intro _ _ _ _; rfl
  | add a b iha ihb =>
      intro h sv sv' env
      simp only [TExpr.maxShare] at h
      split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · next ha hb =>
        simp only [TExpr.evalWith, iha ha sv sv' env, ihb hb sv sv' env]
  | mul a b iha ihb =>
      intro h sv sv' env
      simp only [TExpr.maxShare] at h
      split at h
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · exact absurd h (by simp)
      · next ha hb =>
        simp only [TExpr.evalWith, iha ha sv sv' env, ihb hb sv sv' env]

/-- …so a gate whose body is share-free holds against ANY definition vector if it holds against one. -/
theorem TableGate.holdsAt_of_shareFree {g : TableGate} (h : g.body.maxShare = none)
    {sv sv' : Array ℤ} {env : TRowEnv} {f l : Bool} (hh : g.holdsAt sv env f l) :
    g.holdsAt sv' env f l := by
  unfold TableGate.holdsAt at hh ⊢
  rw [TExpr.evalWith_of_shareFree g.body h sv' sv env]
  exact hh

/-- ⚑ **THE TRANSPORT.** A table whose every gate is share-free has a `RowHoldsWith` independent of
the definition vector — which is what lets a sub-table verdict be carried back to the emitted table
that DOES have definitions. The hypothesis is `decide`-able on the emitted gate list. -/
theorem TableAir.rowHoldsWith_of_shareFree {t : TableAir}
    (h : t.gates.all (fun g => g.body.maxShare == none) = true)
    {sv sv' : Array ℤ} {env : TRowEnv} {f l : Bool} (hh : t.RowHoldsWith sv env f l) :
    t.RowHoldsWith sv' env f l := by
  intro g hg
  refine TableGate.holdsAt_of_shareFree ?_ (hh g hg)
  have := List.all_eq_true.mp h g hg
  simpa using this

/-- …and in particular a share-free table's `RowHolds` is its `RowHoldsWith` at any vector. -/
theorem TableAir.rowHolds_of_shareFree_rowHoldsWith {t : TableAir}
    (h : t.gates.all (fun g => g.body.maxShare == none) = true)
    {sv : Array ℤ} {env : TRowEnv} {f l : Bool} (hh : t.RowHoldsWith sv env f l) :
    t.RowHolds env f l :=
  TableAir.rowHoldsWith_of_shareFree h hh

/-! ## §4 — The wire format.

The five shared leaves render EXACTLY as `WindowExpr.toJson` renders them
(`loc`/`nxt`/`const`/`add`/`mul`), which is why the artifacts emitted before the sharing and
preprocessed nodes existed keep every gate and interaction byte. `shr` is the sixth tag and `prep`
the seventh; `defs` and `prep_width` are the two new top-level keys.

⚠ **Both are emitted unconditionally, and each IS a flag day** — the eight artifacts that predated
`defs` each gained the literal `,"defs":[]` after their width and changed in no other byte, and the
TEN that predate `prep_width` each gain `,"prep_width":0` after their width and change in no other
byte. An OPTIONAL key would have kept them byte-identical and bought a decoder that has to peek,
i.e. a wire format with two readings; this repo's rule is to break loudly rather than reinterpret.
The Rust decoder mirrors THIS renderer key for key, exactly as the v2 decoder mirrors
`emitVmJson2`. -/

private def jsonArray {α : Type} (f : α → String) : List α → String
  | []      => "[]"
  | x :: xs => "[" ++ f x ++ (xs.foldl (fun acc y => acc ++ "," ++ f y) "") ++ "]"

/-- Wire-render a `TExpr`. The five shared constructors are `WindowExpr.toJson`'s, byte for byte.
⚠ `prep` carries a `"c"` (a COLUMN, like `loc`/`nxt`) where `shr` carries an `"i"` (an INDEX into
the definition list) — the tags differ, so a decoder that read the wrong key resolves nothing
rather than resolving something wrong. -/
def TExpr.toJson : TExpr → String
  | .loc c   => "{\"t\":\"loc\",\"c\":" ++ toString c ++ "}"
  | .nxt c   => "{\"t\":\"nxt\",\"c\":" ++ toString c ++ "}"
  | .const z => "{\"t\":\"const\",\"v\":" ++ (if z < 0 then "-" ++ toString (-z) else toString z) ++ "}"
  | .shr i   => "{\"t\":\"shr\",\"i\":" ++ toString i ++ "}"
  | .prep c  => "{\"t\":\"prep\",\"c\":" ++ toString c ++ "}"
  | .add l r => "{\"t\":\"add\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"
  | .mul l r => "{\"t\":\"mul\",\"l\":" ++ l.toJson ++ ",\"r\":" ++ r.toJson ++ "}"

/-- ⚑ The five shared leaves render IDENTICALLY to `WindowExpr`'s. This is the property that makes
the eight pre-sharing artifacts re-emit with their gate bytes untouched, and it is pinned rather
than eyeballed. -/
theorem TExpr.toJson_agrees_with_windowExpr :
    (TExpr.loc 7).toJson = (WindowExpr.loc 7).toJson ∧
    (TExpr.nxt 7).toJson = (WindowExpr.nxt 7).toJson ∧
    (TExpr.const (-3)).toJson = (WindowExpr.const (-3)).toJson ∧
    (TExpr.add (.loc 1) (.const 2)).toJson
      = (WindowExpr.add (.loc 1) (.const 2)).toJson ∧
    (TExpr.mul (.nxt 1) (.const 2)).toJson
      = (WindowExpr.mul (.nxt 1) (.const 2)).toJson := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Render one gate. -/
def TableGate.toJson (g : TableGate) : String :=
  "{\"sel\":\"" ++ g.sel.tag ++ "\",\"body\":" ++ g.body.toJson ++ "}"

/-- Render one bus interaction. -/
def BusInteraction.toJson (i : BusInteraction) : String :=
  "{\"bus\":\"" ++ i.bus ++ "\",\"op\":\"" ++ i.op.tag ++ "\",\"mult\":" ++ i.mult.toJson ++
  ",\"tuple\":" ++ jsonArray TExpr.toJson i.tuple ++ "}"

/-- **`emitTableAirJson`** — the canonical wire string. What the `#guard` golden pins and the
Rust decoder ingests. -/
def emitTableAirJson (t : TableAir) : String :=
  "{\"name\":\"" ++ t.name ++ "\",\"kind\":\"table_air\",\"ir\":2,\"width\":" ++
  toString t.width ++ ",\"prep_width\":" ++ toString t.prepWidth ++
  ",\"defs\":" ++ jsonArray TExpr.toJson t.defs ++
  ",\"gates\":" ++ jsonArray TableGate.toJson t.gates ++
  ",\"interactions\":" ++ jsonArray BusInteraction.toJson t.interactions ++ "}"

/-- **`emitTableAirFamilyJson`** — a JSON ARRAY of table AIRs, the wire form of a table AIR that is
a FAMILY rather than a singleton.

⚑ It exists because ONE of the eleven arms is not one table: `Ir2Air::ExactPublicTable` is a schema
indexed by the declared tuple ARITY, and a descriptor may declare tables at several arities at once
(`private-book-bfv-…-stage0-exact-public` declares arity 17 and arity 4 in the same descriptor). The
alternative shapes were measured against and rejected: 64 separate artifacts multiply the directory
the AIR fingerprint reads by seven, and a single artifact carrying a bus name with a SUBSTITUTION
HOLE is a reference without a referent in wire-format clothes. An array of the SAME object the
singleton path already decodes adds no grammar — the element renderer is `emitTableAirJson`
unchanged. -/
def emitTableAirFamilyJson (ts : List TableAir) : String :=
  jsonArray emitTableAirJson ts

/-! ## §5 — Shared authoring sugar.

The shapes every emitter builds. Kept here rather than in one table's file so the second table
to need `a − b` does not re-derive it (`MapAbsentTableEmit` defined these privately in the first
pass; they are hoisted because `ByteTableEmit`, `MemBoundaryTableEmit` and `MemoryTableEmit`
all need them). -/

/-- Current-row column read. -/
def v (c : Nat) : TExpr := .loc c
/-- NEXT-row column read. ⚠ Only meaningful under `.transition` (or `.first`); on the last row
p3's `next` is the WRAP row. -/
def n (c : Nat) : TExpr := .nxt c
/-- Field constant. -/
def k (z : ℤ) : TExpr := .const z
/-- ⚑ Read shared definition `i` — the value the table computed ONCE for this row. -/
def s (i : Nat) : TExpr := .shr i
/-- ⚑ Read PREPROCESSED column `c` of this row — the verifier-recomputed column space. -/
def p (c : Nat) : TExpr := .prep c
/-- `a − b`, the standard encoding (there is no `sub` node). -/
def eSub (a b : TExpr) : TExpr := .add a (.mul (.const (-1)) b)
/-- `1 − e`. -/
def eOneMinus (e : TExpr) : TExpr := eSub (k 1) e
/-- The boolean gate body `c·(c − 1)` — the Rust `x * (x - ONE)`. -/
def gBool (c : Nat) : TExpr := .mul (v c) (.add (v c) (k (-1)))

/-- An unfiltered gate. -/
def gAll (e : TExpr) : TableGate := ⟨.all, e⟩
/-- A first-row gate. -/
def gFirst (e : TExpr) : TableGate := ⟨.first, e⟩
/-- A transition gate. -/
def gTrans (e : TExpr) : TableGate := ⟨.transition, e⟩

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
def recompose (bits : Nat) (limb0 : Nat) : TExpr :=
  (List.range (limbGeom bits).1).foldl
    (fun acc i => .add acc (.mul (v (limb0 + i)) (k (LIMB_BASE ^ i))))
    (k 0)

/-- `Σ_{b < top} bit_b · 2^b` over the partial top limb's bit columns, same accumulation. -/
def topRecompose (bits : Nat) (limb0 : Nat) : TExpr :=
  (List.range (limbGeom bits).2).foldl
    (fun acc b => .add acc (.mul (v (limb0 + (limbGeom bits).1 + b)) (k (2 ^ b))))
    (k 0)

/-- The GATES of one `bits`-wide decomposition of `ve` over the block at `limb0`: booleans on
the top-limb bits, the top-limb recomposition, then the whole-value recomposition. Emission
order is the Rust loop's. -/
def decompGates (bits : Nat) (ve : TExpr) (limb0 : Nat) : List TExpr :=
  (List.range (limbGeom bits).2).map (fun b => gBool (limb0 + (limbGeom bits).1 + b)) ++
  [ eSub (topRecompose bits limb0) (v (limb0 + (limbGeom bits).1 - 1))
  , eSub (recompose bits limb0) ve ]

/-- The byte-table QUERIES of one decomposition: the FULL limbs only (the top one is
bit-decomposed instead, which is what makes the bound tight). -/
def decompQueries (bits : Nat) (byteBus : String) (limb0 : Nat) (mult : TExpr) :
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

/-! ### §6a′ — ⚑⚑ `LIMB_BITS = 4` IS A SOUNDNESS PIN, NOT A PERFORMANCE ONE.

Read `canonDecompQueries` below: the `hi4` column is bounded by **ONE query on the shared byte bus
and nothing else**. So `hi4`'s admissible range IS the byte table's HEIGHT, and the byte table's
height IS `2 ^ LIMB_BITS`. `hi4` is not a limb — it is the high digit of the canonical split
`value = hi4·2^27 + lo27` — but it is bounded as though it were.

That coupling is invisible from either end. `ByteTableEmit.gates_admit_every_height` proves the
byte table's ALGEBRA does not care how tall it is, which reads as "the height is a free verifier
constant"; and the width arithmetic says a bigger radix is cheaper (measured 2026-08-06: the
corpus aux block is 75,156 columns at radix 4 and 39,168 at radix 8, a 0.521× on the quantity the
prover actually commits). Both are true. Neither can see this.

`KEY_HI_MAX = 15` and `p − 1 = 15·2^27` are what make the split unique at a `[0,16)` bound. The two
theorems below are the pair: the collision a `[0,256)` bound ADMITS, exhibited on a real witness,
and its ABSENCE at the deployed bound. ⚠ The consequence is not a wider range — it is that
`CMP_COLS`/`lexLtGates` order keys lexicographically on `(hi4, lo27)`, so a felt with two
representations compares two ways, which is a satisfying witness for the IMT bracket
`low_addr < key < low_next` on a key that does not lie in it. -/

/-- The felt a canonical-split block denotes: `hi·2^27 + lo`, reduced. -/
def canonValue (hi lo : Nat) : Nat := (hi * 134217728 + lo) % 2013265921

/-- ⚑ **THE COLLISION A 256-ROW BYTE TABLE ADMITS.** `(hi 0, lo 2^27−1)` and `(hi 16, lo 0)` are
both legal under a `[0,256)` bound on `hi` with `lo < 2^27`, and they denote the SAME felt. -/
theorem canon_split_collides_when_hi_reaches_16 :
    canonValue 0 134217727 = canonValue 16 0 := by decide

/-- ⚑ **AND THE DEPLOYED BOUND EXCLUDES IT — the TRUE pole.** No legal `hi < 16` reproduces that
felt from `lo = 0`, so at `[0,16)` the witness above simply does not exist. -/
theorem canon_hi_witness_absent_below_16 :
    (List.range 16).filter (fun hi => canonValue hi 0 == canonValue 0 134217727) = [] := by decide

/-- …and it appears at EXACTLY the first row a 256-height table adds beyond a 16-height one, which
is what makes the height the load-bearing quantity rather than a coincidence of this witness. -/
theorem canon_hi_witness_present_below_256 :
    (List.range 256).filter (fun hi => canonValue hi 0 == canonValue 0 134217727) = [16] := by
  decide

#assert_axioms canon_split_collides_when_hi_reaches_16
#assert_axioms canon_hi_witness_absent_below_16
#assert_axioms canon_hi_witness_present_below_256

/-- `hi4` of a canonical-decomposition block. -/
def canonHi (b0 : Nat) : TExpr := v b0
/-- `lo27 = value − hi4 · 2^27`. -/
def canonLo (ve : TExpr) (b0 : Nat) : TExpr :=
  eSub ve (.mul (v b0) (k KEY_HI_BASE))

/-- The gates of one CANONICAL decomposition `value = hi4·2^27 + lo27` over the 13-column block at
`b0`, gated by `gate`. The last is the UNIQUENESS TOOTH `is15 · lo27 = 0`. -/
def canonDecompGates (ve : TExpr) (b0 : Nat) (gate : TExpr) : List TExpr :=
  decompGates KEY_LO_BITS (canonLo ve b0) (b0 + 1) ++
  [ gBool (b0 + 1 + decompCols KEY_LO_BITS)
  , .mul (eSub (v b0) (k KEY_HI_MAX)) (v (b0 + 1 + decompCols KEY_LO_BITS))
  , eSub (.mul (eSub (v b0) (k KEY_HI_MAX)) (v (b0 + 2 + decompCols KEY_LO_BITS)))
         (eSub gate (v (b0 + 1 + decompCols KEY_LO_BITS)))
  , .mul (v (b0 + 1 + decompCols KEY_LO_BITS)) (canonLo ve b0) ]

/-- The queries of one canonical decomposition: the `hi4` nibble, then the low limbs. -/
def canonDecompQueries (byteBus : String) (b0 : Nat) (mult : TExpr) : List BusInteraction :=
  ⟨byteBus, .query, mult, [v b0]⟩ :: decompQueries KEY_LO_BITS byteBus (b0 + 1) mult

/-- The ROW-LOCAL half of a lex comparator block: the branch selector's boolean and the `dlo`
range decomposition. Always `.all`-scoped in both consumers. -/
def lexLtRowLocalGates (b0 : Nat) : List TExpr :=
  gBool b0 :: decompGates KEY_LO_BITS (v (b0 + 2)) (b0 + 3)

/-- ⚑ The three BRANCH equations of a lex comparator, split out from the row-local half because
the two deployed consumers assert them under DIFFERENT selectors: `MapAbsent` compares two columns
of ONE row (`.all`), the universal boundary compares a row against its SUCCESSOR (`.transition`,
the Rust `transition_only` flag). Keeping them in one list would have forced the second consumer to
re-derive the algebra beside a different filter. -/
def lexLtBranchGates (aHi aLo bHi bLo : TExpr) (b0 : Nat) (gate : TExpr) :
    List TExpr :=
  [ eSub (v (b0 + 1)) (.mul (.mul gate (v b0)) (eSub (eSub bHi aHi) (k 1)))
  , .mul (.mul gate (eOneMinus (v b0))) (eSub bHi aHi)
  , eSub (v (b0 + 2)) (.mul (.mul gate (eOneMinus (v b0))) (eSub (eSub bLo aLo) (k 1))) ]

/-- The gates of one lexicographic STRICT-LT `a < b`, all at one selector — the `MapAbsent` shape.
`s = 1` ⇒ `bHi ≥ aHi + 1` (witness `dhi`, a nibble); `s = 0` ⇒ `bHi = aHi` and `bLo ≥ aLo + 1`
(witness `dlo`, 27-bit). -/
def lexLtGates (aHi aLo bHi bLo : TExpr) (b0 : Nat) (gate : TExpr) : List TExpr :=
  lexLtRowLocalGates b0 ++ lexLtBranchGates aHi aLo bHi bLo b0 gate

/-- The queries of one lex comparator: the `dhi` nibble, then the `dlo` limbs. -/
def lexLtQueries (byteBus : String) (b0 : Nat) (mult : TExpr) : List BusInteraction :=
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
def group8 (base : Nat) : List TExpr := (List.range LANES).map (fun i => v (base + i))

/-- The chip ABSORB tuple `[arity, padTo RATE ins, out0..out7]` (25 wide) — the Lean twin of the
Rust `chip_absorb_tuple`. ⚑ The arity tag is DATA (`ins.length`), not a hardcoded constant: a wider
leaf extends the declared column list and changes NOTHING else here, which is the property the Rust
closure's own doc claims and which a per-table copy would quietly lose.

⚑ **`hAdm` CHECKS the arity; this docstring used to only WARN about it.** `ins.length` must be one
of `CHIP_ADMITTED_ARITIES` — the deployed chip's degree-7 admission product has exactly seven roots
and `≤ RATE` is strictly weaker (`DescriptorIR2`, the arity note). Until 2026-08-02 that sentence
was the entire enforcement, on a function taking `ins : List Nat` unchecked, so a table AIR could
emit a chip query at an arity the chip refuses and nothing in Lean would notice — the same shape the
main descriptor's `chipLookupTuple` carried. It is now an `autoParam`: every honest table
discharges it silently and an inadmissible one **fails to elaborate**. `Prop`-erased, so the emitted
`TExpr` list and every artifact byte are untouched. -/
def chipAbsorbTuple (ins : List Nat) (digest : Nat)
    (hAdm : Dregg2.Circuit.DescriptorIR2.ChipArityAdmitted ins.length := by chip_arity_admitted) :
    List TExpr :=
  let _ := hAdm
  k (ins.length : ℤ) ::
    (ins.map v ++ (List.range (RATE - ins.length)).map (fun _ => k 0) ++ group8 digest)

/-- The arity-16 `node8` compression tuple `[16, L8, R8, out8]` (25 wide): `L8 = cur + dir·(sib −
cur)` and `R8 = sib + dir·(cur − sib)` — the Merkle sibling-swap, `Dregg2.Circuit.GateExpr.gMux`'s
form B (`gSwapLeft`/`gSwapRight`), the Lean twin of the Rust `node8_lookup_tuple`, and the
in-circuit face of `heap_node8` / `recomposeUp8`.

⚑ **RE-EMIT**: this used to be the expensive form (`(1−dir)·cur + dir·sib`, 3 multiplications per
lane); this is the SAME polynomial at 2 multiplications per lane — `GateExpr.node8Tuple_is_gMux`/
`node8Tuple_R_is_gMux` pin this shape against `gSwapLeft`/`gSwapRight` (`rfl`). Written out by hand
rather than calling `GateExpr` directly: `GateExpr` imports `TableAirIR`, so the reverse import
would be a cycle — the same constraint `gCols`/`gVars`/`gOneMinus_table` name against
`DescriptorIR2`/this file elsewhere.

⚠ The direction MIX is what costs the tuple its SECOND degree, and it is why `ir2_degree_budget`
reads 4 rather than 3 on every table that folds a path. -/
def node8Tuple (curBase sibBase outBase dirC : Nat) : List TExpr :=
  let d : TExpr := v dirC
  k NODE8_ARITY ::
  ((List.range LANES).map (fun i =>
      .add (v (curBase + i)) (.mul d (eSub (v (sibBase + i)) (v (curBase + i))))) ++
   (List.range LANES).map (fun i =>
      .add (v (sibBase + i)) (.mul d (eSub (v (curBase + i)) (v (sibBase + i))))) ++
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
def foldQueries (bus : String) (leaf chain0 root sib0 dir0 depth : Nat) (mult : TExpr) :
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

/-! ## §7 — ✅ `ExactPublicTable`: THE LAST ARM, AND ALL FOUR ITEMS DISCHARGED (2026-08-02).

This section priced the ONE arm of the eleven the tool could not express. All four items are now
done and the arm is DELETED; what follows is the record of what each cost, kept because the
reasoning is what a future prep-reading or parameterized table inherits. The emitter is
`Emit/ExactPublicTableEmit.lean`; the deleted Rust was:

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

⚑ **The asymmetry was the whole point: that is ONE gate and ONE bus leg — the SMALLEST arm of the
eleven — and it was the one that could not be ported.** The cost was entirely in the IR, not in the
constraint, which is why it was a tool project rather than a transcription and why starting it
inside a burn-down of transcriptions would have been the wrong shape.

**The four items, in the order they bit.**

1. ✅ **THE DESIGN FORK — DECIDED 2026-08-02, in §1b.** `TableAir` has its OWN expression type. The
   deciding evidence is in §1b: `WindowExpr` is a MAIN-descriptor type (120 files, 110 of them
   constructing `windowGate`), `Ir2Air::Main` can serve neither of the two leaves a table needs, and
   §7's own counter-argument — that a separate type duplicates the grammar §5 exists to avoid
   duplicating — does not hold, because §5/§6 are TABLE-only and no main-descriptor file imports
   them.

   ⓘ **AND THE PRICE IT QUOTED FOR `prep` WAS RIGHT, WITH ONE ADDITION IT DID NOT SEE.** It said one
   constructor plus one case in `TExpr.{evalWith,toJson,readsColWith,readsNextWith,maxShare}` and
   their five Rust mirrors. That is exactly what landed — plus a SIXTH function on each side
   (`maxPrep` / `TableExpr::max_prep`, item 2's bound) and a change the estimate had no way to see:
   the denotation's row window went `VmRowEnv → TRowEnv` (§2), because the third field went from
   documented-as-unused to load-bearing and reusing the `pub` slot for the preprocessed row would
   have been a pun in the type every table theorem is stated over. Field count unchanged, so no
   witness moved; 65 type ascriptions across the eleven table files did. **No main-descriptor file
   moved, and no new refusal landed on the main decode path** — both as priced.

2. ✅ **A WAY TO DECLARE THE PREPROCESSED MATRIX.** `TableAir.prepWidth` (§1), the `"prep_width"`
   wire key (§4), and `prepsInRange` (§3c) — the bound in its OWN space, because `width` bounds a
   different matrix. **All TEN pre-existing artifacts re-emit**, each gaining exactly the literal
   `,"prep_width":0` after its width and changing in NO OTHER BYTE; `air_fingerprint()` and
   `verifier_source_closure_fingerprint()` both move, since both splice `TABLE_AIR_ARTIFACTS` whole.
   The `defs` key took the identical flag day earlier the same day, and this one cost the same.

3. ✅ **PARAMETERIZATION, which the other ten did not need.** This is not one table, it is a FAMILY
   indexed by the declared tuple ARITY, and a single descriptor may declare tables at several
   arities at once. So the emitted object is a SCHEMA and the artifact is a JSON ARRAY
   (`emitTableAirFamilyJson`, §4) of the same object the singleton path already decodes — element
   `i` is arity `i + 1`, up to `ExactPublicTableEmit.EP_MAX_ARITY` (`97` since 2026-08-06;
   it was `64`, and the raise cost a JSON re-emit and no resource).

   ⚑ **AND THE BUS NAME MOVED INTO THE TUPLE, which is what made a per-arity family possible at
   all.** This section previously read *"emitting 64 fixed artifacts is not a way out — the bus name
   still varies with `table_id`"*, and that was true of the deployed shape: one bus
   `ir2_exact_public_{table_id}` per declared table, so an artifact could not name its own bus
   without knowing a number no artifact can know. The fix is not a substitution hole. It is to stop
   spending a STRING on a separation a FIELD can carry: the bus is now `ir2_exact_public_a{arity}`
   and the table id is preprocessed column 0, the first entry of every served tuple and of every
   query. ⚠ The separation is exactly as strong — LogUp balance is a multiset equality over TUPLES,
   the id is a tuple field, and the preprocessed column the verifier rebuilds rather than accepts,
   so a query for table 517 can be served only by an instance whose column 0 is 517. And the
   pre-existing co-batch hazard (two descriptors declaring the SAME wire id pool their capacity) is
   preserved unchanged rather than widened: same id ⇒ same tuples ⇒ same pooling, and a different id
   at the same arity never collides.

4. ✅ **THE DIFFERENTIAL ORACLE WOULD HAVE GONE BLIND — FIXED 2026-08-01, ahead of any
   `prep`-reading emission**, which is the only ordering that could have made this port's sweep
   mean anything. `table_air_gates_accept` built an EMPTY preprocessed window
   (`RowWindow::from_two_rows(&[], &[])`), and every mutation sweep in this burn-down ran through
   it, so a `prep`-reading table would have been swept against zeros — the instrument reporting a
   clean undetected set while seeing none of the columns the arm is about. ⚑ That is the failure
   this repo's own doctrine names: a gate that cannot go red.

   ⚠ **And the fix is the REFUSAL, not the plumbing.** `descriptor_ir2::ir2_air_gates_accept` takes
   the preprocessed rows and checks their shape against the AIR's OWN
   `BaseAir::preprocessed_width` — the authority on whether an arm reads them, so a future arm is
   covered without editing the oracle — and REFUSES a mismatch rather than substituting zeros. An
   oracle that zero-filled would not merely be blind: the manifest's first entry is pinned at
   multiplicity 2, so against an all-zero prep row the honest instance reads UNSAT. A substituted
   witness makes BOTH verdicts meaningless, not just one.
   `circuit/tests/ir2_preprocessed_sweep_harness.rs` measures both poles. ⓘ Its §3 assertion — that
   every `LeanTableAir` declares ZERO preprocessed columns, which is what made the earlier sweeps
   sound — is now FALSE of one table and is re-stated as a per-table pin rather than deleted: the
   exact-public family declares `arity + 2`, every other table still declares 0, and the day a third
   shape appears the pin reds instead of the sweeps quietly going blind.

**⚑ THE BURN-DOWN IS 11 OF 11.** `Ir2Air` is `Main | LeanTable`: one arm interprets the MAIN
descriptor and one interprets a Lean-authored TABLE. There is no arm of that enum that authors a
constraint, and law #1 is now true of the whole IR-v2 instance family rather than of ten elevenths
of it. -/

/-! ## §8 — Tripwires: the grammar golden, the SHARING node, and both polarities of `RowHolds`. -/

/-- A tiny table exercising every node of the grammar: gates at three selectors, a next-row
read, all four bus ops, a non-constant multiplicity. -/
def demoTable : TableAir :=
  { name := "demo-table-air"
  , width := 2
  , prepWidth := 0
  , defs := []
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
-- ⚠ The ONLY difference from the pre-sharing golden is the `,"defs":[]` after the width; every
-- gate and interaction byte is unchanged, which is the property the eight artifacts inherit.
#guard emitTableAirJson demoTable ==
  "{\"name\":\"demo-table-air\",\"kind\":\"table_air\",\"ir\":2,\"width\":2,\"prep_width\":0,\"defs\":[],\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"sel\":\"first\",\"body\":{\"t\":\"loc\",\"c\":0}},{\"sel\":\"transition\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":1}}}}}],\"interactions\":[{\"bus\":\"ir2_byte\",\"op\":\"query\",\"mult\":{\"t\":\"const\",\"v\":1},\"tuple\":[{\"t\":\"loc\",\"c\":1}]},{\"bus\":\"ir2_byte\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":1},\"tuple\":[{\"t\":\"loc\",\"c\":0}]},{\"bus\":\"ir2_map_log\",\"op\":\"receive\",\"mult\":{\"t\":\"loc\",\"c\":0},\"tuple\":[{\"t\":\"loc\",\"c\":0},{\"t\":\"loc\",\"c\":1}]},{\"bus\":\"ir2_mem_check\",\"op\":\"send\",\"mult\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"loc\",\"c\":1}},\"tuple\":[{\"t\":\"loc\",\"c\":1}]}]}"

-- Shape pins: a dropped gate or bus leg moves one of these.
#guard demoTable.gates.length == 3
#guard demoTable.defCount == 0
#guard demoTable.busCount == 4
#guard demoTable.busCountOn "ir2_byte" == 2
#guard demoTable.busCountOp "ir2_byte" .query == 1
#guard demoTable.busCountOp "ir2_byte" .provide == 1
#guard demoTable.gateCountSel .all == 1
#guard demoTable.gateCountSel .transition == 1
#guard demoTable.wellFormed == true
-- The two column predicates, both polarities, on a table that exercises `nxt`.
#guard demoTable.isRowLocal == false
#guard readsNext (DescriptorIR2.WindowExpr.add (.nxt 0) (.loc 0)) == true
#guard readsNext (DescriptorIR2.WindowExpr.loc 0) == false
#guard readsCol (DescriptorIR2.WindowExpr.loc 0) 0 == true
#guard readsCol (DescriptorIR2.WindowExpr.loc 0) 1 == false
#guard TExpr.readsNextIn [] (eSub (n 0) (v 0)) == true
#guard TExpr.readsNextIn [] (gBool 0) == false
#guard TExpr.readsColIn [] (gBool 0) 0 == true
#guard TExpr.readsColIn [] (gBool 0) 1 == false

/-! ### §8b — ⚑ THE SHARING NODE, both polarities.

`shareDemo` computes `d0 = c0 + 1` once and squares it via `d1 = d0·d0`, then asserts `c1 = d1`.
The point of the pins below is that a `shr` is a REAL leaf with a REAL denotation and REAL
analyses — not a wire abbreviation the evaluator re-expands. -/

/-- A table whose gate reads a shared definition twice, through a second definition. -/
def shareDemo : TableAir :=
  { name := "share-demo"
  , width := 2
  , prepWidth := 0
  , defs := [ .add (v 0) (k 1)          -- d0 = c0 + 1
            , .mul (s 0) (s 0) ]        -- d1 = d0²
  , gates := [ gAll (eSub (v 1) (s 1)) ]
  , interactions := [] }

/-- …and the same table with a `nxt` hidden BEHIND a definition, which is the shape a
`shr`-blind `readsNext` would wave through under an `.all` selector. -/
def shareNxtDemo : TableAir :=
  { name := "share-nxt-demo"
  , width := 2
  , prepWidth := 0
  , defs := [ .add (n 0) (k 1) ]
  , gates := [ gAll (eSub (v 1) (s 0)) ]
  , interactions := [] }

#guard shareDemo.defCount == 2
#guard shareDemo.wellFormed == true
#guard shareDemo.isRowLocal == true
-- The wire tag, byte-pinned: `shr` carries an INDEX, not a column.
#guard TExpr.toJson (s 3) == "{\"t\":\"shr\",\"i\":3}"
#guard emitTableAirJson shareDemo ==
  "{\"name\":\"share-demo\",\"kind\":\"table_air\",\"ir\":2,\"width\":2,\"prep_width\":0,\"defs\":[{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"const\",\"v\":1}},{\"t\":\"mul\",\"l\":{\"t\":\"shr\",\"i\":0},\"r\":{\"t\":\"shr\",\"i\":0}}],\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"shr\",\"i\":1}}}}],\"interactions\":[]}"

-- ⚑ THE ANALYSES CHASE `shr`. A column read only THROUGH a definition is still a read…
#guard TExpr.readsColIn shareDemo.defs (s 1) 0 == true
#guard TExpr.readsColIn shareDemo.defs (s 1) 1 == false
-- …and a `nxt` read only THROUGH a definition is still a next-row read. ⚠ This is the pin that
-- keeps the `.all`-scoped-`nxt` refusal honest: `isRowLocal` is FALSE here, and a `readsNext` that
-- stopped at the `shr` leaf would have said `true`.
#guard TExpr.readsNextIn shareNxtDemo.defs (s 0) == true
#guard shareNxtDemo.isRowLocal == false

-- ⚑ WELL-FORMEDNESS, both poles. A forward reference and an out-of-range share are REFUSED.
#guard ({ shareDemo with defs := [.mul (s 1) (k 1), .const 0] } : TableAir).defsAcyclic == false
#guard ({ shareDemo with defs := [.mul (s 0) (k 1)] } : TableAir).defsAcyclic == false
#guard ({ shareDemo with gates := [gAll (s 9)] } : TableAir).sharesInRange == false
#guard ({ shareDemo with
          interactions := [⟨"b", .query, s 9, [v 0]⟩] } : TableAir).sharesInRange == false

/-- ⚑ **THE SHARING IS SEMANTICS-PRESERVING, exhibited.** `shareDemo` accepts exactly the rows on
which `c1 = (c0+1)²`, which is what the same polynomial written as a TREE would accept. Both poles,
decided against the emitted object. -/
theorem shareDemo_accepts_the_square :
    shareDemo.RowHolds ⟨fun c => if c = 0 then 4 else 25, fun _ => 0, fun _ => 0⟩ false false := by
  decide

/-- …and REFUSES a row where the shared value is not squared. A share that evaluated to `0` — the
shape an unresolvable index would produce — would accept `c1 = 0` here; it does not. -/
theorem shareDemo_refuses_a_wrong_square :
    ¬ shareDemo.RowHolds ⟨fun c => if c = 0 then 4 else 24, fun _ => 0, fun _ => 0⟩ false false := by
  decide

/-- …and in particular refuses the all-zero row, which is what a silently-zero `shr` would accept. -/
theorem shareDemo_refuses_zero :
    ¬ shareDemo.RowHolds ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ false false := by decide

/-- ⚑ **THE TREE AND THE DAG DENOTE THE SAME THING**, on the emitted objects rather than in prose:
the un-shared spelling of `shareDemo`'s gate accepts and refuses exactly where the shared one does.
This is the claim the whole node rests on, and it is stated so that a `shareVals` that resolved in
the wrong order would break it. -/
def shareDemoTree : TableAir :=
  { name := "share-demo-tree"
  , width := 2
  , prepWidth := 0
  , defs := []
  , gates := [ gAll (eSub (v 1) (.mul (.add (v 0) (k 1)) (.add (v 0) (k 1)))) ]
  , interactions := [] }

#guard ((List.range 12).all (fun a => (List.range 12).all (fun b =>
    let e : TRowEnv := ⟨fun c => if c = 0 then (a : ℤ) else (b : ℤ), fun _ => 0, fun _ => 0⟩
    decide (shareDemo.RowHolds e false false) == decide (shareDemoTree.RowHolds e false false))))

/-! ### §8c — ⚑ THE PREPROCESSED NODE, both polarities and both column spaces.

`prepDemo` is the shape of the exact-public family in miniature: ONE committed column pinned to a
preprocessed one, plus a `.provide` leg whose tuple is preprocessed and whose multiplicity is
committed. The pins below exist because three things about `prep` are easy to get wrong in a way no
gate-body check would see — the COLUMN SPACE (`readsCol` must not answer for it), the BOUND
(`prepWidth`, not `width`), and the DENOTATION (a leaf that read the committed row instead would
still typecheck and would still vanish on any row where the two agree). -/

/-- A table whose one gate pins committed column 0 to preprocessed column 2, and whose one bus leg
serves the preprocessed pair at the committed multiplicity. -/
def prepDemo : TableAir :=
  { name := "prep-demo"
  , width := 1
  , prepWidth := 3
  , defs := []
  , gates := [ gAll (eSub (v 0) (p 2)) ]
  , interactions := [ ⟨"ir2_exact_public_a2", .provide, v 0, [p 0, p 1]⟩ ] }

/-- The wire tag, byte-pinned: `prep` carries a COLUMN (`c`), where `shr` carries an INDEX (`i`). -/
theorem prep_json_tag_carries_a_column :
    TExpr.toJson (p 3) = "{\"t\":\"prep\",\"c\":3}" := by decide

set_option maxRecDepth 8000 in
/-- The whole `prepDemo` emission, byte for byte — the artifact half of everything below. The
`maxRecDepth` raise is what buys the KERNEL rather than the compiled evaluator the `#guard` used:
this is `decide`, so `#assert_axioms` below can be the strong pin and not `#assert_compiled`. -/
theorem prepDemo_emits_golden : emitTableAirJson prepDemo =
    "{\"name\":\"prep-demo\",\"kind\":\"table_air\",\"ir\":2,\"width\":1,\"prep_width\":3,\"defs\":[],\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"prep\",\"c\":2}}}}],\"interactions\":[{\"bus\":\"ir2_exact_public_a2\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":0},\"tuple\":[{\"t\":\"prep\",\"c\":0},{\"t\":\"prep\",\"c\":1}]}]}" := by
  decide

theorem prepDemo_wellFormed : prepDemo.wellFormed = true := by decide

/-- ⚑ **THE TWO COLUMN SPACES DO NOT ANSWER FOR EACH OTHER**, at EVERY column index rather than at
index 0. A gate reading preprocessed column `c` does NOT read committed column `c`, and vice versa —
the pin a coverage claim or a mutation sweep rests on, and the one a single merged predicate would
silently get wrong in whichever direction the reader assumed. The range is wider than any table in
this file declares, so no member of the family sits outside it. -/
theorem the_two_column_spaces_never_answer_for_each_other :
    (List.range 8).all (fun c =>
      (!TExpr.readsColIn [] (p c) c) && TExpr.readsPrepColIn [] (p c) c &&
        TExpr.readsColIn [] (v c) c && (!TExpr.readsPrepColIn [] (v c) c)) = true := by decide

/-- …and the preprocessed predicate CHASES `shr` exactly as the committed one does, landing on the
ONE column the definition reads and no other. Stated as an iff against `c == 5` so the negative pole
is every other index, not the single hand-picked `4`. -/
theorem the_prep_predicate_chases_shr_to_exactly_one_column :
    (List.range 8).all (fun c =>
      TExpr.readsPrepColIn [.mul (p 5) (k 2)] (s 0) c == (c == 5)) = true := by decide

/-- ⚑ A `prep` read is NOT a next-row read, at any column: there is no `prepNxt`, so an `.all`-scoped
gate reading one is not the wrap-row hazard `readsNext` refuses. -/
theorem a_prep_read_is_never_a_next_row_read :
    (List.range 8).all (fun c => !TExpr.readsNextIn [] (p c)) = true := by decide

/-- …and `isRowLocal` says so of the table that does it. -/
theorem prepDemo_is_row_local : prepDemo.isRowLocal = true := by decide

/-- ⚑ **THE BOUND IS IN THE PREPROCESSED SPACE.** An out-of-range `prep` in a GATE is refused, even
though the same index is a legal committed column elsewhere. -/
theorem an_out_of_range_prep_gate_is_refused :
    ({ prepDemo with gates := [gAll (p 3)] } : TableAir).prepsInRange = false := by decide

/-- …and widening `width` does NOT launder it — the direction the two spaces make easy to get wrong. -/
theorem widening_width_does_not_launder_an_out_of_range_prep :
    ({ prepDemo with width := 64, gates := [gAll (p 3)] } : TableAir).wellFormed = false := by decide

/-- …the bus leg is bounded too: an out-of-range `prep` in a MULTIPLICITY is refused. -/
theorem an_out_of_range_prep_in_a_bus_leg_is_refused :
    ({ prepDemo with interactions := [⟨"b", .provide, p 9, [p 0]⟩] } : TableAir).wellFormed = false := by
  decide

/-- …and so is one hiding in a DEFINITION, which no gate-body scan would reach. -/
theorem an_out_of_range_prep_in_a_definition_is_refused :
    ({ prepDemo with defs := [p 7], gates := [gAll (v 0)] } : TableAir).prepsInRange = false := by
  decide

/-- ⚑ …and the TRUE pole, without which the four refusals above could be a predicate that is simply
always `false`: declare the width the definition needs and the same table is admitted. -/
theorem a_wide_enough_prepWidth_admits_the_definition :
    ({ prepDemo with prepWidth := 8, defs := [p 7], gates := [gAll (v 0)] }
      : TableAir).prepsInRange = true := by decide

#assert_axioms prep_json_tag_carries_a_column
#assert_axioms prepDemo_emits_golden
#assert_axioms prepDemo_wellFormed
#assert_axioms the_two_column_spaces_never_answer_for_each_other
#assert_axioms the_prep_predicate_chases_shr_to_exactly_one_column
#assert_axioms a_prep_read_is_never_a_next_row_read
#assert_axioms prepDemo_is_row_local
#assert_axioms an_out_of_range_prep_gate_is_refused
#assert_axioms widening_width_does_not_launder_an_out_of_range_prep
#assert_axioms an_out_of_range_prep_in_a_bus_leg_is_refused
#assert_axioms an_out_of_range_prep_in_a_definition_is_refused
#assert_axioms a_wide_enough_prepWidth_admits_the_definition

/-- ⚑ **THE PREPROCESSED LEAF IS READ FROM THE PREPROCESSED ROW.** The pin gate accepts exactly when
the committed column equals preprocessed column 2 — a witness where the two DIFFER is refused, and a
`prep` that read the committed row instead would accept it. -/
theorem prepDemo_pins_the_committed_column :
    prepDemo.RowHolds ⟨fun _ => 7, fun _ => 0, fun c => if c = 2 then 7 else 3⟩ false false := by
  decide

/-- …and the FALSE pole, which is the one that distinguishes the two row spaces: the SAME committed
row against a preprocessed row whose column 2 has moved is REFUSED. -/
theorem prepDemo_refuses_a_moved_pin :
    ¬ prepDemo.RowHolds ⟨fun _ => 7, fun _ => 0, fun c => if c = 2 then 8 else 3⟩ false false := by
  decide

/-- …and the pin does NOT read the committed NEXT row, nor any preprocessed column but 2: bending
column 0 and column 1 of the preprocessed row, and the whole `nxt` row, leaves the verdict where it
was. A gate that read the wrong prep column would move here. -/
theorem prepDemo_reads_only_prep_column_two :
    prepDemo.RowHolds ⟨fun _ => 7, fun _ => 99, fun c => if c = 2 then 7 else 41⟩ false false := by
  decide

/-- ⚑ …and the all-zero window ACCEPTS, which is why the false poles above are the load-bearing
half: an emission whose `prep` leaf silently read `0` would pass every honest-looking zero test. -/
theorem prepDemo_accepts_zero : prepDemo.RowHolds ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩ false false := by
  decide

/-- The all-zero window, an interior row (neither first nor last). -/
private def zeroEnv : TRowEnv := ⟨fun _ => 0, fun _ => 0, fun _ => 0⟩

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
