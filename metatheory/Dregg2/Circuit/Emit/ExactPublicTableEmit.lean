/-
# `Dregg2.Circuit.Emit.ExactPublicTableEmit` — the EXACT-PUBLIC manifest table's AIR, AUTHORED IN LEAN.

## What this replaces — the ELEVENTH and LAST hand-written arm

`Ir2Air::ExactPublicTable` (`circuit/src/descriptor_ir2.rs`) realizes one Lean-emitted
`TableSem::ExactPublicRows` manifest as ONE multiplicity-bearing batch instance. It was the last
hand-authored Rust algebra in the IR-v2 instance family, and it is DELETED — the variant, not just
its body. `Ir2Air` is now `Main | LeanTable`.

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `TExpr` under an explicit `RowSel`. Nothing in this cutover hand-writes a
Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for `descriptor_ir2.rs`
goes DOWN.

## Why this one was last, and it was not size

The deleted arm was the SMALLEST of the eleven — one gate and one bus leg:

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

The whole cost was in the IR (`TableAirIR` §7): a `prep` expression leaf reading a SECOND column
space, a declared bound for that space, and a schema rather than a table. All four items are
discharged; §7 records what each cost.

## §0 — ⚑ THE PARAMETERIZATION, and the one design change it forced

This is not a table. It is a FAMILY indexed by the declared tuple ARITY, and one descriptor may
declare tables at several arities at once (`private-book-bfv-…-stage0-exact-public` declares arity
17 and arity 4 together). So the artifact is a JSON ARRAY of the same object the singleton path
already decodes — element `i` is arity `i + 1`, `EP_MAX_ARITY` of them.

⚑ **AND THE BUS NAME MOVED OUT OF THE STRING AND INTO THE TUPLE.** The deployed shape spent one
LogUp bus per declared table, `ir2_exact_public_{table_id}`, which is a number no artifact can know:
a per-arity family could not name its own bus, and §7 recorded exactly that as the reason "emit 64
artifacts" was not a way out. The fix is not a substitution hole in a wire string. It is to stop
spending a STRING on a separation a FIELD carries:

* the bus is `ir2_exact_public_a{arity}` — a function of the arity alone, which the artifact knows;
* the TABLE ID is preprocessed column 0, the first entry of every served tuple, and the query side
  (`Ir2Air::Main`) prepends the same descriptor-derived constant to every lookup.

⚠ **The separation is exactly as strong, and this is why.** LogUp balance is a multiset equality
over TUPLES. The id is a tuple field and it lives in the PREPROCESSED matrix — which the verifier
rebuilds from the descriptor rather than accepting from the prover — so an instance serving table
517 offers only tuples beginning `517`, and a query for 517 can be balanced by nothing else. Two
tables at the same arity share a bus and do not pool. ⓘ And the pre-existing co-batch hazard
(`prove_vm_descriptors2_batch`: two descriptors declaring the SAME wire id pool their capacity) is
preserved and NOT widened — same id still means the same tuples, which is the same defect it was.

## §0b — WHAT THE PORT PROVES, and the refutations are the load-bearing half

Four things this table asserted only in Rust prose, with what each turns out to be:

1. *"The multiplicities are PINNED to descriptor-derived constants, not left free"* — TRUE, in BOTH
   directions (`capacity_is_the_declared_multiplicity`, `+ …_refuses_a_free_capacity`).
2. ⚠ *"The manifest values … are PREPROCESSED, so they are verifier-known by construction"* — true
   of the PLUMBING and the sentence a reader takes away is false of the AIR: **NOT ONE manifest
   value, and not the table id, is bound by any gate of this table** (`the_gates_bind_no_manifest_value`,
   `the_gates_bind_no_table_id`). The whole tuple is admitted at any values. What binds it is that
   the verifier rebuilds the matrix — a fact about `ExactPublicManifest`, one object out, exactly
   like every other bus claim in this burn-down.
3. ⚠ *"Rows past `rows.len()` are all-zero pads carrying multiplicity ZERO, so they contribute
   nothing to the bus"* — the conclusion holds only GIVEN the verifier-built matrix. The gate forces
   the committed capacity to whatever the preprocessed column says, in either direction: a
   pad-SHAPED row (all-zero tuple) is admitted at capacity 5 the moment the preprocessed column
   reads 5 (`a_pad_shaped_row_is_admitted_at_any_capacity_the_matrix_declares`). The pad discipline
   is `ExactPublicManifest::preprocessed`'s, not this AIR's.
4. ⚠ *"a one-row manifest still commits two rows"* (`MIN_EXACT_PUBLIC_HEIGHT`) — a p3 fact this AIR
   neither knows nor enforces: every gate is `.all`-scoped, so `gates_admit_every_height` holds here
   for the same reason it holds of the byte table, and NOTHING in this AIR bounds the committed
   height. The byte table at least forces `value = row index`; this one does not even do that.

## Axiom hygiene
No `sorry`, no new axiom. Every shape pin, both wire goldens and both `RowHolds` poles are `decide`
— the KERNEL — and carry `#assert_axioms`.

⚑ ONE compiled pin, and it is a CONFESSION rather than a regression: the 63 428-byte family
artifact (`the_family_artifact_is_a_json_array_of_63428_bytes`) is past kernel reach (`decide`
exhausts `maxRecDepth 100000` at `maxHeartbeats 10000000` — measured), so it is `native_decide`
under `#assert_compiled`. That fact was ALREADY compiler-trusted when it was a `#guard`; `#guard`
runs the same `unsafe evalExpr` (`metatheory/docs/GUARD-DISCIPLINE.md`) and simply left no axiom
record. The line above used to read "no `native_decide`" and was true only because the compiler
trust was hiding somewhere `#assert_axioms` structurally cannot look.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.ExactPublicTableEmit

open Dregg2.Circuit.TableAirIR (TRowEnv)

-- ⚑ Every shape pin below is `decide`, i.e. the KERNEL, where the `#guard`s it replaces ran the
-- compiled evaluator. The family is 64 members wide and the emitter builds strings, so kernel
-- reduction needs the headroom; buying it here is what lets `#assert_axioms` be the pin instead of
-- `#assert_compiled`.
set_option maxRecDepth 100000

open Dregg2.Circuit.TableAirIR

set_option autoImplicit false

/-! ## §1 — The schema. -/

/-- ⚑ `MAX_EXACT_PUBLIC_ARITY` — the declared tuple-width ceiling. **This `def` is the SOURCE**;
`descriptor_ir2.rs`'s constant is the mirror, and every other Lean file that used to transcribe the
number now reads it from here.

The family carries one table per arity in `1 … EP_MAX_ARITY`.

⚠ The two sides are pinned against each other where it bites: `descriptor_ir2::check_descriptor2`
admits an arity against ITS constant, and `exact_public_lean_instance` REFUSES if the emitted
family's length is not that same number. Without that check a drift would let a descriptor pass
admission and then find no member — a dropped LogUp server, which is an unsatisfiable bus rather
than a loud failure.

## ⚑ FLAG DAY 2026-08-06: `64 → 97`, AND WHAT THE CAP TURNED OUT TO BOUND

Read at source before the raise, because the earlier draft of `MinaAccumulatorAir` §4 called 64 a
PRICE and it is not one. The constant has exactly **two** functional readers, and neither is a
resource:

* `check_descriptor2` (`descriptor_ir2.rs:2195`) — the admission refusal, and
* `exact_public_lean_instance` (`:6799`) — a DRIFT GUARD comparing it to
  `exact_public_table_air_family().len()`, i.e. **the member count of this file's own artifact**,
  whose message already names the remedy: *"re-emit `dregg-ir2-exact-public-v1.json` or re-pin the
  cap"*.

What actually bounds the verifier's allocation is `MAX_EXACT_PUBLIC_CELLS` (`rows · arity ≤ 2^25`)
and `MAX_EXACT_PUBLIC_ROWS` (`2^21`), and NEITHER moves with this ceiling — the committed
preprocessed matrix is `next_pow2(distinct) × (arity + 2)` and is priced by those two. So raising
this number costs the artifact's bytes and nothing else; `the_raise_costs_bytes_and_no_allocation`
states that as arithmetic rather than as a sentence.

⚑ `97 = 1 + 3 · 32` is the routing tuple of a PROJECTIVE PASTA POINT in the sound 8-bit encoding —
a key plus `3 × 32` limbs — which `MinaAccumulatorAir.the_routing_tuple_does_not_fit_one_table`
priced and `MinaAccumulatorAir.addendTable` now declares. The cap is set to exactly the widest
tuple any deployed descriptor needs, so the next descriptor that outgrows it moves this number
VISIBLY instead of finding room.

⚠ **AND THE RAISE INVALIDATES A DESIGN VERDICT, WHICH IS SAID HERE RATHER THAN LEFT TO ROT.**
`MinaWrapCommitMachine.one_hot_word_is_refused_at_this_register_count` justified an encoding change
with `73 > 64`. At 97 the one-hot word FITS, so that premise is dead; the theorem is restated there
against this `def` (not a transcription) and the encoding's surviving reason is the separate one it
already proves — `indexWord` is constant in the register count and `oneHotWord` is not.
`a-cost-verdict-outlives-its-premise`. -/
def EP_MAX_ARITY : Nat := 97

/-- The bus an arity-`a` exact-public table sits on. ⚑ A function of the ARITY, not of the table id:
the id rides in the tuple (§0). -/
def exactPublicBus (arity : Nat) : String := "ir2_exact_public_a" ++ toString arity

/-- The artifact/emission name of the arity-`a` member. -/
def exactPublicName (arity : Nat) : String :=
  "dregg-ir2-exact-public-a" ++ toString arity ++ "-v1"

/-- ⚑ **THE PREPROCESSED LAYOUT.** `[table_id, value_0 … value_{a−1}, multiplicity]`.

The id sits FIRST so the served tuple is a contiguous PREFIX (`prep 0 … prep a`) and the pinned
multiplicity is the single column past it — which is what makes the gate one `eSub` and the tuple
one `List.range`, rather than a list with a hole in it. -/
def EP_ID_COL : Nat := 0
/-- The first manifest VALUE column. -/
def EP_VALUE0 : Nat := 1
/-- The pinned multiplicity column of an arity-`a` member. -/
def epMultCol (arity : Nat) : Nat := arity + 1
/-- The declared preprocessed width of an arity-`a` member: id, `a` values, multiplicity. -/
def epPrepWidth (arity : Nat) : Nat := arity + 2

/-- The COMMITTED width: one column, the capacity this row offers. Everything else this table
reads is preprocessed. -/
def EP_WIDTH : Nat := 1
/-- The committed capacity column. -/
def EP_MULT : Nat := 0

/-- The served tuple: the table id then the `a` manifest values — a contiguous preprocessed prefix.
⚠ Its length is `arity + 1`, which is the LogUp field count the query side must match. -/
def epTuple (arity : Nat) : List TExpr := (List.range (arity + 1)).map p

/-- ⚑ **THE ONE GATE**: the committed capacity equals the DECLARED multiplicity. Free capacity here
would demote the manifest permutation to a containment, which is the whole reason the column is
pinned rather than left to the prover. -/
def epPinGate (arity : Nat) : TableGate := gAll (eSub (v EP_MULT) (p (epMultCol arity)))

/-- ⚑ **THE ONE BUS LEG**: this table SERVES (`.provide` = `LookupBus::table_entry`) its tuple at the
committed capacity. ⚠ `.query` here would make the bus unsatisfiable in one direction and vacuous in
the other, with no gate involved — which is why `BusOp` distinguishes the two sides at all. -/
def epServe (arity : Nat) : BusInteraction :=
  ⟨exactPublicBus arity, .provide, v EP_MULT, epTuple arity⟩

/-- **The arity-`a` member of the exact-public family.** -/
def exactPublicTable (arity : Nat) : TableAir :=
  { name         := exactPublicName arity
  , width        := EP_WIDTH
  , prepWidth    := epPrepWidth arity
  , defs         := []
  , gates        := [epPinGate arity]
  , interactions := [epServe arity] }

/-- **THE FAMILY**, element `i` at arity `i + 1`. -/
def exactPublicFamily : List TableAir :=
  (List.range EP_MAX_ARITY).map (fun i => exactPublicTable (i + 1))

/-! ## §2 — Shape pins, derived from the layout rather than transcribed. -/

theorem the_family_has_one_member_per_arity :
    exactPublicFamily.length = EP_MAX_ARITY := by decide

/-! ### ⚑ §2a — WHAT THE RAISE COSTS, as arithmetic.

The two deployed caps that DO bound an allocation, mirrored, plus the fact that the widest manifest
the raise newly admits still sits under both. Written as a theorem because "the cap bounds no
resource" is exactly the kind of sentence that survives its premise. -/

/-- `MAX_EXACT_PUBLIC_ROWS` (`descriptor_ir2.rs:590`). ⚠ A MIRROR of a Rust constant. -/
def EP_MAX_ROWS : Nat := 2 ^ 21
/-- `MAX_EXACT_PUBLIC_CELLS` (`descriptor_ir2.rs:592`). ⚠ A MIRROR of a Rust constant. -/
def EP_MAX_CELLS : Nat := 2 ^ 25
/-- The Step/Tick SRS width — the largest DISTINCT row count anything in this cone declares. -/
def EP_STEP_SRS : Nat := 2 ^ 16

/-- ⚑ **THE RAISE COSTS ARTIFACT BYTES AND NO ALLOCATION.**

`check_descriptor2`'s allocation refusal is `rows ≤ 2^21 ∧ rows · arity ≤ 2^25`, and the committed
preprocessed matrix is `next_pow2(distinct) · (arity + 2)`. At the widest thing this raise newly
admits — a `2^16`-row manifest at the full `EP_MAX_ARITY` — BOTH deployed bounds still hold with
room, and the committed matrix is `6 488 064` cells (26 MB at four bytes, ONE instance).

⚠ Note which comparison is doing the work: the cell cap is `19.4%` spent, so the arity ceiling was
never the binding constraint on this shape and moving it does not make the cell cap binding either.
The number that DOES move is the artifact's byte count, pinned below. -/
theorem the_raise_costs_bytes_and_no_allocation :
    EP_MAX_ARITY = 97
    ∧ EP_STEP_SRS ≤ EP_MAX_ROWS
    ∧ EP_STEP_SRS * EP_MAX_ARITY ≤ EP_MAX_CELLS
    ∧ EP_STEP_SRS * epPrepWidth EP_MAX_ARITY = 6488064
    ∧ 5 * (EP_STEP_SRS * EP_MAX_ARITY) < EP_MAX_CELLS := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The layout AS RENDERED at a deployed arity — the two column indices and the two names the
artifact and the descriptor have to agree on. Point-valued on purpose: `toString` is the part that
cannot be read off `epMultCol`'s definition. -/
theorem the_deployed_arity_17_member_renders :
    epPrepWidth 17 = 19 ∧ epMultCol 17 = 18 ∧
    exactPublicName 17 = "dregg-ir2-exact-public-a17-v1" ∧
    exactPublicBus 17 = "ir2_exact_public_a17" := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **EVERY member, at EVERY arity, is well-formed and has exactly the shape the deleted arm
had**: ONE gate, ONE bus leg, at committed width 1 with no definitions, and the single gate
`.all`-scoped. Four guards over the same quantifier, now one theorem over it. -/
theorem every_member_has_the_deleted_arms_shape :
    exactPublicFamily.all (fun t =>
      t.wellFormed && t.gates.length == 1 && t.busCount == 1 &&
        t.width == 1 && t.defCount == 0 && t.gateCountSel .all == 1) = true := by
  decide

/-- ⚑ …and every member is on the SERVING side of its own bus and on no other side of it — the
distinction that makes the bus satisfiable in one direction rather than vacuous in the other. -/
theorem every_member_serves_its_bus_and_never_queries_it :
    (List.range EP_MAX_ARITY).all (fun i =>
      ((exactPublicTable (i + 1)).busCountOp (exactPublicBus (i + 1)) .provide == 1) &&
        ((exactPublicTable (i + 1)).busCountOp (exactPublicBus (i + 1)) .query == 0)) = true := by
  decide

/-- ⚑ **THE LOGUP FIELD COUNT, per arity**: the served tuple is `arity + 1` wide (id ‖ values), which
is what the query side must present, and the declared preprocessed width covers that tuple AND the
pin with nothing spare. A family whose members drifted here would balance nothing. -/
theorem the_logup_field_count_is_arity_plus_one :
    (List.range EP_MAX_ARITY).all (fun i =>
      ((epTuple (i + 1)).length == i + 2) &&
        (epPrepWidth (i + 1) == (epTuple (i + 1)).length + 1)) = true := by
  decide

/-- ⚑ **THE FAMILY IS ROW-LOCAL AT EVERY ARITY**, which is a claim about the selector and not about
the body: nothing here reads the next row, so no member has a wrap-row hazard and none needs a
`.transition` scope. A re-emission that re-scoped the pin would leave the algebra byte-identical and
accept strictly more (`TableGate.transition_weakens`), so this is pinned rather than eyeballed. -/
theorem the_family_is_row_local : exactPublicFamily.all (fun t => t.isRowLocal) = true := by
  decide

/-- ⚑ …and the one gate reads the committed CAPACITY column, at every arity: without this the
row-locality pin above would be about a gate that reads no committed column at all. -/
theorem the_one_gate_reads_the_committed_capacity :
    (List.range EP_MAX_ARITY).all (fun i =>
      let t := exactPublicTable (i + 1)
      t.gates.all (fun g => TExpr.readsColIn t.defs g.body EP_MULT)) = true := by
  decide

/-! ## §3 — The wire golden, byte-pinned at two arities.

The whole family is a function of `EP_MAX_ARITY`, so pinning every member's bytes would pin the
same emitter 64 times. What is pinned instead is the SMALLEST member and one deployed arity, plus
the family's length and per-member shape above — which together move if the emitter moves. -/

theorem the_arity_1_member_emits_golden : emitTableAirJson (exactPublicTable 1) =
  "{\"name\":\"dregg-ir2-exact-public-a1-v1\",\"kind\":\"table_air\",\"ir\":2,\"width\":1,\"prep_width\":3,\"defs\":[],\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"prep\",\"c\":2}}}}],\"interactions\":[{\"bus\":\"ir2_exact_public_a1\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":0},\"tuple\":[{\"t\":\"prep\",\"c\":0},{\"t\":\"prep\",\"c\":1}]}]}" := by
  decide

theorem the_arity_3_member_emits_golden : emitTableAirJson (exactPublicTable 3) =
  "{\"name\":\"dregg-ir2-exact-public-a3-v1\",\"kind\":\"table_air\",\"ir\":2,\"width\":1,\"prep_width\":5,\"defs\":[],\"gates\":[{\"sel\":\"all\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"loc\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"prep\",\"c\":4}}}}],\"interactions\":[{\"bus\":\"ir2_exact_public_a3\",\"op\":\"provide\",\"mult\":{\"t\":\"loc\",\"c\":0},\"tuple\":[{\"t\":\"prep\",\"c\":0},{\"t\":\"prep\",\"c\":1},{\"t\":\"prep\",\"c\":2},{\"t\":\"prep\",\"c\":3}]}]}" := by
  decide

/-- The family artifact's byte source. -/
def EXACT_PUBLIC_FAMILY_JSON : String := emitTableAirFamilyJson exactPublicFamily

/-- The artifact is an ARRAY of exactly this many bytes, opening and closing as one. The length is
the number a re-emission has to reproduce, so it is the load-bearing half.

⚑ **MOVED BY THE 2026-08-06 RAISE: `63 428 → 128 141` characters (`+102.0%`).** That doubling is the
WHOLE price of `64 → 97` — the artifact is `O(EP_MAX_ARITY²)` because member `a` renders `a + 1`
tuple entries — and it is the only number the raise moves that anyone pays. `128 142` bytes on disk
(the driver appends one newline). -/
theorem the_family_artifact_is_a_json_array_of_128141_bytes :
    (EXACT_PUBLIC_FAMILY_JSON.length == 128141) &&
      (EXACT_PUBLIC_FAMILY_JSON.take 1).endsWith "[" &&
      (EXACT_PUBLIC_FAMILY_JSON.drop (EXACT_PUBLIC_FAMILY_JSON.length - 1)) == "]" := by
  native_decide

/-! ## §4 — ⚑ WHAT THE ONE GATE FORCES, both directions.

The arity-2 member stands in for the family: every member differs from it only in the tuple length
and the index of the pinned column, and §2 pins both of those at every arity. -/

/-- The arity-2 member — the smallest one with a manifest value on each side of the id. -/
def ep2 : TableAir := exactPublicTable 2

/-- A row window: committed capacity `m`, preprocessed `[id, v0, v1, mult]`. -/
def epRow (m id v0 v1 mult : ℤ) : TRowEnv :=
  ⟨fun c => if c = 0 then m else 0
  , fun _ => 0
  , fun c => if c = 0 then id else if c = 1 then v0 else if c = 2 then v1 else mult⟩

/-- ⚑ **THE COMMITTED CAPACITY IS THE DECLARED MULTIPLICITY.** The direction the doc asserts: a row
whose committed column carries the declared count is accepted, at a duplicate-bearing manifest entry
(multiplicity 2) so the pin is distinguishable from a constant-1 gate. -/
theorem capacity_is_the_declared_multiplicity :
    ep2.RowHolds (epRow 2 517 30 40 2) false false := by decide

/-- …and the FALSE pole, which is what makes the pin a gate: a row offering MORE capacity than the
manifest declares is REFUSED. Free capacity here would demote the exact-public permutation to a
CONTAINMENT, so this refutation is the soundness content of the whole table. -/
theorem the_pin_refuses_a_free_capacity :
    ¬ ep2.RowHolds (epRow 3 517 30 40 2) false false := by decide

/-- …and LESS capacity is refused too. Stated separately because a one-sided pin (`committed ≤
declared`) is the shape a reader might assume from the word "capacity", and it is not what the gate
says: the gate is an EQUALITY. -/
theorem the_pin_refuses_a_short_capacity :
    ¬ ep2.RowHolds (epRow 1 517 30 40 2) false false := by decide

/-! ## §5 — ⚠ THE REFUTATIONS: what the gates do NOT bind. -/

/-- ⚑ **NOT ONE MANIFEST VALUE IS GATE-BOUND.** The same committed capacity against a preprocessed
row whose manifest VALUES are arbitrary garbage satisfies every gate of this table, exactly as the
honest row does. The tuple is 100% of this table's soundness content and 0% of its algebra.

⚠ This is the refutation of the sentence a reader takes from *"the manifest values … are PREPROCESSED,
so they are verifier-known by construction"*: the plumbing claim is true, and the AIR is not what
makes it true. What binds the values is that `ExactPublicManifest::preprocessed` rebuilds them from
the descriptor on BOTH sides — a different object, and the same shape of containment as every other
bus leg in this burn-down. -/
theorem the_gates_bind_no_manifest_value :
    ep2.RowHolds (epRow 2 517 30 40 2) false false ∧
    ep2.RowHolds (epRow 2 517 999999 (-7) 2) false false := by
  refine ⟨by decide, by decide⟩

/-- ⚑ …and NOT THE TABLE ID EITHER, which is the field the whole per-instance separation now rests
on (§0). No gate reads preprocessed column 0. The separation is a LogUp fact about a
verifier-rebuilt column, not an algebraic one — stated here because moving the id from a bus NAME
into a bus TUPLE would otherwise read as moving it from unenforced to enforced, and it does not. -/
theorem the_gates_bind_no_table_id :
    ep2.RowHolds (epRow 2 517 30 40 2) false false ∧
    ep2.RowHolds (epRow 2 0 30 40 2) false false := by
  refine ⟨by decide, by decide⟩

/-- …and that is decidable on the EMITTED object rather than read off two witnesses: no gate of any
member reads the id column or any manifest value column of the preprocessed matrix. -/
theorem no_gate_reads_the_id_or_any_manifest_value :
    (List.range EP_MAX_ARITY).all (fun i =>
      let t := exactPublicTable (i + 1)
      (List.range (i + 2)).all (fun c =>
        t.gates.all (fun g => !TExpr.readsPrepColIn t.defs g.body c))) = true := by
  decide

/-- …while the pinned column IS read, at every arity. Without this the refutation above would be a
claim about a gate that reads nothing. -/
theorem the_pinned_multiplicity_column_is_read_at_every_arity :
    (List.range EP_MAX_ARITY).all (fun i =>
      let t := exactPublicTable (i + 1)
      t.gates.all (fun g => TExpr.readsPrepColIn t.defs g.body (epMultCol (i + 1)))) = true := by
  decide

/-- ⚑ **THE PAD DISCIPLINE IS NOT THIS AIR'S.** *"Rows past `rows.len()` are all-zero pads carrying
multiplicity ZERO, so they contribute nothing to the bus"* — the conclusion is true of the matrix
the verifier builds and is NOT a property of the gate. A pad-SHAPED row (all-zero tuple) is admitted
at capacity 5 the moment the preprocessed multiplicity column reads 5, and the gate has no opinion
about which rows are pads.

That matters because a reader of the arm alone would take "pads contribute nothing" for a tooth. It
is a fact about `ExactPublicManifest::preprocessed`'s `values.resize(.., F::ZERO)`. -/
theorem a_pad_shaped_row_is_admitted_at_any_capacity_the_matrix_declares :
    ep2.RowHolds (epRow 5 0 0 0 5) false false ∧
    ¬ ep2.RowHolds (epRow 5 0 0 0 0) false false := by
  refine ⟨by decide, by decide⟩

/-- …and the direction the deployed matrix actually produces: a pad row whose declared multiplicity
is zero forces the committed capacity to zero, so it really does offer nothing. Both halves are
needed — the first says the AIR does not enforce the discipline, this says the discipline is
enforceable and the matrix enforces it. -/
theorem a_declared_pad_offers_no_capacity :
    ep2.RowHolds (epRow 0 0 0 0 0) false false ∧
    ¬ ep2.RowHolds (epRow 1 0 0 0 0) false false := by
  refine ⟨by decide, by decide⟩

/-- ⚑ **THE AIR DOES NOT BOUND ITS OWN HEIGHT** — the same shape the byte table's
`gates_admit_every_height` found, and weaker here, because this table does not even force
`value = row index`. Every gate is `.all`-scoped, so ANY list of rows that individually satisfy the
pin satisfies the whole table; a manifest instance of any length whatever passes.

⚠ So `MIN_EXACT_PUBLIC_HEIGHT`'s *"a one-row manifest still commits two rows"* is a p3 fact this AIR
neither knows nor enforces, and the height contract is `ProverData::from_airs_and_degrees`'s. -/
theorem gates_admit_every_height (n : Nat) :
    ep2.Holds ((List.range n).map (fun _ => epRow 2 517 30 40 2)) := by
  have hrow : ∀ (f l : Bool), ep2.RowHolds (epRow 2 517 30 40 2) f l := by
    intro f l g hg
    simp only [ep2, exactPublicTable, List.mem_cons, List.not_mem_nil, or_false] at hg
    subst hg
    show _ ≡ 0 [ZMOD 2013265921]
    decide
  intro i h
  simp only [List.getElem_map]
  exact hrow _ _

/-! ## §6 — ⚠ HONEST SCOPE.

`TableAir.Holds` quantifies over GATES ONLY (`TableAirIR` §3), and this table has exactly one gate,
which copies a verifier-known number into a committed column. So `ep2.Holds rows` says precisely
*"the prover wrote down the capacities the descriptor declares"* — nothing about membership, nothing
about the manifest, nothing about exactness. The exactness is the LogUp balance of the whole batch
against `Ir2Air::Main`'s query side, and it lives with the batch soundness results.

⚑ That is not a weakening introduced by the port: the deleted Rust arm had the identical content,
and the difference is that the scope is now stated in the object rather than in a comment. -/

/-- The stand-in member really is the one-gate, one-bus-leg object the scope note describes. -/
theorem ep2_has_one_gate_and_one_bus_leg :
    ep2.busCount = 1 ∧ ep2.gates.length = 1 := by
  refine ⟨by decide, by decide⟩

#assert_axioms the_family_has_one_member_per_arity
#assert_axioms the_raise_costs_bytes_and_no_allocation
#assert_axioms the_deployed_arity_17_member_renders
#assert_axioms every_member_has_the_deleted_arms_shape
#assert_axioms every_member_serves_its_bus_and_never_queries_it
#assert_axioms the_logup_field_count_is_arity_plus_one
#assert_axioms the_one_gate_reads_the_committed_capacity
#assert_axioms the_arity_1_member_emits_golden
#assert_axioms the_arity_3_member_emits_golden
#assert_compiled the_family_artifact_is_a_json_array_of_128141_bytes
#assert_axioms no_gate_reads_the_id_or_any_manifest_value
#assert_axioms the_pinned_multiplicity_column_is_read_at_every_arity
#assert_axioms ep2_has_one_gate_and_one_bus_leg

end Dregg2.Circuit.Emit.ExactPublicTableEmit
