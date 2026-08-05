/-
# `Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit` — the COHORT universal boundary's AIR, in Lean.

## What this replaces

`Ir2Air::UMemBoundaryCohort` (`circuit/src/descriptor_ir2.rs`) is the width-9 SINGLE-ROW
specialization of the universal-memory boundary: the same `ir2_umem_check` Blum legs and the same
served `ir2_umem_addrs` closure table as the general boundary, with the inter-row lexicographic
comparator and the canonical key decomposition — 29 of the general boundary's 38 columns — DROPPED.
Its algebra was hand-authored Rust, which architectural law #1 forbids: *"circuits are emitted from
Lean; Rust only INTERPRETS."*

## ⚑ SAY THE SUBSTRATE OUT LOUD: this is Lean-authored AIR.

Every gate below is a Lean `TExpr` under an explicit `RowSel`. Nothing in this cutover
hand-writes a Rust constraint, and the `law1_no_new_rust_authored_constraints` baseline for
`descriptor_ir2.rs` goes DOWN.

## The comment-only claim this port turns into theorems — and the half it REFUTES

The deleted arm asserted, in prose:

> THE SINGLE-ROW TOOTH: at most one real row (row 0). Every transition forces the NEXT row to be
> a pad, so the declared address list has length ≤ 1 ⇒ `Nodup` is free. This is what licenses
> dropping the lexicographic comparator: there is never a second row to compare against.

That is the ENTIRE soundness licence for a table that drops a `Nodup`-establishing comparator, and
nothing checked it. §4 proves it and then draws the line the prose does not:

  * `every_row_after_the_first_is_a_pad` — from the emitted `.transition` gate under `Coherent`,
    rows `1 …` all carry `is_real = 0`. So at most ONE row is real and `Nodup` is
    `nodup_singleton` (Lean `UniversalMemory.universal_memory_sound_single`). ⚑ Note the shape: the
    gate reads ONLY `next.is_real`, so this is not "a pad may not be followed by a real" — it is
    "every row but the first is a pad", unconditionally, and it does NOT force row 0 to be real.
  * `canonical_none_is_forced` — an absent cell carries payload 0, on both images. That is what
    makes `(present, value)` a faithful encoding of `Option` (Lean `optOf`).
  * ⚠ `a_pad_row_can_still_serve_the_closure_table` — **THE FALSE POLE, and it is the one that
    matters here.** "The declared address list has length ≤ 1" is TRUE OF THE MULTISET, whose legs
    ride at `is_real`. It is NOT true of the SERVED `ir2_umem_addrs` table: that leg rides at
    `UBC_ADDR_MULT`, which NO gate reads, on EVERY row including the pads. A two-row window whose
    second row is a pad serving a DIFFERENT `(domain, key)` at multiplicity 7 satisfies every
    emitted gate. So the closure table this AIR serves is not a singleton, even though the
    declared list the `Nodup` argument is about is.

## ⚠ The containment, which lives in a DIFFERENT object

What stops a pad-served address from being useful is the `ir2_umem_check` multiset: the init `.send`
at serial 0 rides at `is_real`, so a pad publishes NOTHING, and a `umemOp` at a pad-served
`(domain, key)` has no serial-0 cell to consume. The permutation cannot balance. That is a property
of the assembled instance family — the half `TableAir.Holds` is silent about (`TableAirIR` §3) — and
it is written here because a reader of this table alone would take the single-row tooth to bound the
served table too. It bounds the multiset's declared list; the closure table it serves is bounded by
the multiset instead, one object further out.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Crypto enters nowhere.
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit

open Dregg2.Circuit.TableAirIR (TRowEnv)

open Dregg2.Circuit.TableAirIR
  (TExpr BusOp BusInteraction TableAir TableGate Coherent emitTableAirJson
   v n k eSub eOneMinus gBool gAll gTrans)

set_option autoImplicit false

/-! ## §1 — The deployed column layout.

Transcribed from `descriptor_ir2.rs`'s `UBC_*` constants; the `#guard`s derive each offset from the
one before it. -/

def UBC_DOMAIN : Nat := 0
def UBC_KEY : Nat := 1
def UBC_INIT_PRESENT : Nat := 2
def UBC_INIT_VALUE : Nat := 3
def UBC_FIN_PRESENT : Nat := 4
def UBC_FIN_VALUE : Nat := 5
def UBC_FIN_SERIAL : Nat := 6
def UBC_IS_REAL : Nat := 7
def UBC_ADDR_MULT : Nat := 8
/-- `UBC_WIDTH`. -/
def UBC_WIDTH : Nat := UBC_ADDR_MULT + 1

#guard UBC_WIDTH == 9

/-- The bus names, verbatim from the Rust `BUS_*` constants. -/
def BUS_BYTE : String := "ir2_byte"
def BUS_UMEM_CHECK : String := "ir2_umem_check"
def BUS_UMEM_ADDRS : String := "ir2_umem_addrs"

/-! ## §2 — THE TABLE. -/

/-- `is_real`, the row guard. -/
def gReal : TExpr := v UBC_IS_REAL

/-- The gate list, in the deleted Rust arm's emission order.

  * (1)(2)(3) `.all` — the row guard and both presence bits are boolean.
  * (4) `.transition` — ⚑ THE SINGLE-ROW TOOTH. `next.is_real = 0` on every transition, so rows
    `1 …` are pads and the declared address list has length ≤ 1. This is the whole licence for
    dropping the general boundary's lexicographic comparator.
  * (5)(6) `.all` — CANONICAL `none`: an absent cell carries payload 0, on both images. -/
def cohortGates : List TableGate :=
  [ gAll (gBool UBC_IS_REAL)
  , gAll (gBool UBC_INIT_PRESENT)
  , gAll (gBool UBC_FIN_PRESENT)
  , gTrans (n UBC_IS_REAL)
  , gAll (.mul (.mul gReal (eOneMinus (v UBC_INIT_PRESENT))) (v UBC_INIT_VALUE))
  , gAll (.mul (.mul gReal (eOneMinus (v UBC_FIN_PRESENT))) (v UBC_FIN_VALUE)) ]

/-- The bus interactions, in the deleted Rust arm's emission order.

  * the DOMAIN nibble query (multiplicity 1 as deployed — a pad row still queries, and its domain
    column is therefore range-bound even though nothing else about a pad is),
  * the two Blum legs, both at `is_real`: the init cell PUBLISHED at serial 0, the final cell
    CONSUMED,
  * and the `ir2_umem_addrs` closure table this AIR SERVES, at `UBC_ADDR_MULT`. -/
def cohortInteractions : List BusInteraction :=
  [ ⟨BUS_BYTE, .query, k 1, [v UBC_DOMAIN]⟩
  , ⟨BUS_UMEM_CHECK, .send, gReal,
      [v UBC_DOMAIN, v UBC_KEY, v UBC_INIT_PRESENT, v UBC_INIT_VALUE, k 0]⟩
  , ⟨BUS_UMEM_CHECK, .receive, gReal,
      [v UBC_DOMAIN, v UBC_KEY, v UBC_FIN_PRESENT, v UBC_FIN_VALUE, v UBC_FIN_SERIAL]⟩
  , ⟨BUS_UMEM_ADDRS, .provide, v UBC_ADDR_MULT, [v UBC_DOMAIN, v UBC_KEY]⟩ ]

/-- **`cohortTable`** — the cohort universal boundary's AIR, as a Lean object. -/
def cohortTable : TableAir :=
  { name         := "dregg-ir2-umem-boundary-cohort-v1"
  , width        := UBC_WIDTH
  , prepWidth    := 0
  , defs         := []
  , gates        := cohortGates
  , interactions := cohortInteractions }

/-! ## §3 — Shape pins. -/

#guard cohortTable.width == 9
#guard cohortTable.gates.length == 6
#guard cohortTable.busCount == 4
#guard cohortTable.busCountOn BUS_BYTE == 1
#guard cohortTable.busCountOn BUS_UMEM_CHECK == 2
#guard cohortTable.busCountOn BUS_UMEM_ADDRS == 1

-- ⚑ SELECTOR pins. EXACTLY ONE gate is transition-scoped, and it is the single-row tooth. A
-- re-scope to `.all` would bind the WRAP row (row n−1's `next` is row 0) and make an honest cohort
-- with a real row 0 UNSAT; a re-scope the other way (`.transition → .all` on a `.all` gate) accepts
-- strictly more (`TableGate.transition_weakens`). Either way the algebra is unchanged and only this
-- count moves.
#guard cohortTable.gateCountSel .all == 5
#guard cohortTable.gateCountSel .transition == 1
#guard cohortTable.gateCountSel .first == 0
#guard cohortTable.gateCountSel .last == 0

-- ⚑ BUS-SIDE pins. This table SERVES `ir2_umem_addrs` (the closure table `Ir2Air::UMemory`
-- queries) and QUERIES `ir2_byte`; a swap on either would leave every gate green.
#guard cohortTable.busCountOp BUS_UMEM_ADDRS .provide == 1
#guard cohortTable.busCountOp BUS_UMEM_ADDRS .query == 0
#guard cohortTable.busCountOp BUS_BYTE .query == 1
#guard cohortTable.busCountOp BUS_BYTE .provide == 0
#guard cohortTable.busCountOp BUS_UMEM_CHECK .send == 1
#guard cohortTable.busCountOp BUS_UMEM_CHECK .receive == 1

-- The table reads `nxt`, so it is not row-local — the reason it needed the second-pass IR.
#guard cohortTable.isRowLocal == false

/-! ## §4 — THE SINGLE-ROW TOOTH, PROVED — and the line the prose does not draw. -/

/-- The transition gate, unpacked: on any non-final row the NEXT window's guard vanishes. -/
theorem next_is_a_pad {rows : List TRowEnv}
    (hh : cohortTable.Holds rows) (i : Nat) (hlt : i < rows.length) (h : i + 1 < rows.length) :
    rows[i].nxt UBC_IS_REAL ≡ 0 [ZMOD 2013265921] := by
  have hg := hh i hlt ⟨.transition, n UBC_IS_REAL⟩ (by simp [cohortTable, cohortGates, gTrans])
  simp only [TableGate.holdsAt] at hg
  have hz := hg (by simp; omega)
  simpa [n, TExpr.evalWith] using hz

/-- ⚑ **THE SINGLE-ROW TOOTH.** On a COHERENT accepting trace every row after the first carries
`is_real = 0`. So AT MOST ONE declared address reaches the `ir2_umem_check` multiset, `Nodup` is
`nodup_singleton`, and dropping the general boundary's 29-column lexicographic comparator is sound
(Lean `UniversalMemory.universal_memory_sound_single`).

⚠ Two things this does NOT say, both of which the prose runs together:
  * it does not force row 0 to be real (a cohort with no declared address is admissible), and
  * it says nothing about what a PAD row SERVES — see §4b. -/
theorem every_row_after_the_first_is_a_pad {rows : List TRowEnv}
    (hc : Coherent rows) (hh : cohortTable.Holds rows) :
    ∀ i, ∀ h : i + 1 < rows.length, rows[i + 1].loc UBC_IS_REAL ≡ 0 [ZMOD 2013265921] := by
  intro i h
  have hlt : i < rows.length := by omega
  have hstep := next_is_a_pad hh i hlt h
  have hcoh : rows[i].nxt = rows[i + 1].loc := hc i h
  rwa [hcoh] at hstep

/-- **CANONICAL `none`.** On a real row an absent INIT cell carries payload 0 — what makes the
committed `(present, value)` pair a faithful encoding of `Option` (Lean `optOf`) rather than a pair
that merely happens to agree with one. -/
theorem canonical_none_is_forced {rows : List TRowEnv} (hh : cohortTable.Holds rows)
    (i : Nat) (h : i < rows.length)
    (hr : rows[i].loc UBC_IS_REAL = 1) (hp : rows[i].loc UBC_INIT_PRESENT = 0) :
    rows[i].loc UBC_INIT_VALUE ≡ 0 [ZMOD 2013265921] := by
  have hg := hh i h
    ⟨.all, .mul (.mul gReal (eOneMinus (v UBC_INIT_PRESENT))) (v UBC_INIT_VALUE)⟩
    (by simp [cohortTable, cohortGates, gAll])
  simp only [TableGate.holdsAt] at hg
  simp only [gReal, eOneMinus, eSub, v, k, TExpr.evalWith, hr, hp] at hg
  simpa using hg

/-! ### §4b — ⚠ THE FALSE POLE: the single-row tooth does NOT bound the served table. -/

/-- A TWO-ROW window: a real row 0 declaring `(domain 3, key 5)`, and a PAD row 1 that declares
nothing to the multiset — its Blum legs ride at `is_real = 0` — but SERVES `(domain 3, key 9)` to
`ir2_umem_addrs` at multiplicity 7, because `UBC_ADDR_MULT` is read by no gate. -/
def padServesRow0 : TRowEnv :=
  ⟨fun c =>
      if c = UBC_DOMAIN then 3
      else if c = UBC_KEY then 5
      else if c = UBC_IS_REAL then 1
      else if c = UBC_ADDR_MULT then 1
      else 0
  , fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- The pad that serves a SECOND key. Its `nxt` is all-zero, which is what a coherent two-row
trace's second window carries: `rows[1].nxt` is the wrap row and the tooth does not bind it. -/
def padServesRow1 : TRowEnv :=
  ⟨fun c =>
      if c = UBC_DOMAIN then 3
      else if c = UBC_KEY then 9
      else if c = UBC_ADDR_MULT then 7
      else 0
  , fun _ => 0, fun _ => 0, fun _ => 0⟩

/-- ⚑ **THE REFUTATION, ON THE EMITTED OBJECT.** Both windows satisfy every emitted gate — row 0 as
the FIRST row of a two-row trace, row 1 as its LAST — while the pad carries a different key and a
nonzero served multiplicity. So the sentence *"the declared address list has length ≤ 1"* is true of
the `ir2_umem_check` multiset (whose legs ride at `is_real`) and FALSE of the `ir2_umem_addrs`
closure table this AIR serves.

⚠ Direction: this is not a defect the deployed prover admits — the honest witness generator writes
`mult · is_real`, and a `umemOp` at a pad-served key still has no serial-0 cell to consume, so the
multiset refuses it. What it shows is that the refusal is the MULTISET's, one object further out,
and not the single-row tooth's. A soundness story that read the tooth as bounding the served table
would be resting on a leg this AIR does not have. -/
theorem a_pad_row_can_still_serve_the_closure_table :
    cohortTable.RowHolds padServesRow0 true false ∧
    cohortTable.RowHolds padServesRow1 false true ∧
    padServesRow1.loc UBC_IS_REAL = 0 ∧
    padServesRow1.loc UBC_ADDR_MULT = 7 ∧
    padServesRow1.loc UBC_KEY ≠ padServesRow0.loc UBC_KEY := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- ⚠ **NO GATE READS `UBC_ADDR_MULT`**, stated as an emission fact rather than as prose. -/
theorem addr_mult_is_read_by_no_gate :
    cohortTable.gates.all (fun g => !TExpr.readsColIn cohortTable.defs g.body UBC_ADDR_MULT) = true := by decide

/-- …nor `UBC_KEY`, which is why a pad may serve any key at all: the key column enters ONLY the two
Blum tuples and the served entry, never a gate. -/
theorem key_is_read_by_no_gate :
    cohortTable.gates.all (fun g => !TExpr.readsColIn cohortTable.defs g.body UBC_KEY) = true := by decide

/-- …and the CONTRAST, so the two predicates above are not vacuously true of every column: the row
guard is read by FOUR of the six gates — its own boolean, the single-row tooth (through `nxt`), and
both canonical-`none` legs. -/
theorem is_real_is_read_by_gates :
    (cohortTable.gates.filter (fun g => TExpr.readsColIn cohortTable.defs g.body UBC_IS_REAL)).length = 4 := by decide

/-! ### §4c — Non-vacuity, both poles of the GATES themselves. -/

/-- A real row 0 with a canonical `none` init image is ACCEPTED. -/
theorem an_honest_cohort_row_is_accepted : cohortTable.RowHolds padServesRow0 true false := by
  decide

/-- …and a SECOND REAL ROW is REFUSED: read as an interior window, row 0's transition gate fires on
a successor that claims `is_real = 1`. This is the single-row tooth going red, which is what makes
it a gate rather than a comment. -/
theorem a_second_real_row_is_refused :
    ¬ cohortTable.RowHolds
        (⟨fun c => if c = UBC_IS_REAL then 1 else 0
        , fun c => if c = UBC_IS_REAL then 1 else 0
        , fun _ => 0, fun _ => 0⟩) true false := by decide

/-- …and a NON-CANONICAL `none` (present = 0 with a nonzero payload) is REFUSED on a real row. -/
theorem a_non_canonical_none_is_refused :
    ¬ cohortTable.RowHolds
        (⟨fun c => if c = UBC_IS_REAL then 1 else if c = UBC_INIT_VALUE then 1 else 0
        , fun _ => 0, fun _ => 0, fun _ => 0⟩) true true := by decide

/-! ## §5 — The wire pin. -/

/-- The wire string the Rust interpreter ingests. -/
def UMEM_BOUNDARY_COHORT_JSON : String := emitTableAirJson cohortTable

-- THE WIRE PIN. Byte length plus the structural `#guard`s in §3 (6 gates, 4 interactions in a fixed
-- per-bus/per-side split, width 9). (The checked-in artifact is these bytes plus ONE trailing
-- newline, which `JsonCursor` skips as whitespace.)
#guard UMEM_BOUNDARY_COHORT_JSON.length == 1451

/-- The emission is not empty and not a stub. -/
theorem cohortTable_is_not_empty : cohortTable.gates ≠ [] := by
  simp [cohortTable, cohortGates]

end Dregg2.Circuit.Emit.UMemBoundaryCohortTableEmit
