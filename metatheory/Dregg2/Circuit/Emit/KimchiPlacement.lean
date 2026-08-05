/-
# Dregg2.Circuit.Emit.KimchiPlacement — the Snarky-style PLACEMENT + COPY-PERMUTATION pass (R1)

## ⚑ THE RUNG THIS IS (R1, the keystone), AND WHAT IT IS NOT

`KimchiTarget.KRow` carries `wires : List Nat` = VARIABLE INDICES, PRE-placement (its "Two
deliberate departures" note). o1js, after synthesis, emits `PERMUTS = 7` placement cells `{row,col}`
per gate — the copy-constraint (sigma) targets produced by the wiring pass. `KimchiCustomGates`
measured this exact gap: `typ`/`coeffs` byte-exact, **`wires` diverges structurally** because dregg
had NO placement pass. **This file IS that pass.** It turns a variable-in-cell grid (Snarky's
`rows_rev`) plus the public-input size into the placed circuit: each variable's cells collected into
an equivalence class, the class SORTED and rotated into a permutation cycle, and every one of the 7
permutation columns of every row wired to the next cell in its cycle. The emitted `{row,col}` wires
are then **byte-comparable to o1js**.

This is **Phase A** — the placed wires are established DIFFERENTIALLY, byte-diffed against o1js's own
`Provable.constraintSystem(f).gates[i].wires` (`bridge/mina-zkapp/scripts/pickles-placement-oracle.mjs`,
o1js 2.15.0). It is **NOT** a soundness proof and **NOT** "machine-checked Pickles."

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The placement algorithm below is authored in Lean, transcribed
from Mina's Snarky backend `plonk_constraint_system.ml` (o1js vendored copy, READ-ONLY):

  * `Row`/`Position` — `plonk_constraint_system.ml:53-105` (`Position.t = {row; col}`; public-input
    rows first, `Public_input i` sorts before `After_public_input j`).
  * `add_row` — `:1131-1150`: for `col ∈ 0..min(PERMUTS,|vars|)`, wire `vars[col]` at `{next_row,col}`.
  * `wire'` — `:1121-1123`: records the cell into the variable's equivalence class.
  * `equivalence_classes_to_hashtbl` — `:917-943`: merge classes by union-find root, **sort each
    class by `[%compare: Row.t Position.t]`, ROTATE LEFT, map cell → next-in-cycle** (last wraps to
    first; a singleton maps to itself).
  * `finalize_and_get_gates` — `:1156-1253`: public-input rows 0..P-1 (Generic, `coeffs=[1,0,0,0,0]`,
    col 0 wired to `External row`), then circuit rows P.., each gate's `wired_to = Array.init 7 (fun
    col => permutation {row; col})`; a cell not in any class self-wires.

o1js is a READ-ONLY ORACLE supplying the byte target (`gates[i].wires`). No Rust or TypeScript
authors placement here.

## ⚑ internal_vars — R3's named residual, MODELLED here

R3 (`PicklesStatementDiff.lean`) left one residual: `internal_vars` — "the witness-placement recipe
… has no dregg model." This file gives it a model: `InternalVarDef` is exactly the mina-rust blob
shape `InternalVarsRaw = HashMap<u32,(Vec<(BigInt,VRaw)>,Option<BigInt>)>` (`mina-rust
crates/ledger/src/proofs/provers.rs:284-293`; consumed by `compute_witness` `transaction.rs:3822`),
and `PGate.permVars` is the `rows_rev` grid (`Vec<Vec<Option<VRaw>>>`, same source). So R1 CLOSES the
"no dregg model" half of the residual. The remaining sub-residual is the ORACLE: o1js's
`constraintSystem` JSON does not expose internal_vars, so its byte-diff needs the circuit-blobs
`*_internal_vars.bin`/`*_rows_rev.bin` binprot dump — named, not a zero-build o1js oracle. The
PLACEMENT (`wires`) IS zero-build-diffable and is the gate below.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`.
NEW file. Imports `KimchiTarget` only (for `KGateType`, `K_PERMUTS`).
-/
import Dregg2.Circuit.Emit.KimchiTarget

namespace Dregg2.Circuit.Emit.KimchiPlacement

open Dregg2.Circuit.Emit.KimchiTarget

set_option autoImplicit false

/-! ## §1 — the data model: variables, cells, grid rows.

`V.t` (`plonk_constraint_system.ml:686-689`) is `External of int | Internal of Internal_var.t`;
`VRaw` (mina-rust `provers.rs:286-289`) serializes it as `External(u32) | Internal(u32)`. -/

/-- A Snarky constraint-system variable: a witness/public-input (`external`) or an auxiliary
reduction variable (`internal`). Matches `V.t` / `VRaw`. -/
inductive PVar where
  | external : Nat → PVar
  | internal : Nat → PVar
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A cell = a `(row, col)` position (`Position.t`, `:73-77`). `row`/`col` are absolute. -/
structure Cell where
  row : Nat
  col : Nat
  deriving DecidableEq, Repr, Inhabited, BEq

/-- **A placement-input gate.** `permVars` are the (up to `K_PERMUTS = 7`) permutation-column
variables of the row — `Some v` = the variable in that column, `None` = an unwired column (advice
columns 7..14 do not permute and are not carried here). This IS one row of Snarky's `rows_rev`,
truncated to the permutation columns. `kind`/`coeffs` are the emitted `typ`/`coeffs` (carried
through unchanged; placement never touches them). -/
structure PGate where
  kind : KGateType
  permVars : List (Option PVar)
  coeffs : List Int
  deriving Repr, Inhabited

/-- **A placed gate.** `wires` is the `K_PERMUTS = 7` `{row,col}` copy-constraint cells o1js emits. -/
structure PlacedGate where
  kind : KGateType
  wires : List Cell
  coeffs : List Int
  deriving Repr, DecidableEq, Inhabited

/-! ## §2 — the permutation math: sort a class, rotate left, map cell → next-in-cycle.

`equivalence_classes_to_hashtbl` (`:936-942`): `ps |> sort |> (fun ps -> zip ps (rotate_left ps))`,
mapping each cell to the next in the sorted cycle, the last wrapping to the first. -/

/-- Cell ordering: `(row,col)` lexicographic, matching `[%compare: Row.t Position.t]` (a
`Public_input i` sorts before `After_public_input j` — reproduced here by absolute rows, since
`Public_input i ↦ i < P ≤ j+P ↦ After_public_input j`). -/
def cellLt (a b : Cell) : Bool :=
  a.row < b.row || (a.row == b.row && a.col < b.col)

/-- Insert into a `cellLt`-sorted list. -/
def insertCell (c : Cell) : List Cell → List Cell
  | [] => [c]
  | d :: ds => if cellLt c d then c :: d :: ds else d :: insertCell c ds

/-- Insertion sort by `cellLt`. The class is a `Hash_set` of DISTINCT cells (`:931,939`), so the
order is unambiguous and stability is moot. -/
def sortCells : List Cell → List Cell
  | [] => []
  | c :: cs => insertCell c (sortCells cs)

/-- `rotate_left` (`:937`): `x :: xs ↦ xs ++ [x]`. -/
def rotateLeft {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

/-- The cycle map of ONE equivalence class: sort its cells, then pair each with the next
(`zip ps (rotate_left ps)`). A singleton maps to itself. -/
def cyclePairs (cs : List Cell) : List (Cell × Cell) :=
  let s := sortCells cs
  s.zip (rotateLeft s)

/-! ## §3 — collecting cells per variable (the equivalence classes).

`wire` records `{row,col}` into the variable's class (`:1121-1123`); a class is deduplicated by
`Hash_set.of_list` (`:931`). Union-find (`:764`) only merges classes when `assert_equal` unions two
DISTINCT variables — the R1 copy circuits create their copies from the SAME variable in several
cells, so class = "cells of one variable" with no merge.

⚑ **`assert_equal` NOW EXISTS**, in `Dregg2.Circuit.Emit.KimchiAssertEqual`: a zero-row union-find
over `PVar` composed at `circuitPositions` (`mergedPositions`/`placeWith`), with a fail-closed entry
`placeCheckedMerged` that routes through `placeCheckedWith` below on the post-merge gate list, so H1,
the dead-gap refusal and H2 are the ones running and cannot be weakened there. `place` and
`circuitPositions` are UNCHANGED — `placeWith ms` at `ms = []` is `place`, proved. -/

/-- One grid row's `(variable, cell)` positions, cols `0..`, skipping `None`. Truncated to
`K_PERMUTS` by the caller (`add_row`'s `min permutation_cols`). -/
def rowPositionsFrom (absRow col : Nat) : List (Option PVar) → List (PVar × Cell)
  | [] => []
  | none :: rest => rowPositionsFrom absRow (col + 1) rest
  | some v :: rest => (v, ⟨absRow, col⟩) :: rowPositionsFrom absRow (col + 1) rest

def rowPositions (absRow : Nat) (pv : List (Option PVar)) : List (PVar × Cell) :=
  rowPositionsFrom absRow 0 (pv.take K_PERMUTS)

/-- **All `(variable, cell)` positions of a circuit**, in Snarky's recording order: the public-input
cells (`External i` at `{i,0}`, `:1189-1191`) first, then each circuit gate's cells at absolute row
`P + gateIndex` (`:1142-1143`, `Row.After_public_input`). -/
def circuitPositions (pubSize : Nat) (gates : List PGate) : List (PVar × Cell) :=
  (List.range pubSize).map (fun i => (PVar.external i, (⟨i, 0⟩ : Cell)))
    ++ (gates.zip (List.range gates.length)).flatMap
        (fun ggi => rowPositions (pubSize + ggi.2) ggi.1.permVars)

/-- The (deduplicated) cells of variable `v` — its equivalence class (`Hash_set.of_list data`).
**This is the SPEC** of the variable→cells direction: one filter of the whole position list per
query. `permPairs` answers the same question for EVERY variable at once out of `varBuckets`; the
two are pinned equal in §3b. -/
def classCells (poss : List (PVar × Cell)) (v : PVar) : List Cell :=
  ((poss.filter (fun p => p.1 == v)).map (·.2)).dedup

/-- The distinct variables, as `List.dedup` orders them — **SPEC**; `distinctVars` computes the same
list in one pass. `List.dedup = pwFilter (· ≠ ·)` keeps an element only when it does not RECUR
later, so the order is that of each variable's LAST occurrence
(`[1,2,3,1,2,4].dedup = [3,1,2,4]`), not first-appearance. -/
def distinctVarsSpec (poss : List (PVar × Cell)) : List PVar :=
  (poss.map (·.1)).dedup

/-! ### §3a — THE INDEX: what makes `place` linear instead of quadratic.

`place` asks three questions, and each was answered by a SCAN of a whole list per query:

  * *which variables are there* — `List.dedup`, O(P²) in the position count;
  * *which cells does variable `v` own* — `classCells`, one `filter` of all P positions per
    variable, so O(V·P);
  * *what does cell `c` wire to* — `permLookup`, a `find?` over ALL σ pairs, called `7·nRows` times,
    so O(nRows·P) — the dominant term.

MEASURED at the step_main-fragment scale rung (`KimchiComposeStepFragment`, commit `3c3f61b24`):
`place` took 170 / 1941 / 25707 ms at 454 / 1674 / 4058 rows — a fitted exponent of **1.95**, i.e.
genuinely quadratic, extrapolating to ~48 min at `step_main`'s ~17,806 rows.

The fix is an INDEX built ONCE per circuit and read in O(1): a `varIx`-keyed bucket array for the
variable→cells direction and a row-keyed bucket array for the cell→successor direction. Both are
`Array`+`List` (NOT `Std.HashMap`) deliberately: `Array.replicate`/`Array.modify`/`Array.getD` all
reduce in the KERNEL, so §6's `by decide` byte pins against o1js still hold on the same
definitions the interpreter runs. Nothing about the emitted object changes — §3b pins that. -/

/-- Bucket index of a variable: `external n ↦ 2n`, `internal n ↦ 2n+1`. Injective, so one array
indexed by it separates every variable with no collision to resolve. -/
def varIx : PVar → Nat
  | .external n => 2 * n
  | .internal n => 2 * n + 1

/-- One past the largest `varIx` present — the bucket-array size (so it is O(#variables), not O(id
space); a sparse allocation would only cost empty buckets, never correctness). -/
def varIxBound (poss : List (PVar × Cell)) : Nat :=
  poss.foldl (fun m p => Nat.max m (varIx p.1 + 1)) 0

/-- **THE VARIABLE → CELLS INDEX**, one pass: bucket `varIx v` holds `v`'s cells in RECORDING order
(fold the reversed list and cons, so the first-recorded cell ends up at the head — the same order
`classCells`' `filter` produces). -/
def varBuckets (poss : List (PVar × Cell)) : Array (List Cell) :=
  poss.reverse.foldl (fun a p => a.modify (varIx p.1) (p.2 :: ·))
    (Array.replicate (varIxBound poss) [])

/-- The distinct variables, in `distinctVarsSpec`'s (= `List.dedup`'s) order, in ONE pass: scan
right-to-left with a `varIx`-indexed seen-array and cons the FIRST sighting from the right — which
is exactly each variable's LAST occurrence, prepended so the surviving order is preserved. -/
def distinctVars (poss : List (PVar × Cell)) : List PVar :=
  (poss.reverse.foldl
      (fun (st : Array Bool × List PVar) p =>
        let i := varIx p.1
        if st.1.getD i false then st else (st.1.set! i true, p.1 :: st.2))
      (Array.replicate (varIxBound poss) false, [])).2

/-- **The whole permutation**, as a `Cell → Cell` association list: every class's cycle pairs.
Reads each class out of `varBuckets` instead of re-filtering the position list per variable. -/
def permPairs (poss : List (PVar × Cell)) : List (Cell × Cell) :=
  let bs := varBuckets poss
  (distinctVars poss).flatMap (fun v => cyclePairs ((bs.getD (varIx v) []).dedup))

/-- **SPEC** of `permPairs`: the scanning definition, kept as the differential reference §3b pins
`permPairs` against (and as the readable statement of what the index computes). -/
def permPairsSpec (poss : List (PVar × Cell)) : List (Cell × Cell) :=
  (distinctVarsSpec poss).flatMap (fun v => cyclePairs (classCells poss v))

/-- `permutation pos` (`:1202-1203`): the next cell in `pos`'s cycle, or `pos` itself if `pos` is
in no class (an unwired column / advice cell). **SPEC** of the cell→successor direction — a scan of
all pairs; `place` uses `pairsByRow`/`placedWiresAt` instead. -/
def permLookup (pairs : List (Cell × Cell)) (c : Cell) : Cell :=
  match pairs.find? (fun p => p.1 == c) with
  | some p => p.2
  | none => c

/-! ## §4 — the placement pass. -/

/-- A row's 7 wired cells: `Array.init K_PERMUTS (fun col => permutation {row; col})` (`:1210-1211`).
**SPEC** of one row's wiring; `place` uses `placedWiresAt`. -/
def placedWires (pairs : List (Cell × Cell)) (absRow : Nat) : List Cell :=
  (List.range K_PERMUTS).map (fun col => permLookup pairs ⟨absRow, col⟩)

/-- **THE CELL → SUCCESSOR INDEX**, bucketed by SOURCE ROW, one pass. Bucket `r` holds the σ pairs
whose source cell lies in row `r`, in list order (so `find?`'s first-match semantics is preserved —
though sources are in fact unique: every `(row,col)` carries at most one variable). A pair whose
source row is ≥ `nRows` is dropped by `Array.modify`'s out-of-bounds no-op, and such a row is never
queried. -/
def pairsByRow (nRows : Nat) (pairs : List (Cell × Cell)) : Array (List (Cell × Cell)) :=
  pairs.reverse.foldl (fun a p => a.modify p.1.row (p :: ·)) (Array.replicate nRows [])

/-- `placedWires` against the row index. Every pair in bucket `absRow` has source row `absRow`, so
testing the COLUMN alone is the same test as testing the whole cell — over a bucket of at most
`K_PERMUTS = 7` entries instead of the whole pair list. -/
def placedWiresAt (rowIdx : Array (List (Cell × Cell))) (absRow : Nat) : List Cell :=
  let bs := rowIdx.getD absRow []
  (List.range K_PERMUTS).map (fun col =>
    match bs.find? (fun p => p.1.col == col) with
    | some p => p.2
    | none => (⟨absRow, col⟩ : Cell))

/-- **THE PLACEMENT PASS.** `finalize_and_get_gates` (`:1156-1253`): public-input Generic rows first
(`coeffs=[1,0,0,0,0]`), then the circuit gates, each carrying its 7 placed `{row,col}` wires. This
is the object whose `wires` field is byte-diffed against o1js. -/
def place (pubSize : Nat) (gates : List PGate) : List PlacedGate :=
  let rowIdx := pairsByRow (pubSize + gates.length) (permPairs (circuitPositions pubSize gates))
  (List.range pubSize).map
      (fun i => { kind := .generic, wires := placedWiresAt rowIdx i, coeffs := [1, 0, 0, 0, 0] })
    ++ (gates.zip (List.range gates.length)).map
        (fun ggi => { kind := ggi.1.kind
                    , wires := placedWiresAt rowIdx (pubSize + ggi.2)
                    , coeffs := ggi.1.coeffs })

/-- **SPEC** of `place`: the scanning definition, `permLookup` over the whole pair list per cell.
The differential reference §3b pins `place` against. -/
def placeSpec (pubSize : Nat) (gates : List PGate) : List PlacedGate :=
  let pairs := permPairsSpec (circuitPositions pubSize gates)
  (List.range pubSize).map
      (fun i => { kind := .generic, wires := placedWires pairs i, coeffs := [1, 0, 0, 0, 0] })
    ++ (gates.zip (List.range gates.length)).map
        (fun ggi => { kind := ggi.1.kind
                    , wires := placedWires pairs (pubSize + ggi.2)
                    , coeffs := ggi.1.coeffs })

/-- The flat list of every emitted wire cell — the domain of the sigma permutation. -/
def allWires (placed : List PlacedGate) : List Cell := (placed.map (·.wires)).flatten

/-! ### §4a — THE INDEX CHANGES NOTHING (the differential pin, and it can go red).

The optimization above is only legitimate if `place` still emits the SAME object. §6's `by decide`
byte pins cover 1–2 rows; these `#guard`s cover a circuit big enough for the index to matter, with
classes that span rows, both `varIx` parities populated, unwired holes, repeated variables inside a
row — **and a non-zero `public_input_size`**, the path `3c3f61b24` named as never exercised. -/

/-- A synthetic multi-row circuit for the index differential: rotating `external`/`internal`
variables with holes, so classes vary in size, span rows, and both `varIx` parities are used. -/
def idxProbeGates (n : Nat) : List PGate :=
  (List.range n).map (fun r =>
    { kind := .generic
    , permVars := (List.range K_PERMUTS).map (fun c =>
        if (r + c) % 5 == 0 then none
        else if (r + c) % 3 == 0 then some (.internal ((r * 2 + c) % 7))
        else some (.external ((r * 3 + c * 5) % 11)))
    , coeffs := [] })

/-- A ONE-CELL mutation of the probe: row 7's column 1 variable moved to a different id. -/
def idxProbeMisplaced (n : Nat) : List PGate :=
  (idxProbeGates n).zip (List.range n) |>.map (fun gi =>
    if gi.2 == 7 then { gi.1 with permVars := gi.1.permVars.set 1 (some (.external 10)) } else gi.1)

-- The probe is non-degenerate: real classes, both parities, cross-row cycles.
#guard (idxProbeGates 60).length == 60
#guard (distinctVars (circuitPositions 0 (idxProbeGates 60))).length == 18
#guard ((permPairs (circuitPositions 0 (idxProbeGates 60))).filter
          (fun pr => pr.1.row != pr.2.row)).length == 336

-- ⚑ THE INDEX IS FAITHFUL. Every stage — the distinct-variable list, the σ pair list, and the
-- placed gates themselves — is EQUAL to the scanning spec, at `public_input_size` 0 AND 3.
#guard distinctVars (circuitPositions 0 (idxProbeGates 60))
        == distinctVarsSpec (circuitPositions 0 (idxProbeGates 60))
#guard permPairs (circuitPositions 0 (idxProbeGates 60))
        == permPairsSpec (circuitPositions 0 (idxProbeGates 60))
#guard place 0 (idxProbeGates 60) == placeSpec 0 (idxProbeGates 60)
#guard distinctVars (circuitPositions 3 (idxProbeGates 60))
        == distinctVarsSpec (circuitPositions 3 (idxProbeGates 60))
#guard permPairs (circuitPositions 3 (idxProbeGates 60))
        == permPairsSpec (circuitPositions 3 (idxProbeGates 60))
#guard place 3 (idxProbeGates 60) == placeSpec 3 (idxProbeGates 60)

-- ⚑ IT CAN GO RED, twice over.
-- (a) The `==` is DISCRIMINATING: move ONE variable one slot and indexed and scanning placement
--     disagree — so the equalities above are not "any two traversals of anything".
#guard (place 0 (idxProbeGates 60) == placeSpec 0 (idxProbeMisplaced 60)) == false
#guard (place 0 (idxProbeMisplaced 60) == placeSpec 0 (idxProbeGates 60)) == false
-- (b) `varIx` is INJECTIVE — the ONE property the bucket array rests on. A collision would MERGE
--     two variables' equivalence classes and silently wire cells that must not be wired.
#guard (((List.range 24).map (fun n => varIx (.external n))
          ++ (List.range 24).map (fun n => varIx (.internal n))).dedup).length == 48

/-! ## §5 — the internal-variable model (R3's residual, the witness-generation recipe).

`InternalVarDef` is exactly `(Vec<(BigInt,VRaw)>, Option<BigInt>)` per id (`provers.rs:293`): a
linear combination `Σ termsᵢ.scale · termsᵢ.var + const` that `compute_witness` folds
(`transaction.rs:3864-3866`). This is one entry of `*_internal_vars.bin`. -/
structure InternalVarDef where
  id : Nat
  terms : List (Int × PVar)
  const : Option Int
  deriving Repr, DecidableEq, Inhabited

/-- The internal-variable table = the content of `*_internal_vars.bin`
(`InternalVarsRaw = HashMap<u32,…>`). -/
abbrev InternalVarTable := List InternalVarDef

/-! ## §6 — THE o1js BYTE PIN (the gate; it can go red).

Fixed circuits dumped by `bridge/mina-zkapp/scripts/pickles-placement-oracle.mjs` from o1js 2.15.0
`Provable.constraintSystem(f).gates[i].wires`. The Lean `place` of the SAME variable-in-cell grid
must reproduce those `{row,col}` cells byte-for-byte. -/

/-! ### §6a — Case A: `x + y === 8` (o1js example `constraint-system.ts`), ONE generic gate.
o1js `rows=1 pub=0`, gate 0 wires `(0,5)(0,1)(0,2)(0,3)(0,4)(0,0)(0,6)`: cols 0,5 form a 2-cycle (a
reduction internal var); `x`/`y` are singletons (self-wired); the rest unwired (self). -/

/-- Case-A grid. `vA` (internal 0) at cols 0,5 is the reduced-sum var; `x=external 0`, `y=external 1`
at cols 1,2 are singletons (self-wire — exercising the `find?`-to-self path, distinct from the
`None`-default path). -/
def caseA : List PGate :=
  [ { kind := .generic
    , permVars := [some (.internal 0), some (.external 0), some (.external 1),
                   none, none, some (.internal 0), none]
    , coeffs := [] } ]

/-- o1js's emitted wires for case A. -/
def caseA_o1js : List (List Cell) :=
  [[⟨0,5⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,0⟩, ⟨0,6⟩]]

/-- **BYTE PIN A.** `place`'s wires equal o1js's, cell-for-cell. -/
theorem caseA_wires_match_o1js : (place 0 caseA).map (·.wires) = caseA_o1js := by decide

/-! ### §6b — Case B: ONE copied variable across TWO rows — the smallest FALSIFIABLE placement case.
o1js circuit: `x = witness; x.mul(x).assertEquals(49); x.add(1).assertEquals(8)`. `x` lands in three
cells across two rows → a 3-cell class. o1js `rows=2 pub=0`:
  gate 0 wires `(0,5)(0,1)(0,2)(0,4)(1,3)(0,0)(0,6)`
  gate 1 wires `(1,5)(1,1)(1,2)(0,3)(1,4)(1,0)(1,6)`
Classes: `x`={(0,3),(0,4),(1,3)} (3-cycle across rows), `vA`={(0,0),(0,5)}, `vB`={(1,0),(1,5)}. -/

/-- Case-B grid. `x = external 0` at (0,3),(0,4),(1,3); `vA = internal 0` at row-0 cols 0,5;
`vB = internal 1` at row-1 cols 0,5. -/
def caseB : List PGate :=
  [ { kind := .generic
    , permVars := [some (.internal 0), none, none,
                   some (.external 0), some (.external 0), some (.internal 0), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.internal 1), none, none,
                   some (.external 0), none, some (.internal 1), none]
    , coeffs := [] } ]

/-- o1js's emitted wires for case B (the copy). -/
def caseB_o1js : List (List Cell) :=
  [ [⟨0,5⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,4⟩, ⟨1,3⟩, ⟨0,0⟩, ⟨0,6⟩]
  , [⟨1,5⟩, ⟨1,1⟩, ⟨1,2⟩, ⟨0,3⟩, ⟨1,4⟩, ⟨1,0⟩, ⟨1,6⟩] ]

/-- **THE BYTE PIN (R1's gate).** Lean `place`'s `{row,col}` wires equal o1js's, cell-for-cell,
including the cross-row copy `(0,4)↦(1,3)↦(0,3)↦(0,4)`. -/
theorem caseB_wires_match_o1js : (place 0 caseB).map (·.wires) = caseB_o1js := by decide

/-! ### §6c — falsifiability: the pin BITES, and the copy is load-bearing. -/

/-- A grid where `x`'s third cell is mis-placed `(1,3) → (1,4)` (the `x.add` cell in the wrong
column). The placement then DIVERGES from o1js — the gate goes RED on exactly a mis-placement. -/
def caseB_misplaced : List PGate :=
  [ { kind := .generic
    , permVars := [some (.internal 0), none, none,
                   some (.external 0), some (.external 0), some (.internal 0), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.internal 1), none, none,
                   none, some (.external 0), some (.internal 1), none]  -- x now at col 4, not col 3
    , coeffs := [] } ]

/-- **The pin can go RED.** A mis-placed input cell produces wires ≠ o1js's. -/
theorem caseB_misplaced_diverges : (place 0 caseB_misplaced).map (·.wires) ≠ caseB_o1js := by decide

/-- **The copy is load-bearing.** Drop the copy (make `x` appear once per row, no cross-row cell) and
the wires are all-self — ≠ o1js's, whose `(0,4)↦(1,3)` cross-row wire encodes the copy. -/
def caseB_noCopy : List PGate :=
  [ { kind := .generic
    , permVars := [some (.internal 0), none, none, some (.external 0), none, some (.internal 0), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.internal 1), none, none, some (.external 2), none, some (.internal 1), none]
    , coeffs := [] } ]

theorem caseB_noCopy_diverges : (place 0 caseB_noCopy).map (·.wires) ≠ caseB_o1js := by decide

/-! ## §7 — σ is a PERMUTATION (the copy-constraint soundness shape, concretely).

PLONK's copy argument requires the wiring σ to be a BIJECTION on all cells. Here: the multiset of
emitted wire cells equals the multiset of all `(row,col)` cells of the circuit — proved by comparing
the two SORTED flat lists. Not a general theorem (R5), but a real structural check on the emitted
object, red-provable. -/

/-- Every `(row,col)` cell of the placed circuit, `row ∈ 0..P+N-1`, `col ∈ 0..6`. -/
def allCells (nRows : Nat) : List Cell :=
  (List.range nRows).flatMap (fun r => (List.range K_PERMUTS).map (fun c => (⟨r, c⟩ : Cell)))

/-- **σ IS A PERMUTATION (case B).** The sorted emitted wires equal the sorted full cell set: the
wiring neither drops, duplicates, nor invents a cell — it permutes the 14 cells of the 2-row
circuit. -/
theorem caseB_sigma_is_permutation :
    sortCells (allWires (place 0 caseB)) = sortCells (allCells 2) := by decide

/-- Case A likewise: σ permutes the 7 cells of the 1-row circuit. -/
theorem caseA_sigma_is_permutation :
    sortCells (allWires (place 0 caseA)) = sortCells (allCells 1) := by decide

/-! ## §8 — internal_vars, EMITTED (R3's residual model), and its named oracle.

R1 supplies the model R3 lacked. Here is a representative entry: the `x + 1` linear reduction of case
B's second gate becomes an internal variable with recipe `1·(external 0) + 1`
(`completely_reduce`/`create_internal_var`, `plonk_constraint_system.ml:1339-1358`). The exact
recipes are NOT recoverable from o1js's `constraintSystem` JSON (it does not expose internal_vars),
so the BYTE-diff oracle is the circuit-blobs `*_internal_vars.bin` binprot dump (mina-rust
`provers.rs:293`), NOT a zero-build o1js oracle — a NAMED sub-residual. The MODEL half is closed. -/

/-- A representative internal-variable recipe for case B's `x + 1` reduction. -/
def caseB_internalVars : InternalVarTable :=
  [ { id := 0, terms := [(1, .external 0)], const := some 1 } ]

/-- Sanity: the recipe folds to `x + 1` shape — one external term, constant 1. -/
theorem caseB_internalVars_shape :
    caseB_internalVars.head?.map (fun d => (d.terms.length, d.const))
      = some (1, some 1) := by decide

/-! ## §4b — THE TWO PUBLIC-INPUT HAZARDS, made to REFUSE instead of to pass green.

`place`'s two arguments are INDEPENDENT and nothing reconciles them. Two ways that goes wrong, both
found by the public-input lane (`6203df56d`) on a real circuit, both of which produce a **confident
green**:

  **H1 — silent public/aux absorption.** Public word `i` lives at `external i` — faithfully to
  Snarky, whose `finalize_and_get_gates` wires public row `i` col 0 to `External row` (`:1189-1191`),
  so this is the ORACLE's numbering and not a dregg choice. But every existing Lean circuit here
  numbers its OWN variables from `external 0` too. Hand such a circuit a `pubSize > 0` and its first
  `pubSize` aux variables are ABSORBED into the public input: the classes merge, the placement is
  self-consistent, the circuit proves — and it proves something else. The lane had to hand-route its
  gates to `external 3` to escape this.

  **H2 — inert public words.** A declared public word that NO gate reads gets a singleton class,
  self-wires, is pinned by the σ-is-a-permutation check, and is INERT — an unconstrained input
  nothing reports. A `PRIMARY_LEN` mismatch is then N inert words and a green — and the two numbers
  in play are easy to swap: mina-rust `crates/ledger/src/proofs/constants.rs` gives
  `StepTransactionProof { PRIMARY_LEN = 67, ROWS = 17806 }` (the step_main target) against
  `WrapTransactionProof { PRIMARY_LEN = 40, ROWS = 15122 }` — read there, not relayed.

**The missing information is WHERE THE CIRCUIT'S OWN VARIABLES START**, and `place` cannot infer it —
a gate reading `external 0` under `pubSize = 3` is exactly what a *correct* public-input consumer
looks like. So it is DEMANDED: `Contract` carries `auxBase`, and `placeChecked` refuses rather than
reinterprets. `place` itself is UNCHANGED (every emitted byte depends on it), and at `pubSize = 0`
`placeChecked` is `place` with an always-vacuous check — pinned below. -/

/-- The variable-numbering CONTRACT `place`'s two arguments cannot express: `pubSize` public words at
`external 0 .. pubSize-1` (Snarky's own numbering), and `auxBase` = the lowest `external` id the
circuit allocates for its OWN variables. -/
structure Contract where
  pubSize : Nat
  auxBase : Nat
  deriving Repr, DecidableEq, Inhabited

/-- Why a placement was REFUSED. -/
inductive PlaceRefusal where
  /-- **H1.** The circuit's own ids start BELOW the public words, so `auxBase .. pubSize-1` would be
  silently absorbed into the public input. -/
  | auxOverlapsPublic (auxBase pubSize : Nat)
  /-- A gate references `external i` in the DEAD GAP `pubSize ≤ i < auxBase` — an id that is neither
  a public word nor one the circuit declared it allocates. -/
  | referenceInGap (i : Nat)
  /-- **H2.** Public word `i` is read by no gate: a self-wired singleton, unconstrained, inert. -/
  | inertPublicWord (i : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- Every `external` id any gate references (permutation columns only — the ones `place` wires). -/
def externalRefs (gates : List PGate) : List Nat :=
  (gates.flatMap (fun g => (g.permVars.take K_PERMUTS).filterMap id)).filterMap
    (fun v => match v with | .external i => some i | .internal _ => none)

/-- Which public words a circuit's gates actually READ, as a `pubSize`-wide bitmap (one pass). -/
def publicWordsRead (pubSize : Nat) (gates : List PGate) : Array Bool :=
  (externalRefs gates).foldl (fun a i => if i < pubSize then a.set! i true else a)
    (Array.replicate pubSize false)

/-- **H2, REPORTABLE.** The declared public words no gate reads. Empty is the healthy case; a
`PRIMARY_LEN` mismatch shows up here as exactly the surplus words. -/
def inertPublicWords (pubSize : Nat) (gates : List PGate) : List Nat :=
  let read := publicWordsRead pubSize gates
  (List.range pubSize).filter (fun i => !(read.getD i false))

/-- **H2, RELATIVE TO A DECLARED UNREAD SET.** The inert words a caller did NOT declare.

⚑ **WHY THIS EXISTS, and why it is not a hole in H2.** `placeChecked` below is
`placeCheckedWith … []`, so H2 as written is "no public word may be inert" — and that is STRICTER
THAN MINA'S OWN WRAP CIRCUIT. `Impls.Wrap.input ()` builds the 40-word wrap statement through
`Spec.packed_typ`, whose `Constant` case (`composition_types/spec.ml:312-330`) keeps the underlying
`Typ.t` — *"we do use the underlying [Typ.t] to make sure that we allocate public inputs
correctly"* — while replacing `check` with `return ()` AND handing the circuit body a
`Cvar.Constant` instead of the allocated variable. So those slots are ALLOCATED, READ BY NOTHING and
CHECKED BY NOTHING, upstream, by construction. A placement that refuses them refuses `wrap_main`.

⚠ The declared set is an INPUT, never read off the gates: `inertOk` says which slots the caller
CLAIMS to leave unread, and the check is that the gates leave unread NO MORE THAN THAT. A caller
that derived `inertOk` from `inertPublicWords` of the same gates would have written a check that
cannot go red — that is the laundering this signature exists to make visible, and the wrap side's
`wrapInertOk` is a function of Mina's own census and the rung, not of the emitted rows. -/
def inertPublicWordsBeyond (pubSize : Nat) (inertOk : List Nat) (gates : List PGate) : List Nat :=
  (inertPublicWords pubSize gates).filter (fun i => !(inertOk.contains i))

/-- **THE FAIL-CLOSED PLACEMENT ENTRY, WITH THE DECLARED UNREAD SET.** Same placement, or a REFUSAL
naming the incoherence. `placeChecked` is this at `inertOk = []`. -/
def placeCheckedWith (c : Contract) (inertOk : List Nat) (gates : List PGate) :
    Except PlaceRefusal (List PlacedGate) :=
  if c.auxBase < c.pubSize then .error (.auxOverlapsPublic c.auxBase c.pubSize)
  else match (externalRefs gates).find? (fun i => c.pubSize ≤ i && i < c.auxBase) with
    | some i => .error (.referenceInGap i)
    | none =>
      match (inertPublicWordsBeyond c.pubSize inertOk gates).head? with
      | some i => .error (.inertPublicWord i)
      | none => .ok (place c.pubSize gates)

/-- **THE FAIL-CLOSED PLACEMENT ENTRY.** Same placement, or a REFUSAL naming the incoherence. A
circuit that means to have public inputs calls THIS; `place` stays available for the raw pass (and is
what every `pubSize = 0` fixture uses), but a `pubSize > 0` caller that reaches for it is opting out
of both checks in the open. Declares NO slot unread, so H2 bites on every inert word. -/
def placeChecked (c : Contract) (gates : List PGate) :
    Except PlaceRefusal (List PlacedGate) :=
  placeCheckedWith c [] gates

/-- **The strict entry IS the general one at an empty declaration** — so nothing that reads
`placeChecked` is reading a different function than the wrap side's widened caller. -/
theorem placeChecked_is_placeCheckedWith_nil (c : Contract) (gates : List PGate) :
    placeChecked c gates = placeCheckedWith c [] gates := rfl

/-! ### §4b.1 — the refusals BITE, and the `pubSize = 0` path is untouched. -/

/-- A two-row circuit reading public words 0,1,2 and allocating its own vars from `external 10`. -/
def piProbeGates : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.external 10),
                   none, none, some (.external 10), none]
    , coeffs := [] }
  , { kind := .generic
    , permVars := [some (.external 2), some (.external 11), none,
                   some (.external 10), none, none, none]
    , coeffs := [] } ]

-- ⚑ pubSize = 0 IS UNTOUCHED: the checked entry returns exactly `place`'s object for every existing
-- fixture shape, so nothing emitted can move through this door either.
#guard (placeChecked ⟨0, 0⟩ caseA).toOption == some (place 0 caseA)
#guard (placeChecked ⟨0, 0⟩ caseB).toOption == some (place 0 caseB)
#guard (placeChecked ⟨0, 0⟩ (idxProbeGates 60)).toOption == some (place 0 (idxProbeGates 60))

-- The coherent public-input circuit is ACCEPTED, and gives the same placement `place` would.
#guard (placeChecked ⟨3, 10⟩ piProbeGates).toOption == some (place 3 piProbeGates)
#guard inertPublicWords 3 piProbeGates == []

-- ⚑ H1 REFUSES. The same gates declared with aux starting at 0 — the shape every existing circuit
-- has — is the silent-absorption case, and it now cannot pass.
#guard match placeChecked ⟨3, 0⟩ piProbeGates with
       | .error (.auxOverlapsPublic 0 3) => true | _ => false

-- ⚑ H2 REFUSES, and REPORTS which words are inert. `pubSize = 6` over a circuit that reads only
-- 0,1,2 leaves 3,4,5 unconstrained — the `PRIMARY_LEN` 67-vs-40 shape in miniature.
#guard inertPublicWords 6 piProbeGates == [3, 4, 5]
#guard match placeChecked ⟨6, 10⟩ piProbeGates with
       | .error (.inertPublicWord 3) => true | _ => false
-- …and the surplus is exactly the mismatch, counted: declare step_main's `PRIMARY_LEN = 67` over a
-- circuit that reads only 7 of them and 60 words are reported inert, not silently pinned.
#guard (inertPublicWords 67
          [{ kind := .generic
           , permVars := (List.range K_PERMUTS).map (fun c => some (.external c))
           , coeffs := [] }]) == (List.range 67).drop 7

-- A reference in the DEAD GAP (neither public nor declared-aux) refuses too.
#guard match placeChecked ⟨2, 5⟩ piProbeGates with
       | .error (.referenceInGap 2) => true | _ => false

/-! ### §4b.2 — ⚑ **THE DECLARED UNREAD SET IS A DECLARATION, AND IT STILL BITES.**

The three legs that make `placeCheckedWith` a gate rather than a waiver, stated as named theorems
because each is a fact the wrap side's 40-word layout leans on. -/

/-- **A DECLARED slot may be inert; an UNDECLARED one still refuses; and declaring a slot the
circuit DOES read changes nothing.** The middle leg is the whole content: declaring 3 and 4 does not
buy 5, and the refusal names 5 — so a caller whose declaration is short of its emission is refused
at exactly the slot it forgot. -/
theorem declared_inert_is_allowed_and_undeclared_still_refuses :
    placeCheckedWith ⟨6, 10⟩ [3, 4, 5] piProbeGates = .ok (place 6 piProbeGates)
    ∧ (match placeCheckedWith ⟨6, 10⟩ [3, 4] piProbeGates with
       | .error (.inertPublicWord 5) => true | _ => false) = true
    ∧ placeCheckedWith ⟨3, 10⟩ [0, 1, 2] piProbeGates = .ok (place 3 piProbeGates) := by
  refine ⟨rfl, rfl, rfl⟩

/-- **AND THE DECLARATION CANNOT MANUFACTURE A PLACEMENT.** H1 and the dead-gap refusal are
untouched by it — an `inertOk` naming every slot in sight does not buy either. -/
theorem the_declaration_does_not_reach_h1_or_the_gap :
    (match placeCheckedWith ⟨3, 0⟩ (List.range 40) piProbeGates with
     | .error (.auxOverlapsPublic 0 3) => true | _ => false) = true
    ∧ (match placeCheckedWith ⟨2, 5⟩ (List.range 40) piProbeGates with
       | .error (.referenceInGap 2) => true | _ => false) = true := by
  refine ⟨rfl, rfl⟩

/-- **`inertPublicWordsBeyond` REPORTS the shortfall**, so an emission's declaration can be diffed
against its gates rather than only accepted or refused. -/
theorem the_shortfall_is_reportable :
    inertPublicWordsBeyond 6 [3, 4] piProbeGates = [5]
    ∧ inertPublicWordsBeyond 6 [3, 4, 5] piProbeGates = []
    ∧ inertPublicWordsBeyond 6 [] piProbeGates = [3, 4, 5] := by
  refine ⟨rfl, rfl, rfl⟩

#assert_axioms declared_inert_is_allowed_and_undeclared_still_refuses
#assert_axioms the_declaration_does_not_reach_h1_or_the_gap
#assert_axioms the_shortfall_is_reportable

#assert_axioms caseA_wires_match_o1js
#assert_axioms caseB_wires_match_o1js
#assert_axioms caseB_misplaced_diverges
#assert_axioms caseB_noCopy_diverges
#assert_axioms caseB_sigma_is_permutation
#assert_axioms caseB_internalVars_shape

end Dregg2.Circuit.Emit.KimchiPlacement
