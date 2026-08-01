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
cells, so class = "cells of one variable" with no merge. `mergeRoots` is the seam where an
`assert_equal` remap would compose; identity for R1. -/

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

/-- The distinct variables, in first-appearance order. -/
def distinctVars (poss : List (PVar × Cell)) : List PVar :=
  (poss.map (·.1)).dedup

/-- The (deduplicated) cells of variable `v` — its equivalence class (`Hash_set.of_list data`). -/
def classCells (poss : List (PVar × Cell)) (v : PVar) : List Cell :=
  ((poss.filter (fun p => p.1 == v)).map (·.2)).dedup

/-- **The whole permutation**, as a `Cell → Cell` association list: every class's cycle pairs. -/
def permPairs (poss : List (PVar × Cell)) : List (Cell × Cell) :=
  (distinctVars poss).flatMap (fun v => cyclePairs (classCells poss v))

/-- `permutation pos` (`:1202-1203`): the next cell in `pos`'s cycle, or `pos` itself if `pos` is
in no class (an unwired column / advice cell). -/
def permLookup (pairs : List (Cell × Cell)) (c : Cell) : Cell :=
  match pairs.find? (fun p => p.1 == c) with
  | some p => p.2
  | none => c

/-! ## §4 — the placement pass. -/

/-- A row's 7 wired cells: `Array.init K_PERMUTS (fun col => permutation {row; col})` (`:1210-1211`). -/
def placedWires (pairs : List (Cell × Cell)) (absRow : Nat) : List Cell :=
  (List.range K_PERMUTS).map (fun col => permLookup pairs ⟨absRow, col⟩)

/-- **THE PLACEMENT PASS.** `finalize_and_get_gates` (`:1156-1253`): public-input Generic rows first
(`coeffs=[1,0,0,0,0]`), then the circuit gates, each carrying its 7 placed `{row,col}` wires. This
is the object whose `wires` field is byte-diffed against o1js. -/
def place (pubSize : Nat) (gates : List PGate) : List PlacedGate :=
  let pairs := permPairs (circuitPositions pubSize gates)
  (List.range pubSize).map
      (fun i => { kind := .generic, wires := placedWires pairs i, coeffs := [1, 0, 0, 0, 0] })
    ++ (gates.zip (List.range gates.length)).map
        (fun ggi => { kind := ggi.1.kind
                    , wires := placedWires pairs (pubSize + ggi.2)
                    , coeffs := ggi.1.coeffs })

/-- The flat list of every emitted wire cell — the domain of the sigma permutation. -/
def allWires (placed : List PlacedGate) : List Cell := (placed.map (·.wires)).flatten

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

#assert_axioms caseA_wires_match_o1js
#assert_axioms caseB_wires_match_o1js
#assert_axioms caseB_misplaced_diverges
#assert_axioms caseB_noCopy_diverges
#assert_axioms caseB_sigma_is_permutation
#assert_axioms caseB_internalVars_shape

end Dregg2.Circuit.Emit.KimchiPlacement
