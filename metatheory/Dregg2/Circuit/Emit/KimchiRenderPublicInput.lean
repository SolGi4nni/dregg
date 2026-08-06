/-
# Dregg2.Circuit.Emit.KimchiRenderPublicInput — the PUBLIC-INPUT path of `place`, in a PROVED circuit

## ⚑ THE HOLE THIS CLOSES

Measured 2026-08-01 across every committed pickles fixture (`pickles-r4-harness`,
`-poseidon-harness`, `-curvegate-harness`, `-compose-harness`, `-stepfragment-harness`): **all nine
circuit fixtures carry `public_input_size: 0`.** `KimchiPlacement.place` takes `pubSize` as its FIRST
argument and has a whole branch for it — the leading `pubSize` Generic rows, the `External i ↦ {i,0}`
cells prepended to `circuitPositions`, the `pubSize + gateIndex` row offset of every circuit gate —
and **not one line of that branch had ever been inside a circuit a prover accepted.** Every rung from
R4a to the 132-row step_main fragment ran at `pubSize = 0`, where all three collapse to identity.

`step_main` HAS a public input. Measured from mina-rust's own `ProofConstants` table
(`~/dev/mina-rust/crates/ledger/src/proofs/constants.rs`): **Step proofs are `PRIMARY_LEN = 67`**
(`StepTransactionProof`, `StepBlockProof`, `StepMergeProof`, all three `StepZkapp*`), and **Wrap
proofs are `PRIMARY_LEN = 40`**. So the first `pubSize` rows are 67 of the ~17 806 rows of a real
step, and until this file nothing had ever proved one.

This module is the smallest circuit that makes that branch LOAD-BEARING, plus a step-scale instance
at the measured `PRIMARY_LEN = 67`.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gates, their coefficients, the placement (`place`, imported
READ-ONLY from `KimchiPlacement`) and the witness are authored here in Lean. `proof-systems` 0.3.0 is
the Rust PROVER that RUNS the emitted artifact (`pickles-publicinput-harness`); it authors no
constraint. House Law #1.

## The public-input convention, and the TWO independent sources it was read from

kimchi does **not** synthesise public rows — the caller supplies them in the gate vector, and
`.public(n)` only tells the constraint system how many leading rows are public:

  * `kimchi/src/prover.rs:270` — `let public = witness[0][0..index.cs.public].to_vec();`
    The prover's public vector is **witness column 0, rows `0..n`**. Nothing else.
  * `kimchi/src/circuits/constraints.rs:420-423` — `if row < self.cs.public && gate.coeffs.first()
    != Some(&F::one()) { return Err(GateError::IncorrectPublic(row)) }`. A public row's `coeffs[0]`
    **must** be 1.
  * `kimchi/src/circuits/polynomials/generic.rs:297-304` — the generic gate's first half evaluates
    `c₀w₀ + c₁w₁ + c₂w₂ + c₃w₀w₁ + c₄ − pᵣ`, where `pᵣ = public.get(row)` (zero past `n`). With
    `coeffs = [1,0,0,0,0]` that is exactly `w₀[r] = pᵣ` — the public row **pins witness cell `(r,0)`
    to public word `r`**, and constrains nothing else in the row.
  * `generic.rs:379-390` (`GenericGateSpec::Pub`) — kimchi's own public row is `coeffs[0] = 1`, rest
    zero. `place` emits `[1,0,0,0,0]`; kimchi reads absent coefficients as zero
    (`generic.rs:281-286`), so the five-element vector is that gate.

The SECOND source is the deployed Mina prover, not a re-reading of the first — mina-rust
`crates/ledger/src/proofs/transaction.rs:3854-3872` (`compute_witness`):

    for i in 0..public_input_size { res[0][i] = external_values(i); }   // ← External i at (i, 0)
    for (i_after_input, cols) in prover.rows_rev.iter().rev().enumerate() {
        let row_idx = i_after_input + public_input_size;                // ← circuit rows start at P
    }

with `external_values(i) = w.primary[i]` for `i < PRIMARY_LEN`. That is `place`'s model exactly:
`circuitPositions` prepends `(PVar.external i, ⟨i,0⟩)` and places gate `g` at row `pubSize + g`. The
two sources agree, and neither is `place`'s own definition.

## What the harness measures (`metatheory/fixtures/pickles-publicinput-harness`)

  * ACCEPT — `verify() == true` on instance A `(5, 7, 35)` and on instance B `(3, 11, 33)`: the
    circuit is the RELATION `p₀·p₁ = p₂`, and the public input selects the instance.
  * **PI COMMITMENT** — the honest proof of instance A verified against instance B's public input is
    REJECTED, and each single-word flip of A's public input is REJECTED. The proof binds the claim.
  * **PI WIRE (σ)** — flip the public cell `(0,0)` AND tell the verifier the new value, so the public
    row's own constraint `w₀[0] = p₀` still holds: REJECTED, by the copy-permutation `(0,0)↦(3,0)`
    alone. This is the leg that shows a public word is WIRED INTO the circuit rather than merely
    declared.
  * **CONTROL** — the same flip on `piNoWire`, whose only difference is that gate 0 reads a fresh
    `external 3` instead of `external 0`, is ACCEPTED. So the rejection above is the placement wire.
  * **NON-VACUITY** — flipping `(0,3)`, a cell IN a public row that the public gate does not read and
    σ does not wire, is ACCEPTED. A public row constrains column 0 and nothing else.
  * **SCALE** — `piWide`, `public_input_size = 67` (step_main's measured `PRIMARY_LEN`), 134 rows,
    every public word consumed by the circuit; accept + a public-word tamper + the same non-vacuity
    control.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`/`native_decide`. Imports
`KimchiPlacement` only. Carries NO `main` — the emit driver is `EmitPublicInputJson.lean`, so this
module roots cleanly into `PicklesSynthesis` (same split as `KimchiRenderPoseidon`).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson

namespace Dregg2.Circuit.Emit.KimchiRenderPublicInput

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson

set_option autoImplicit false

/-! ## §1 — `piMul`: the smallest circuit whose public-input path is load-bearing.

Three public words `p₀ p₁ p₂` and the relation `p₀ · p₁ = p₂`. Public word `i` is `external i` and
lives at cell `⟨i,0⟩` (`compute_witness`'s `res[0][i]`); the two circuit gates sit at absolute rows
`3` and `4` (`pubSize + gateIndex`).

    row 0..2  public   Generic  coeffs [1,0,0,0,0]     w₀ = pᵢ            (emitted by `place`)
    row 3     Mul      Generic  coeffs [0,0,-1,1,0,…]  t = w₀·w₁          w₀=p₀ w₁=p₁ w₂=t
    row 4     Eq       Generic  coeffs [1,-1,0,0,0,…]  w₀ − w₁ = 0        w₀=t  w₁=p₂

Every public word reaches the circuit ONLY through σ:
`p₀: (0,0)↔(3,0)`, `p₁: (1,0)↔(3,1)`, `p₂: (2,0)↔(4,1)`, and `t: (3,2)↔(4,0)`. -/

/-- The Lean-authored public-input circuit. `external 0/1/2` ARE the three public words. -/
def piMulGates : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 0), some (.external 1), some (.internal 0), none, none, none, none]
    , coeffs := [0, 0, -1, 1, 0,  0, 0, 0, 0, 0] }
  , { kind := .generic
    , permVars := [some (.internal 0), some (.external 2), none, none, none, none, none]
    , coeffs := [1, -1, 0, 0, 0,  0, 0, 0, 0, 0] } ]

/-- **CONTROL for the PI-WIRE claim.** Identical to `piMulGates` except gate 0's left input is a
FRESH variable (`external 3`, an auxiliary — mina-rust's `external_values` routes `i ≥ PRIMARY_LEN`
to `w.aux()`), so public word 0 is declared and pinned by its own row but reaches NO circuit cell:
its class is the singleton `{(0,0)}` and it self-wires. The same `(0,0)` flip the wired circuit
REJECTS must be ACCEPTED here. -/
def piNoWireGates : List PGate :=
  [ { kind := .generic
    , permVars := [some (.external 3), some (.external 1), some (.internal 0), none, none, none, none]
    , coeffs := [0, 0, -1, 1, 0,  0, 0, 0, 0, 0] }
  , { kind := .generic
    , permVars := [some (.internal 0), some (.external 2), none, none, none, none, none]
    , coeffs := [1, -1, 0, 0, 0,  0, 0, 0, 0, 0] } ]

/-- Public-input size of `piMul`/`piNoWire`. -/
def piPub : Nat := 3

/-- Rows of `piMul`/`piNoWire` = `piPub` public rows + 2 circuit gates. -/
def piRows : Nat := 5

def piMulPlaced : List PlacedGate := place piPub piMulGates
def piNoWirePlaced : List PlacedGate := place piPub piNoWireGates

/-! ### The witness grid, 15 columns × 5 rows, for an instance `(a, b, c)` with `a·b = c`.

`col0 = [a, b, c, a, c]`, `col1 = [0,0,0, b, c]`, `col2 = [0,0,0, c, 0]`, cols 3..14 zero. Rows 0..2
are the public cells the prover reads as its public vector (`prover.rs:270`); rows 3..4 are the
circuit. `piNoWire` uses the SAME grid — its only change is which variable owns `(3,0)`. -/
def piWitnessOf (a b c : Int) : List (List Int) :=
  [ [a, b, c, a, c]        -- col 0
  , [0, 0, 0, b, c]        -- col 1
  , [0, 0, 0, c, 0] ]      -- col 2
  ++ (List.replicate 12 [0, 0, 0, 0, 0])   -- cols 3..14

/-- The public vector of an instance, in the order the verifier is handed it. -/
def piPublicOf (a b c : Int) : List Int := [a, b, c]

/-- Instance A: `5 · 7 = 35`. -/
def piWitnessA : List (List Int) := piWitnessOf 5 7 35
def piPublicA : List Int := piPublicOf 5 7 35

/-- Instance B: `3 · 11 = 33`. A SECOND instance of the SAME circuit — the accept-on-B leg is what
makes "the public input selects the instance" a measurement rather than a hardcoded fixture. -/
def piWitnessB : List (List Int) := piWitnessOf 3 11 33
def piPublicB : List Int := piPublicOf 3 11 33

/-! ## §2 — `piWide`: the same path at step_main's MEASURED public-input size.

`PRIMARY_LEN = 67` for every Step proof in mina-rust's `ProofConstants` table (Wrap is 40). The
circuit folds all 67 public words into one accumulator and pins the total, so EVERY public word is
consumed by σ — a public row that placed wrong would break the fold rather than sit inert.

    row 0..66    public   w₀ = pᵢ                                   (67 rows)
    row 67       Add      acc₀ = p₀ + p₁                            w₀=p₀ w₁=p₁ w₂=acc₀
    row 67+j     Add      accⱼ = accⱼ₋₁ + pⱼ₊₁     (1 ≤ j ≤ 65)     w₀=accⱼ₋₁ w₁=pⱼ₊₁ w₂=accⱼ
    row 133      Const    acc₆₅ = 2278                              w₀=acc₆₅

134 rows total. `pᵢ = i+1`, so `acc₆₅ = Σ_{k=1}^{67} k = 2278`. -/

/-- Step's measured `PRIMARY_LEN` (mina-rust `constants.rs:39,46,53,84,113,120`). -/
def wideN : Nat := 67

/-- Public word `i` of `piWide`. -/
def widePub (i : Nat) : Int := (i : Int) + 1

/-- Accumulator after gate `j`: `Σ_{k=1}^{j+2} k`. -/
def wideAcc (j : Nat) : Int := (((j + 2) * (j + 3)) / 2 : Nat)

/-- The pinned total, `Σ_{k=1}^{67} k`. -/
def wideTotal : Int := wideAcc (wideN - 2)

/-- The `wideN - 1 = 66` accumulation gates plus one pinning `Const` gate. -/
def piWideGates : List PGate :=
  (List.range (wideN - 1)).map (fun j =>
    if j = 0 then
      { kind := .generic
      , permVars := [some (.external 0), some (.external 1), some (.internal 0),
                     none, none, none, none]
      , coeffs := [1, 1, -1, 0, 0,  0, 0, 0, 0, 0] }
    else
      { kind := .generic
      , permVars := [some (.internal (j - 1)), some (.external (j + 1)), some (.internal j),
                     none, none, none, none]
      , coeffs := [1, 1, -1, 0, 0,  0, 0, 0, 0, 0] })
  ++ [ { kind := .generic
       , permVars := [some (.internal (wideN - 2)), none, none, none, none, none, none]
       , coeffs := [1, 0, 0, 0, -wideTotal,  0, 0, 0, 0, 0] } ]

def piWideRows : Nat := wideN + wideN

def piWidePlaced : List PlacedGate := place wideN piWideGates

/-- `piWide`'s witness cell at `(col, row)`. Column 0 carries the public words on rows `0..66` and
the accumulator inputs on the circuit rows; columns 1/2 carry the addend and the running sum. -/
def wideWitAt (col row : Nat) : Int :=
  if row < wideN then
    (if col = 0 then widePub row else 0)
  else
    let j := row - wideN
    if j = 0 then
      (if col = 0 then widePub 0 else if col = 1 then widePub 1
       else if col = 2 then wideAcc 0 else 0)
    else if j < wideN - 1 then
      (if col = 0 then wideAcc (j - 1) else if col = 1 then widePub (j + 1)
       else if col = 2 then wideAcc j else 0)
    else
      (if col = 0 then wideTotal else 0)

def piWideWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range piWideRows).map (fun row => wideWitAt col row))

def piWidePublic : List Int := (List.range wideN).map widePub

/-! ## §3 — the JSON renderer (same shape every pickles harness parses). -/

/-! ⚑ `public_input` is emitted beside `public_input_size` because a `pubSize > 0` circuit is not
runnable without it: the verifier is handed the vector separately (`kimchi/src/verifier.rs:816`
rejects a length mismatch outright), so a fixture that omits it would force the harness to re-derive
the public input in Rust — which is witness authoring, and would put the thing under test on both
sides of the test. -/
/-! ⚑ **ONE RENDERER, AND IT TAKES THE PUBLIC VECTOR.** The copy this module carried was written
because none of the seven `pubSize = 0` copies took a `public_input`. Presence is now a field of the
`KimchiCircuit` VALUE (`publicInput := some pub`), not a choice of which copy to call, and
`renderCircuit_public_is_the_open_coded_shape` pins over EVERY argument that
`KimchiCircuitJson.renderCircuit` emits the chain this module's copy emitted.

⚠ `some []` is NOT `none`: the empty vector still emits `"public_input":[],`. That is what the wrap
and step rungs below their closing rung emit, and it is why presence is carried rather than inferred
from emptiness (`optField_some_nil_still_emits_the_key`). -/

def piMulJsonA : String :=
  renderCircuit { name := "piMulInstanceA", pubSize := piPub, numRows := piRows
                , gates := piMulPlaced, witness := piWitnessA, publicInput := some piPublicA }
def piMulJsonB : String :=
  renderCircuit { name := "piMulInstanceB", pubSize := piPub, numRows := piRows
                , gates := piMulPlaced, witness := piWitnessB, publicInput := some piPublicB }
def piNoWireJson : String :=
  renderCircuit { name := "piNoWireControl", pubSize := piPub, numRows := piRows
                , gates := piNoWirePlaced, witness := piWitnessA, publicInput := some piPublicA }
def piWideJson : String :=
  renderCircuit { name := "piWideStepPrimaryLen", pubSize := wideN, numRows := piWideRows
                , gates := piWidePlaced, witness := piWideWitness
                , publicInput := some piWidePublic }

/-! ## §4 — the in-CI pins over the EMITTED object (`#guard` / `decide`; they can go red).

These pin the three things the `pubSize = 0` rungs could not see: the shape of a public row, the σ
class that carries a public word into the circuit, and the row offset of the circuit gates. -/

-- Shape: 3 public rows + 2 circuit gates, 7 wires each.
#guard piMulPlaced.length == piRows
#guard (piMulPlaced.map (fun g => g.wires.length)).all (· == 7)
#guard piWitnessA.length == 15
#guard (piWitnessA.map (·.length)).all (· == piRows)

/-- **THE PUBLIC ROW IS THE ROW kimchi DEMANDS.** Each of the first `piPub` placed gates is
`Generic` with `coeffs[0] = 1` — `constraints.rs:420-423` errors `IncorrectPublic(row)` on anything
else, and `generic.rs:297-304` then reads the row as `w₀[r] − pᵣ = 0`. -/
theorem piMul_public_rows_are_pub_gates :
    ((piMulPlaced.take piPub).map (fun g => (g.kind.ordinal, g.coeffs)))
      = List.replicate piPub (1, ([1, 0, 0, 0, 0] : List Int)) := by decide

/-- **THE PUBLIC WORDS ARE WIRED INTO THE CIRCUIT.** `place`'s σ carries `⟨0,0⟩ ↦ ⟨3,0⟩`,
`⟨1,0⟩ ↦ ⟨3,1⟩` and `⟨2,0⟩ ↦ ⟨4,1⟩` — public word `i` at cell `⟨i,0⟩` is in one equivalence class
with the circuit cell that consumes it, at circuit rows offset by `piPub`. This is the whole
public-input branch of `place`, as an equality on the emitted object. -/
theorem piMul_public_cells_wire_into_circuit :
    ((piMulPlaced.take piPub).map (fun g => g.wires.headD ⟨0,0⟩))
      = [⟨3,0⟩, ⟨3,1⟩, ⟨4,1⟩] := by decide

/-- The circuit gates sit at rows `piPub + gateIndex`, and their col-0 wires point BACK at the
public cells — the return leg of the same cycles. -/
theorem piMul_circuit_rows_point_back :
    ((piMulPlaced.drop piPub).map (fun g => g.wires.headD ⟨0,0⟩)) = [⟨0,0⟩, ⟨3,2⟩] := by decide

/-- **σ IS A PERMUTATION with `pubSize > 0`.** The sorted emitted wires equal the sorted full cell
set of all 5 rows — the public rows are inside the permutation, not bolted on beside it. Every
earlier rung proved this only at `pubSize = 0`. -/
theorem piMul_sigma_is_permutation :
    sortCells (allWires piMulPlaced) = sortCells (allCells piRows) := by decide

/-- **THE CONTROL IS A CONTROL.** In `piNoWire`, public cell `⟨0,0⟩` self-wires: word 0 is pinned by
its own public row and reaches no circuit cell, so the σ rejection the wired circuit produces cannot
be attributed to anything else. Words 1 and 2 stay wired, so the control differs in exactly one
class. -/
theorem piNoWire_public_cell_0_is_singleton :
    ((piNoWirePlaced.take piPub).map (fun g => g.wires.headD ⟨0,0⟩))
      = [⟨0,0⟩, ⟨3,1⟩, ⟨4,1⟩] := by decide

/-- **FALSIFIABILITY.** The wired and unwired placements differ — if they did not, the control would
be the same circuit and every rejection/acceptance pair below would be vacuous. -/
theorem piMul_and_piNoWire_placements_differ :
    (piMulPlaced.map (·.wires)) ≠ (piNoWirePlaced.map (·.wires)) := by decide

/-- The instances are distinct and both satisfy the relation the circuit encodes. -/
theorem piInstances_distinct : piPublicA ≠ piPublicB := by decide

-- Witness/public agreement: the prover reads its public vector out of witness column 0
-- (`prover.rs:270`), so the emitted `public_input` must BE that prefix or the fixture is incoherent.
#guard (piWitnessA.headD []).take piPub == piPublicA
#guard (piWitnessB.headD []).take piPub == piPublicB

-- `piWide` at step_main's measured PRIMARY_LEN.
#guard wideN == 67
#guard piWideGates.length == wideN
#guard piWideRows == 134
#guard wideTotal == 2278
#guard piWidePublic.length == wideN
#guard (piWideWitness.headD []).take wideN == piWidePublic
#guard piWideWitness.length == 15
#guard (piWideWitness.map (·.length)).all (· == piWideRows)

-- The wide circuit's public rows carry kimchi's public shape too, and the LAST public row (index 66,
-- word 66) is wired into the LAST accumulation gate — placed row `wideN + 65 = 132`, column 1. That
-- is the far end of the indexing, and exactly where an off-by-one in `pubSize + gateIndex` lands.
#guard ((piWidePlaced.take wideN).map (fun g => (g.kind.ordinal, g.coeffs))).all
        (· == (1, ([1, 0, 0, 0, 0] : List Int)))
#guard (piWidePlaced.getD 66 default).wires.headD ⟨0,0⟩ == (⟨132, 1⟩ : Cell)
#guard (piWidePlaced.getD 0 default).wires.headD ⟨0,0⟩ == (⟨67, 0⟩ : Cell)
#guard sortCells (allWires piWidePlaced) == sortCells (allCells piWideRows)

#assert_axioms piMul_public_rows_are_pub_gates
#assert_axioms piMul_public_cells_wire_into_circuit
#assert_axioms piMul_circuit_rows_point_back
#assert_axioms piMul_sigma_is_permutation
#assert_axioms piNoWire_public_cell_0_is_singleton
#assert_axioms piMul_and_piNoWire_placements_differ
#assert_axioms piInstances_distinct

end Dregg2.Circuit.Emit.KimchiRenderPublicInput
