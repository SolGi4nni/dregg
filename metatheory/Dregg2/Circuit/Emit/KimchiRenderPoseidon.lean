/-
# Dregg2.Circuit.Emit.KimchiRenderPoseidon — assemble + render a REAL Poseidon circuit (R4a, scaled)

## ⚑ THE RUNG THIS IS, AND WHAT IT IS NOT

R4a (`KimchiRender`) proved a LEAN-SYNTHESIZED circuit is a real, provable, binding kimchi circuit —
but on a TOY circuit (`p = a·b ∧ p = 35`, two generic gates). This file scales that to the SMALLEST
MEANINGFUL circuit: a **single Poseidon permutation** (the 11 custom `Poseidon` gate rows + a closing
`Zero` gate), assembled from the byte-exact custom-gate rows (`KimchiCustomGates.poseidonRowCoeffs` —
the 165 round constants that byte-match o1js) and placed by the byte-verified copy-permutation pass
(`KimchiPlacement.place`). The witness — the 55 intermediate Poseidon round states — is COMPUTED IN
LEAN by dregg's own Poseidon-over-Fp evaluator (`PastaPoseidon.Ref.permFrom`), the same reference
that reproduces the o1js `Poseidon.hash` gold KATs. The companion Rust harness
(`pickles-poseidon-harness`) reads the emitted JSON, builds the pure-Rust kimchi objects, and
PROVES + VERIFIES it, and checks BOTH tamper polarities (a round-state witness flip and a round-
constant coeff flip) are REJECTED.

This closes the gap named in the R4a work: the R4a wire-fidelity check used EMPTY-coeff circuits, so
the real Poseidon coeffs had never been in an actual PROOF. Here they are — the 165 byte-exact round
constants now CONSTRAIN a real kimchi proof, and the permutation's output equals dregg's own
`Ref.hash [1]` (= the o1js `Poseidon.hash([1])` gold), so the coeffs are shown to compute the RIGHT
thing in a proof, not merely to match a diff.

It is **NOT** a soundness proof, **NOT** "machine-checked Pickles", and **NOT** a Mina-valid Pickles
proof. The kimchi proof is an INNER proof; the reportable increment is that the o1js-free
Lean-render → pure-Rust-prove pipeline works for a REAL circuit (Poseidon), not just a toy.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored synthesis.** The gate list (`poseidonGates`), the per-row coefficients
(`poseidonRowCoeffs`, imported read-only from `KimchiCustomGates`), the placement (`place`, imported
read-only from `KimchiPlacement`), and the witness (`poseidonWitness`, computed from
`PastaPoseidon.Ref.permFrom`) are all authored/derived in Lean. `proof-systems` is the Rust PROVER
that RUNS the Lean-emitted artifact — it authors no constraint. The `Poseidon` gate's constraint
polynomial (`f^7 + c(x) − f(wx)`, the sbox/MDS/round-constant identity across the 5 rounds of a row)
is `proof-systems`' fixed gate semantics (`poseidon.rs`); assembling the 11 rows + their coefficients
+ their identity self-wires IS the synthesis.

## The witness layout (transcribed from `poseidon.rs::generate_witness`, read-only)

`SPONGE_WIDTH = 3`, `ROUNDS_PER_ROW = 5`, `POS_ROWS_PER_HASH = 11`, `STATE_ORDER = [0,2,3,4,1]` ⇒
`round_to_cols i = (STATE_ORDER[i])·3 .. +3`. Poseidon row `r` (absolute row `r`, `r = 0..10`) holds:
  * state `s(5r)`   at cols 0,1,2   (`round_to_cols 0`, the row input — for `r>0` it is the previous
    row's round-4 output, chained by the gate's Curr/Next reference, not by a copy wire),
  * state `s(5r+1)` at cols 6,7,8   (`round_to_cols 1`),
  * state `s(5r+2)` at cols 9,10,11 (`round_to_cols 2`),
  * state `s(5r+3)` at cols 12,13,14(`round_to_cols 3`),
  * state `s(5r+4)` at cols 3,4,5   (`round_to_cols 4`).
The final permutation output `s(55)` lands at row 11 cols 0,1,2 (the `Zero` gate row); cols 3..14 of
row 11 are 0. Here `s(k) = Ref.permFrom 0 k [1,0,0]`, so `s(55)[0] = Ref.hash [1]` (o1js
`Poseidon.hash([1])`). The rows are self-wired (identity σ) — exactly `Wire::for_row` /
`create_poseidon_gadget` for a standalone hash — because the state chains across rows through the
gate's `Next`-row reference, needing no copy constraint.

## Axiom hygiene / build

NO `main` (so it roots cleanly into the `PicklesSynthesis` aggregate alongside `KimchiRender`, which
carries the only `main` in that cone). The emit driver is the sibling `EmitPoseidonJson.lean`
(`lake env lean --run`). `#guard`s reduce in the interpreter; no `sorry`/`native_decide`.
Imports `KimchiPlacement` (place/PGate/PlacedGate/Cell/PVar), `KimchiCustomGates` (poseidonRowCoeffs),
`PastaPoseidon` (Ref.permFrom / Ref.hash).
-/
import Dregg2.Circuit.Emit.KimchiPlacement
import Dregg2.Circuit.Emit.KimchiCircuitJson
import Dregg2.Circuit.Emit.KimchiCustomGates
import Dregg2.Circuit.Emit.PastaPoseidon

namespace Dregg2.Circuit.Emit.KimchiRenderPoseidon

open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.KimchiCircuitJson
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.PastaPoseidon

set_option autoImplicit false

/-! ## §1 — the circuit, authored in Lean and placed by `place`. -/

/-- The permutation input state: absorbing `[1]` into a zero sponge state gives `[1,0,0]`, so the
permutation output lane 0 is `Poseidon.hash([1])` — a value with a published o1js gold. -/
def poseidonInput : List Nat := [1, 0, 0]

/-- The Poseidon state after `k` rounds, over Pasta Fp, via dregg's own reference permutation
(`PastaPoseidon.Ref.permFrom` — sbox `x⁷`, the `fp_kimchi` MDS, round constants `rcsN[r]`). -/
def stateAt (k : Nat) : List Nat := Ref.permFrom 0 k poseidonInput

/-- Lane `j` of state `s(k)`, as an `Int` (all states are `Nat` in `[0, p)`). -/
def laneI (k j : Nat) : Int := ((stateAt k).getD j 0 : Int)

/-- Seven unwired permutation columns ⇒ `place` emits identity self-wires for the row (the state
chains across rows through the gate's Curr/Next reference, so no copy constraint is needed). -/
def sevenNones : List (Option PVar) := List.replicate 7 none

/-- The Lean-authored Poseidon circuit: 11 `Poseidon` gate rows (row `j` carries the 15 byte-exact
round constants `poseidonRowCoeffs j`) + one closing `Zero` gate (holds the output state). -/
def poseidonGates : List PGate :=
  (List.range 11).map (fun j =>
      { kind := .poseidon, permVars := sevenNones, coeffs := poseidonRowCoeffs j })
    ++ [ { kind := .zero, permVars := sevenNones, coeffs := [] } ]

/-- The placed circuit — `place`'s byte-verified pass applied to `poseidonGates` (identity σ). -/
def poseidonPlaced : List PlacedGate := place 0 poseidonGates

/-- Column `col`, row `row` of the witness grid (see the header for the `round_to_cols` map). -/
def witAt (col row : Nat) : Int :=
  if col < 3 then laneI (5 * row) col                                        -- s(5r)   @ cols 0,1,2
  else if col < 6 then (if row < 11 then laneI (5 * row + 4) (col - 3) else 0)  -- s(5r+4) @ cols 3,4,5
  else if col < 9 then (if row < 11 then laneI (5 * row + 1) (col - 6) else 0)  -- s(5r+1) @ cols 6,7,8
  else if col < 12 then (if row < 11 then laneI (5 * row + 2) (col - 9) else 0) -- s(5r+2) @ cols 9,10,11
  else (if row < 11 then laneI (5 * row + 3) (col - 12) else 0)               -- s(5r+3) @ cols 12,13,14

/-- The Lean-computed witness: 15 columns × 12 rows. Row 11 (the `Zero` gate) holds the output state
`s(55)` in cols 0,1,2 and 0 elsewhere. -/
def poseidonWitness : List (List Int) :=
  (List.range 15).map (fun col => (List.range 12).map (fun row => witAt col row))

/-! ## §2 — the JSON renderer (same shape `KimchiRender` emits; the harness parses it). -/


/-! ⚑ **ONE RENDERER.** The copy of `renderCircuit` this module carried — one of eleven, each with
its own private `q`/`qt`/`qs`, `renderCell`, `renderWires`, `renderIntList`, `renderGate`,
`renderGates`, `renderWitness` — is DELETED. `KimchiCircuitJson.renderCircuit` is a pure function of
a `KimchiCircuit` VALUE, and `renderCircuit_base_is_the_open_coded_shape` pins over EVERY argument
that it emits the chain the deleted copy emitted. -/

/-- The rendered Poseidon circuit JSON (0 public inputs, 12 rows). -/
def poseidonJson : String :=
  renderCircuit { name := "poseidonPermHash1", pubSize := 0, numRows := 12
                , gates := poseidonPlaced, witness := poseidonWitness }

/-! ## §3 — the in-CI pins (`#guard`; interpreter-reduced). -/

-- Structural: 12 gates (11 Poseidon + 1 Zero), 7 wires each, 15 columns × 12 rows.
#guard poseidonGates.length == 12
#guard poseidonPlaced.length == 12
#guard (poseidonPlaced.map (fun g => g.wires.length)).all (· == 7)
#guard poseidonWitness.length == 15
#guard (poseidonWitness.map (·.length)).all (· == 12)

-- Coeffs: each Poseidon row carries 15 round constants; the closing Zero gate carries none.
#guard ((poseidonPlaced.headD default).coeffs).length == 15
#guard ((poseidonPlaced.getD 11 default).coeffs).length == 0
#guard (poseidonPlaced.headD default).kind.ordinal == 2   -- Poseidon
#guard (poseidonPlaced.getD 11 default).kind.ordinal == 0 -- Zero

-- Placement fidelity: row 0 is identity self-wired, exactly `Wire::for_row(0)` /
-- `create_poseidon_gadget`'s standalone-hash wiring.
#guard (poseidonPlaced.headD default).wires ==
  ([⟨0,0⟩, ⟨0,1⟩, ⟨0,2⟩, ⟨0,3⟩, ⟨0,4⟩, ⟨0,5⟩, ⟨0,6⟩] : List Cell)

-- ⚑ The OUTPUT is the o1js `Poseidon.hash([1])` gold value (and dregg's own `Ref.hash [1]`): the
-- permutation output lane 0 (row 11, col 0 of the witness) equals both. This is the "checker as
-- oracle" pin — the coeffs, in the assembled circuit, compute the RIGHT hash.
#guard (stateAt 55).getD 0 0 ==
  7555220006856562833147743033256142154591945963958408607501861037584894828141
#guard (stateAt 55).getD 0 0 == Ref.hash [1]
#guard (poseidonWitness.getD 0 []).getD 11 0 ==
  (7555220006856562833147743033256142154591945963958408607501861037584894828141 : Int)

end Dregg2.Circuit.Emit.KimchiRenderPoseidon
