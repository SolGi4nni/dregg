/-
# Dregg2.Circuit.Emit.KimchiCircuitJson — THE renderer. One, for every Lean-placed kimchi circuit.

## ⚑ WHAT THIS REPLACES

Eleven copies. `renderCircuit` was open-coded, character for character, in `KimchiRender`,
`KimchiRenderPoseidon`, `KimchiRenderCompleteAdd`, `KimchiRenderVarBaseMul`, `KimchiRenderEndoMul`,
`KimchiRenderEndoMulScalar`, `KimchiComposeMSM`, `KimchiRenderPublicInput` and
`KimchiPreimageCircuit`, and again — under two other names, with two more field groups — as
`KimchiStepMainCore.renderStepCircuit` and `KimchiWrapMainCore.renderWrapCircuit`. Each carried its
own private `q`/`qt`/`qs`, its own `renderCell`, `renderWires`, `renderIntList`, `renderGate`,
`renderGates`, `renderWitness`. `KimchiComposeStepFragment` avoided a twelfth by importing
`KimchiRenderVarBaseMul` purely for its renderer, which is what a missing shared module looks like
from the inside.

**What the copies disagreed about was one thing: WHICH FIELDS THEY CARRY.** Four field-sets, and a
lane that needed a public-input vector had to write a new copy because the seven it could see did
not take one. That is the two-line generalization nobody did, and it is this file.

## ⚑ THE FIELD SET IS DATA, NOT A MODE

`KimchiCircuit` is a **value**. `renderCircuit` is a pure function of it. There is no monad, no
runtime config, no emitter state: a circuit's JSON is a function of the circuit, and a control
circuit is another value, so "these two emissions are byte-identical" stays a statement relating
two objects (`KimchiPreimageCircuit.the_reauthored_json_is_byte_identical` is exactly that, and it
still is).

⚠ **The optional groups are `Option`, NOT "omit when empty".** The wrap and step rungs emit
`"public_input":[]` at `pubSize = 0` — the KEY IS PRESENT and the array is empty — while the seven
`pubSize = 0` gate-fixture circuits omit the key entirely. Inferring presence from emptiness would
have collapsed those two into one and moved bytes on nine committed artifacts. Presence is carried,
not guessed.

## ⚑ THE PINS: general theorems, not a diff

§3 states, **for every name, every pubSize, every row count, every gate list, every witness, every
public vector, every probe list and every slot census**, that `renderCircuit` at that field-set is
character-for-character the chain the deleted copy contained. Four theorems, one per inherited
shape, each universally quantified — not a case test on the committed fixtures.

⚠ They are proved by `simp only [… String.append_assoc, String.append_empty]`, not by `rfl`. That
is not a weaker STATEMENT — it is the same equation over the same variables — it is a weaker
*witness*: the general renderer parenthesises its concatenation differently from the inherited
chain, and `String.append` on a chain containing variables is stuck at the first non-literal, so
the two terms are equal but not definitionally equal. `rfl` was measured: **7 min of `whnf` and a
timeout at 4,000,000 heartbeats.** The associativity rewrite closes all four in under four seconds
and rests on two core theorems, so the pins are kernel-clean (`#assert_axioms` below).
-/
import Dregg2.Circuit.Emit.KimchiPlacement

namespace Dregg2.Circuit.Emit.KimchiCircuitJson

open Dregg2.Circuit.Emit.KimchiPlacement

set_option autoImplicit false

/-! ## §1 — the JSON vocabulary. Every emitted artifact in this cone is built from exactly these. -/

/-- A quoted string. Brace and quote literals are kept out of `s!` interpolation throughout. -/
def q (s : String) : String := "\"" ++ s ++ "\""

/-- A cell, as the `[row, col]` pair the harnesses parse into `Wire { row, col }`. -/
def renderCell (c : Cell) : String := "[" ++ toString c.row ++ "," ++ toString c.col ++ "]"

def renderWires (ws : List Cell) : String :=
  "[" ++ String.intercalate "," (ws.map renderCell) ++ "]"

def renderWireList (wss : List (List Cell)) : String :=
  "[" ++ String.intercalate "," (wss.map renderWires) ++ "]"

/-- Coefficients/witness values are emitted as DECIMAL STRINGS (signed) so the Rust side reduces
them into the field losslessly regardless of magnitude/sign. ⚠ The sign is why: a coefficient like
`-35` is a full field element after reduction, and a harness that parses these with a fixed-width
integer type silently loses both the magnitude and the sign. -/
def renderIntList (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map (fun i => q (toString i))) ++ "]"

/-- Row indices and slot indices are UNQUOTED — they are array offsets, not field elements. -/
def renderNatList (xs : List Nat) : String :=
  "[" ++ String.intercalate "," (xs.map toString) ++ "]"

def renderGate (g : PlacedGate) : String :=
  "{" ++ q "typ" ++ ":" ++ toString g.kind.ordinal ++ ","
       ++ q "wires" ++ ":" ++ renderWires g.wires ++ ","
       ++ q "coeffs" ++ ":" ++ renderIntList g.coeffs ++ "}"

def renderGates (gs : List PlacedGate) : String :=
  "[" ++ String.intercalate "," (gs.map renderGate) ++ "]"

def renderWitness (w : List (List Int)) : String :=
  "[" ++ String.intercalate "," (w.map renderIntList) ++ "]"

/-! ## §2 — the circuit, as a value, and the one renderer over it. -/

/-- **A renderable kimchi circuit.** Everything a harness needs to build the `Vec<CircuitGate>`, the
`[Vec<F>; COLUMNS]` witness and the public-input vector, plus the two census groups the assembled
step/wrap rungs carry so their tampers aim at what the Lean schedule emitted rather than at a
hand-copied constant.

The three `Option` fields are the whole generalization: they are the field groups the eleven copies
differed by, promoted from "which copy you call" to "what the value says".

  * `publicInput = none` omits the `public_input` key; `some v` emits it, INCLUDING `some []`.
  * `slots = some (derived, unread)` emits `derived_slots` and `unread_slots` together — they are
    one census and a circuit that declared half of it would be worse than one declaring neither.
  * `probeRows = some rs` emits `probe_rows`.

Emission order is fixed and is the order the harnesses' `serde` shapes were written against:
`name`, `public_input_size`, `public_input`, `derived_slots`, `unread_slots`, `num_rows`,
`probe_rows`, `gates`, `witness`. -/
structure KimchiCircuit where
  name        : String
  pubSize     : Nat
  numRows     : Nat
  gates       : List PlacedGate
  witness     : List (List Int)
  publicInput : Option (List Int) := none
  slots       : Option (List Nat × List Nat) := none
  probeRows   : Option (List Nat) := none

/-- One `"key":value,` field. -/
def field (k v : String) : String := q k ++ ":" ++ v ++ ","

/-- A field group that is present or absent by DATA. -/
def optField {α : Type} (k : String) (r : α → String) : Option α → String
  | none => ""
  | some v => field k (r v)

/-- The slot census: both halves or neither. -/
def slotFields : Option (List Nat × List Nat) → String
  | none => ""
  | some du => field "derived_slots" (renderNatList du.1) ++ field "unread_slots" (renderNatList du.2)

/-- **THE renderer.** A pure function of the circuit value; §3 pins it against all four inherited
shapes, generally. -/
def renderCircuit (c : KimchiCircuit) : String :=
  "{" ++ field "name" (q c.name)
      ++ field "public_input_size" (toString c.pubSize)
      ++ optField "public_input" renderIntList c.publicInput
      ++ slotFields c.slots
      ++ field "num_rows" (toString c.numRows)
      ++ optField "probe_rows" renderNatList c.probeRows
      ++ field "gates" (renderGates c.gates)
      ++ q "witness" ++ ":" ++ renderWitness c.witness ++ "}"

/-- A wire-fidelity check object: the render's `placed_wires` (from `place`) vs the o1js
`o1js_wires` golden. The Rust harness parses both and asserts equality — a differential that the
render (Lean → JSON → Rust parse) did not corrupt the byte-exact placement. -/
def renderWireCheck (name : String) (placed o1js : List (List Cell)) : String :=
  "{" ++ q "name" ++ ":" ++ q name ++ ","
       ++ q "placed_wires" ++ ":" ++ renderWireList placed ++ ","
       ++ q "o1js_wires" ++ ":" ++ renderWireList o1js ++ "}"

/-! ## §3 — ⚑ THE EMITTED OBJECT DID NOT MOVE.

⚠ Shapes C and D wrote `":["`, `"],"` and `"]}"` as single literals where the shared vocabulary
splits them across `field`/`renderGates`/`renderWitness`. The three `rfl` identities below re-split
them so the associativity normal form can meet; they are transcription, not content, and each is
`rfl` on a two-character literal. -/

private theorem split_colon_bracket : (":[" : String) = ":" ++ "[" := rfl
private theorem split_bracket_comma : ("]," : String) = "]" ++ "," := rfl
private theorem split_bracket_brace : ("]}" : String) = "]" ++ "}" := rfl

/-! ### The four inherited shapes.

Each theorem below is the deleted copy's chain, transcribed verbatim as the right-hand side, under a
universal quantifier over every argument that copy took. Nothing is instantiated at a fixture; a
shape that these four do not cover is a shape no deleted copy emitted. -/

/-- **SHAPE A** — the seven `pubSize = 0` gate-fixture renderers (`KimchiRender`,
`KimchiRenderPoseidon`, `KimchiRenderCompleteAdd`, `KimchiRenderVarBaseMul`, `KimchiRenderEndoMul`,
`KimchiRenderEndoMulScalar`, `KimchiComposeMSM`) — which emit NO `public_input` key at all. -/
theorem renderCircuit_base_is_the_open_coded_shape
    (name : String) (pubSize numRows : Nat) (gs : List PlacedGate) (w : List (List Int)) :
    renderCircuit { name := name, pubSize := pubSize, numRows := numRows, gates := gs,
                    witness := w } =
      "{" ++ q "name" ++ ":" ++ q name ++ ","
           ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
           ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
           ++ q "gates" ++ ":" ++ renderGates gs ++ ","
           ++ q "witness" ++ ":" ++ renderWitness w ++ "}" := by
  simp only [renderCircuit, field, optField, slotFields, String.append_assoc, String.append_empty]

/-- **SHAPE B** — `KimchiRenderPublicInput` and `KimchiPreimageCircuit`: the public vector travels
with the circuit, because a `pubSize > 0` circuit is not runnable without it. -/
theorem renderCircuit_public_is_the_open_coded_shape
    (name : String) (pubSize numRows : Nat) (gs : List PlacedGate) (w : List (List Int))
    (pub : List Int) :
    renderCircuit { name := name, pubSize := pubSize, numRows := numRows, gates := gs,
                    witness := w, publicInput := some pub } =
      "{" ++ q "name" ++ ":" ++ q name ++ ","
           ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
           ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
           ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
           ++ q "gates" ++ ":" ++ renderGates gs ++ ","
           ++ q "witness" ++ ":" ++ renderWitness w ++ "}" := by
  simp only [renderCircuit, field, optField, slotFields, String.append_assoc, String.append_empty]

/-- **SHAPE C** — `KimchiStepMainCore.renderStepCircuit`: the public vector plus the absolute rows
of the σ-only probes. -/
theorem renderCircuit_step_is_the_open_coded_shape
    (name : String) (pubSize numRows : Nat) (gs : List PlacedGate) (w : List (List Int))
    (pub : List Int) (probes : List Nat) :
    renderCircuit { name := name, pubSize := pubSize, numRows := numRows, gates := gs,
                    witness := w, publicInput := some pub, probeRows := some probes } =
      "{" ++ q "name" ++ ":" ++ q name ++ ","
           ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
           ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
           ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
           ++ q "probe_rows" ++ ":" ++ renderNatList probes ++ ","
           ++ q "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
           ++ q "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}" := by
  simp only [renderCircuit, field, optField, slotFields, renderGates, renderWitness,
             split_colon_bracket, split_bracket_comma, split_bracket_brace,
             String.append_assoc, String.append_empty]

/-- **SHAPE D** — `KimchiWrapMainCore.renderWrapCircuit`: shape C plus the slot census, which
travels WITH the circuit so the harness's public-input polarity measures the 24-vs-40 split instead
of asserting it. -/
theorem renderCircuit_wrap_is_the_open_coded_shape
    (name : String) (pubSize numRows : Nat) (gs : List PlacedGate) (w : List (List Int))
    (pub : List Int) (probes derivedSlots unreadSlots : List Nat) :
    renderCircuit { name := name, pubSize := pubSize, numRows := numRows, gates := gs,
                    witness := w, publicInput := some pub, probeRows := some probes,
                    slots := some (derivedSlots, unreadSlots) } =
      "{" ++ q "name" ++ ":" ++ q name ++ ","
           ++ q "public_input_size" ++ ":" ++ toString pubSize ++ ","
           ++ q "public_input" ++ ":" ++ renderIntList pub ++ ","
           ++ q "derived_slots" ++ ":" ++ renderNatList derivedSlots ++ ","
           ++ q "unread_slots" ++ ":" ++ renderNatList unreadSlots ++ ","
           ++ q "num_rows" ++ ":" ++ toString numRows ++ ","
           ++ q "probe_rows" ++ ":" ++ renderNatList probes ++ ","
           ++ q "gates" ++ ":[" ++ String.intercalate "," (gs.map renderGate) ++ "],"
           ++ q "witness" ++ ":[" ++ String.intercalate "," (w.map renderIntList) ++ "]}" := by
  simp only [renderCircuit, field, optField, slotFields, renderGates, renderWitness,
             split_colon_bracket, split_bracket_comma, split_bracket_brace,
             String.append_assoc]

/-! ### ⚑ …and the presence of a group is NOT its emptiness.

`some []` emits `"key":[],` — the key is there and the array is empty. `none` emits nothing at all.
The wrap and step rungs below their closing rung emit the first; the seven `pubSize = 0` gate
fixtures emit the second. A renderer that inferred presence from emptiness would have collapsed
those two and moved bytes on nine committed artifacts. Both facts are general over the key, and
both can go red. -/

theorem optField_some_nil_still_emits_the_key (k : String) :
    optField k renderIntList (some []) = q k ++ ":" ++ "[]" ++ "," := rfl

theorem optField_none_emits_nothing (k : String) :
    optField k renderIntList none = "" := rfl

#assert_axioms renderCircuit_base_is_the_open_coded_shape
#assert_axioms renderCircuit_public_is_the_open_coded_shape
#assert_axioms renderCircuit_step_is_the_open_coded_shape
#assert_axioms renderCircuit_wrap_is_the_open_coded_shape
#assert_axioms optField_some_nil_still_emits_the_key
#assert_axioms optField_none_emits_nothing

end Dregg2.Circuit.Emit.KimchiCircuitJson
