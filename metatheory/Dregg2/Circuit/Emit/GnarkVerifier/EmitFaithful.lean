/-
# Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful — the emit socket over the R1csFr foundation.

`Dregg2.Exec.CircuitEmit` established the pattern for the ℤ rail: a SEPARATE wire-form
mirror of the circuit AST (`emit`), a decode inverse (`decodeE`), a standalone denotation
for the wire form (`satisfiedEmitted`), and the round-trip + faithfulness theorems
(`decodeE_emit`, `emit_faithful`) — so the emitted bytes are not the proof object by fiat;
the semantic identity is PROVED. This module re-bases that pattern to the gnark target:
the frontend op-DAG of `Dregg2.Circuit.R1csFr` (`Wire`: var/const/add/mul/select over
`Fr = ZMod rBN254`) whose lowering to genuine R1CS carries the proven bridge
`R1csFr.gHolds` (frontend satisfied ↔ lowered R1CS satisfied by the canonical extension)
and the stronger `lower_sound`.

  * **`GnarkCircuitData`** — the emission package: circuit name, public-input map
    (name → frontend variable), gadget-invocation records (which named gnark gadget was
    laid down over which variables), and the `R1csFr.Circuit` itself.
  * **`gHolds d a`** — the package's R1CS-level denotation: the LOWERED system is
    satisfied by the canonical extension of `a` (the form the gnark backend consumes).
  * **`emit` / `decode`** — serializer to the wire mirror (`Emitted`, over `EWire`) and
    its inverse; **`decode_emit`** proves the round trip (`emit` loses nothing).
  * **`emit_faithful`** — THE theorem: `gHolds d a ↔ satisfiedEmitted (emit d) a`.
    It composes the proven `R1csFr.gHolds` bridge with pointwise evaluation agreement
    (`emitW_eval`), so satisfaction of the WIRE FORM is exactly satisfaction of the
    lowered R1CS — end to end, for every package and every witness.

The JSON byte grammar for `Emitted` lives in `EmitJson.lean`; the toy end-to-end
∀-refinement (an emitted `AssertIsCanonical` provably equivalent to `val < BabyBearP`)
lives in `CanonicityToy.lean`.
-/
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr

/-! ## §1 The emission package. -/

/-- One recorded gadget invocation: the gnark gadget's name (e.g. `AssertIsCanonical`)
and the frontend variables it was laid down over. Wire metadata — the constraint content
is carried by the circuit's asserts; the record lets the Go side name-check the layout. -/
structure GadgetInvocation where
  gadget : String
  args   : List Nat
  deriving Repr, DecidableEq

/-- **The emission package**: name + public-input map + gadget-invocation records + the
frontend circuit (the `R1csFr` op-DAG whose lowering is genuine R1CS). -/
structure GnarkCircuitData where
  name         : String
  publicInputs : List (String × Nat)
  gadgets      : List GadgetInvocation
  circuit      : Circuit

/-- **`gHolds`** — the package's R1CS-level denotation: the lowered system of the
package's circuit is satisfied by the canonical witness extension of `a`. By
`R1csFr.gHolds` this is equivalent to frontend acceptance; stating it at the R1CS level
keeps the emit theorem anchored to the object the gnark backend actually consumes. -/
def gHolds (d : GnarkCircuitData) (a : Assignment) : Prop :=
  r1csSatisfied d.circuit.lower (d.circuit.extend a)

/-! ## §2 The wire mirror — a separate inductive, so emission is a real serialization
step with its own faithfulness obligation (the `CircuitEmit` discipline). -/

/-- The wire-form mirror of `R1csFr.Wire` (var/const/add/mul/select over `Fr`). -/
inductive EWire where
  | var    : Nat → EWire
  | const  : Fr → EWire
  | add    : EWire → EWire → EWire
  | mul    : EWire → EWire → EWire
  | select : EWire → EWire → EWire → EWire

/-- The wire-form package: metadata verbatim, asserts as `EWire` pairs. -/
structure Emitted where
  name         : String
  publicInputs : List (String × Nat)
  gadgets      : List GadgetInvocation
  asserts      : List (EWire × EWire)

/-- Serialize one wire. Structure-preserving by construction. -/
def emitW : Wire → EWire
  | .var v        => .var v
  | .const c      => .const c
  | .add x y      => .add (emitW x) (emitW y)
  | .mul x y      => .mul (emitW x) (emitW y)
  | .select b x y => .select (emitW b) (emitW x) (emitW y)

/-- **`emit`** — the deterministic serializer `GnarkCircuitData → Emitted`. -/
def emit (d : GnarkCircuitData) : Emitted :=
  { name         := d.name
    publicInputs := d.publicInputs
    gadgets      := d.gadgets
    asserts      := d.circuit.asserts.map fun p => (emitW p.1, emitW p.2) }

/-- Deserialize one wire (the inverse used to state/prove the round trip). -/
def decodeW : EWire → Wire
  | .var v        => .var v
  | .const c      => .const c
  | .add x y      => .add (decodeW x) (decodeW y)
  | .mul x y      => .mul (decodeW x) (decodeW y)
  | .select b x y => .select (decodeW b) (decodeW x) (decodeW y)

/-- **`decode`** — the inverse deserializer `Emitted → GnarkCircuitData`. -/
def decode (e : Emitted) : GnarkCircuitData :=
  { name         := e.name
    publicInputs := e.publicInputs
    gadgets      := e.gadgets
    circuit      := ⟨e.asserts.map fun p => (decodeW p.1, decodeW p.2)⟩ }

/-- Standalone denotation of an emitted wire (so the wire form is not evaluated "via
decode by fiat" — agreement with `Wire.eval` is a theorem, `emitW_eval`). -/
def EWire.eval : EWire → Assignment → Fr
  | .var v,        a => a v
  | .const c,      _ => c
  | .add x y,      a => x.eval a + y.eval a
  | .mul x y,      a => x.eval a * y.eval a
  | .select b x y, a => b.eval a * (x.eval a - y.eval a) + y.eval a

/-- **`satisfiedEmitted`** — the wire form's own notion of satisfaction: every emitted
assert pair evaluates equal. -/
def satisfiedEmitted (e : Emitted) (a : Assignment) : Prop :=
  ∀ p ∈ e.asserts, p.1.eval a = p.2.eval a

instance (e : Emitted) (a : Assignment) : Decidable (satisfiedEmitted e a) :=
  inferInstanceAs (Decidable (∀ p ∈ e.asserts, p.1.eval a = p.2.eval a))

/-! ## §3 Round trip + evaluation agreement. -/

/-- `decodeW ∘ emitW = id`: serialization then decode recovers the original wire. -/
theorem decodeW_emitW (w : Wire) : decodeW (emitW w) = w := by
  induction w with
  | var v => rfl
  | const c => rfl
  | add x y ihx ihy => simp [emitW, decodeW, ihx, ihy]
  | mul x y ihx ihy => simp [emitW, decodeW, ihx, ihy]
  | select b x y ihb ihx ihy => simp [emitW, decodeW, ihb, ihx, ihy]

/-- The emitted wire's standalone denotation agrees pointwise with the frontend's. -/
theorem emitW_eval (w : Wire) (a : Assignment) : (emitW w).eval a = w.eval a := by
  induction w with
  | var v => rfl
  | const c => rfl
  | add x y ihx ihy => simp [emitW, EWire.eval, Wire.eval, ihx, ihy]
  | mul x y ihx ihy => simp [emitW, EWire.eval, Wire.eval, ihx, ihy]
  | select b x y ihb ihx ihy => simp [emitW, EWire.eval, Wire.eval, ihb, ihx, ihy]

/-- **`decode_emit`** — the round trip at the package level: `emit` loses nothing (so no
two packages collide on the wire; the serializer is injective). -/
theorem decode_emit (d : GnarkCircuitData) : decode (emit d) = d := by
  obtain ⟨name, pis, gads, ⟨asserts⟩⟩ := d
  simp only [decode, emit, List.map_map]
  have h : asserts.map
      ((fun p => (decodeW p.1, decodeW p.2)) ∘ fun p : Wire × Wire => (emitW p.1, emitW p.2))
      = asserts :=
    (List.map_congr_left fun p _ => by
      simp [Function.comp, decodeW_emitW]).trans (List.map_id asserts)
  rw [h]

/-! ## §4 `emit_faithful` — THE deliverable. -/

/-- **`emit_faithful`.** The package's R1CS-level denotation holds IFF the emitted wire
form is satisfied — for every package and every witness. Composes the PROVEN
`R1csFr.gHolds` bridge (frontend ↔ lowered R1CS, riding `lower_sound`) with pointwise
wire-denotation agreement (`emitW_eval`): the bytes the emitter ships denote exactly the
R1CS the foundation verified. -/
theorem emit_faithful (d : GnarkCircuitData) (a : Assignment) :
    gHolds d a ↔ satisfiedEmitted (emit d) a := by
  unfold gHolds
  rw [← R1csFr.gHolds]
  unfold Circuit.satisfied satisfiedEmitted emit
  simp only [List.mem_map]
  constructor
  · rintro h p ⟨q, hq, rfl⟩
    simpa only [emitW_eval] using h q hq
  · intro h p hp
    simpa only [emitW_eval] using h (emitW p.1, emitW p.2) ⟨p, hp, rfl⟩

#assert_axioms decodeW_emitW
#assert_axioms emitW_eval
#assert_axioms decode_emit
#assert_axioms emit_faithful

end Dregg2.Circuit.Emit.GnarkVerifier
