/-
# CanonicalCodecFalsifier — the rejector calibration for the `Canonical` deriving handler.

**This file was written BEFORE the handler it calibrates.** Its job is to make three
failures LOUD, and to make one already-shipped weakness VISIBLE as a theorem:

1. **A field type with no proved codec law cannot be derived.** `Digest32` has NO
   `parseBytes32Hex? (bytes32Hex d) = some d` lemma anywhere in this tree (measured
   2026-08-05: `Emit.lean` proves only two `native_decide` point vectors,
   `parseBytes32Hex_test_federation_vector` and `parseBytes32Hex_refuses_display_label`).
   So there is deliberately no `HasFieldCodec Digest32`, and a digest-bearing record
   REFUSES to derive rather than deriving a weaker theorem quietly.
2. **A codec whose reader disagrees with its writer cannot be packaged at all.** The
   roundtrip law is a FIELD of `FieldCodec`, so a wrong codec is a type error, not a
   failing test. `#assert_term_refused` pins that the type error still happens — and
   refuses a term that only elaborated because Lean recovered with `sorryAx`.
3. **The `_reencodes` shape that 33 PoA roundtrip theorems use is satisfied by a decoder
   that accepts NOTHING.** `blindDecode_reencodes` below is that theorem, proved, over a
   decoder defined as `fun _ => none`. It is the vacuity this lane exists to stop being
   able to hide inside a *derived* theorem, where it would look like uniform coverage.

`#assert_codec_nonvacuous` must REJECT the shape in (3) and ACCEPT the derived shape.
Both directions are exercised here; a checker that only ever passes is not a checker.

Everything tagged `@[linter_calibration]` in this file is a DELIBERATE fixture built to be
rejected. It is not spec debt. (Same discipline as `Dregg2/Tactics.lean`'s calibration pair.)
-/
import Dregg2.Games.PathOfAngels.CanonicalCodec
import Dregg2.Games.PathOfAngels.Core

namespace Dregg2.Games.PathOfAngels.CanonicalCodecFalsifier

open Lean
open Dregg2.Canonical

set_option autoImplicit false

/-! ## F1 — a field with no proved law REFUSES to derive.

`Digest32` is the single field type that blocks a derived roundtrip for most of the PoA
wire tower: `WorldWire`, `OfficerWire`, `VisitKeyWire`, `ServingWire`, every envelope.
The blocker is exactly one missing lemma. Naming it here, in a build-time refusal, is the
point: the coverage gap becomes uneven BY DESIGN AND VISIBLE instead of uneven by accident.
-/

/-- DELIBERATE: a record whose only field is a digest. There is no `HasFieldCodec Digest32`
(and there must not be one until `Emit.parseBytes32Hex? (Emit.bytes32Hex d) = some d` is a
theorem), so deriving `Canonical` for it must FAIL. -/
@[linter_calibration]
structure SealBearingWire where
  seal : Digest32
deriving DecidableEq

#assert_derive_refuses SealBearingWire

/-! ## F2 — a codec whose reader disagrees with its writer cannot be CONSTRUCTED.

The roundtrip law is a field of `FieldCodec`, so this is a type error and not a red test.
`#assert_term_refused` pins that it stays one. It treats "elaborated, but the proof term
contains `sorryAx`" as a REFUSAL, because Lean recovers from a failed `by` block by
inserting `sorryAx` — without that check the falsifier would pass on the wrong evidence.
-/

/-- DELIBERATE: an off-by-one reader. `read (toJson a)` is `.ok (a+1)`, never `.ok a`,
so the law field has no inhabitant and `rfl` cannot close it. If this command ever stops
throwing, the law field has gone vacuous (or `#assert_term_refused` has gone blind). -/
#assert_term_refused (
  ({ ok := fun _ => true
     toJson := Dregg2.Canonical.natToJson
     render := toString
     read := fun j => (Dregg2.Canonical.natRead 64 j).map (· + 1)
     read_toJson := by intro a _; rfl } : Dregg2.Canonical.FieldCodec Nat))

/-- DELIBERATE: a reader that drops the bound the writer's `ok` advertises. `ok` claims
every `Nat` is fine while `read` refuses anything over 64, so the law is FALSE (take
`a = 65`) and no proof exists. Calibrates that the law really ties `ok` to `read`. -/
#assert_term_refused (
  ({ ok := fun _ => true
     toJson := Dregg2.Canonical.natToJson
     render := toString
     read := Dregg2.Canonical.natRead 64
     read_toJson := by intro a _; rfl } : Dregg2.Canonical.FieldCodec Nat))

/-- POSITIVE CONTROL for F2, through the SAME probe. `#assert_term_refused` is a pure
rejector, so it cannot detect its own blindness: if the probe broke and started reporting
every term refused, both fixtures above would look perfect. This is the same codec shape
with an honest reader; it must elaborate, and it is checked by the dual command rather than
by a plain `example`, because an `example` does not go through `runProbe` and so would not
notice the probe failing. -/
#assert_term_elaborates (
  ({ ok := fun n => decide (n ≤ 64)
     toJson := Dregg2.Canonical.natToJson
     render := toString
     read := Dregg2.Canonical.natRead 64
     read_toJson := Dregg2.Canonical.natRead_natToJson 64 } :
    Dregg2.Canonical.FieldCodec Nat))

/-! ## F3 — the vacuity that a derived theorem must never inherit.

Every canonical-wire module in PoA proves exactly one universally-quantified roundtrip
fact, in this shape (measured 2026-08-05: 33 `_reencodes` theorems across 8 modules, each
module carrying its own copy of the same generic `canonicalDecode_reencodes` lemma):

    decode bytes = some value → encode value = bytes

Read it carefully. It constrains the decoder only on inputs the decoder ACCEPTS. A decoder
that accepts nothing satisfies it for free, and so does a decoder that accepts nothing the
encoder can produce. The theorem below is that observation, proved.

This is not a defect in the shipped theorems — canonicality is a real property and they
state it correctly. It is a statement about what the shape can and cannot buy: it buys
"accepted bytes are canonical", it does NOT buy "the encoder's output is accepted". No PoA
module proves the second for a general value; the strongest evidence in tree is a handful of
per-fixture `native_decide` roundtrips (`fixture_input_roundtrip`, `fixture_beta_seal_roundtrip`,
`strict_command_roundtrip`, …) — one point each.
-/

/-- DELIBERATE: a decoder that accepts NOTHING. -/
@[linter_calibration]
def blindDecode (_bytes : String) : Option Nat := none

/-- DELIBERATE, and TRUE: the `_reencodes` shape, discharged over a decoder that accepts
nothing, by a term proof with no content. Vacuity is not hypothetical here; it is this
declaration. `#assert_codec_nonvacuous` must reject a "roundtrip" of this shape. -/
@[linter_calibration]
theorem blindDecode_reencodes {bytes : String} {value : Nat}
    (accepted : blindDecode bytes = some value) : toString value = bytes :=
  absurd accepted (by simp [blindDecode])

#assert_axioms blindDecode_reencodes

/-- The counterpart the derived handler produces instead. Stated here on the raw field
codec so the calibration does not depend on any derived instance existing yet: the reader
accepts EVERY value the writer can emit, universally quantified, conclusion `Except.ok`.
This is the shape `#assert_codec_nonvacuous` requires. -/
theorem natField_accepts_every_encoding (limit n : Nat) (bounded : decide (n ≤ limit) = true) :
    Dregg2.Canonical.natRead limit (Dregg2.Canonical.natToJson n) = Except.ok n :=
  Dregg2.Canonical.natRead_natToJson limit n bounded

#assert_axioms natField_accepts_every_encoding

/-- The satisfiability witness for the hypothesis of the theorem above. A conditional
roundtrip whose condition is unsatisfiable is vacuous in a second, quieter way; this is
why `#assert_codec_nonvacuous` demands a `canonWf` witness alongside the theorem. -/
theorem natField_bound_is_satisfiable :
    decide ((7 : Nat) ≤ Dregg2.Canonical.WIRE_U64_MAX) = true := by decide

#assert_axioms natField_bound_is_satisfiable

end Dregg2.Games.PathOfAngels.CanonicalCodecFalsifier
