/-
# Dregg2.Circuit.Emit.GarbledEvalEmit — the emit-from-Lean descriptor for GARBLED-CIRCUIT
EVALUATION (the production 56-column DSL AIR).

## What this file IS

An `EffectVmDescriptor2` that DECLARES, in the IR-v2 grammar, the per-row relation the
hand-authored 56-column garbled-evaluation DSL descriptor enforces
(`circuit/src/dsl/garbled.rs::garbled_extended_descriptor`, which SUPERSEDES the deprecated
49-column `circuit/src/garbled_air.rs::GarbledEvaluationAir`). The row is one garbled-gate
evaluation. The constraints emitted here are, term-for-term, the DSL's:

  * C1-C8   — `circuit_commitment[0..4]` / `output_label_hash[0..4]` pinned to the 8 public
              inputs (`ConstraintExpr::PiBinding` + `BoundaryDef::PiBinding`, first row);
  * C9-C16  — DECRYPTION CORRECTNESS, gated on `(1 - is_padding)`:
              `output(i) - table_entry(i) + hash_out(i) == 0`
              (`ConstraintExpr::InvertedGated` over the 3-term `Polynomial`);
  * C17-C22 — the six BOOLEAN selectors `is_and, is_or, is_xor, is_not, chain_flag, is_padding`
              (`ConstraintExpr::Binary`, `x·(x-1) == 0`);
  * C23     — GATE-TYPE EXCLUSIVITY, gated on `(1 - is_padding)`:
              `is_and + is_or + is_xor + is_not - 1 == 0`;
  * C24-C31 — WIRE CHAINING (the cross-row leg): `chain_flag · (next.left(i) - output(i)) == 0`
              (`ConstraintExpr::Gated` over `ConstraintExpr::Transition`) — the two-row window
              gate `windowGate (onTransition := true)`;
  * boundary — first-row `gate_index_delta == 0` (`BoundaryDef::Fixed`).

The emitted JSON (`emitVmJson2`) is BYTE-PINNED below (`#guard`). The Rust equality gate
(`circuit-prove/tests/garbled_eval_emit_gate.rs`) DECODES this exact string via
`parse_vm_descriptor2`, asserts it EQUALS an independently Rust-built descriptor, proves an
HONEST evaluation witness through the REAL `prove_vm_descriptor2` / `verify_vm_descriptor2`
(ACCEPT), and mutates the witness six ways (each biting a distinct constraint family) to force
real UNSAT (the mutation canary).

## ⚑ THE NAMED, EXECUTOR-VERIFIED CARRIER (the DECO-leaf / soundness-gap posture — honest scope)

Neither the hand-AIR nor the DSL descriptor CONSTRAINS the garbling hash: the columns
`hash_out(i)` are FREE witnesses, and `hash_out == Poseidon2(left || right || gate_index)` /
`circuit_commitment == Poseidon2(tables)` / `output_label_hash == Poseidon2(output_label)` are
computed ENTIRELY in Rust witness-gen (`circuit/src/garbled.rs`), NOT in-circuit
(`garbled_air.rs:24`, `dsl/garbled.rs:1-5`). This descriptor is a FAITHFUL mirror of that hand
artifact: it therefore emits NO Poseidon2 chip lookup for the digest columns — adding one would
be a MORE-than-the-hand-AIR divergence. The Poseidon2 garbling-hash binding is left NAMED as an
EXECUTOR-VERIFIED carrier (the honest garbled-circuit semantics: the evaluator, holding the
labels, computes the digests; the AIR proves the DECRYPTION algebra `output = table - hash` over
those digests). The Yao 2PC correctness / input-privacy carriers proved in
`metatheory/Dregg2/Crypto/GarbledJoint.lean` are the SEMANTIC-LAYER twin (privacy floor); they
model the protocol, not this AIR trace layout, so they do NOT feed this emit.

## ⚑ THE VERIFIER-WRAPPER TOOTH (preserved as a named check, not silently dropped)

The DSL binds only the FIRST 4 felts of each 8-felt `WideHash` in-circuit (`piCount = 8 = 4+4`,
the reused 4-felt `col::CIRCUIT_COMMITMENT` / `col::OUTPUT_LABEL_HASH` columns). The FULL 8-felt
(~124-bit) match is a VERIFIER-SIDE struct equality in
`circuit/src/dsl/garbled.rs::verify_garbled_evaluation_dsl` (`proof.circuit_commitment !=
*expected_circuit_commitment` → reject). That wrapper check is off-descriptor by design; it is
NAMED here (and re-stated in the gate test doc) rather than emitted as a base gate, because the
descriptor's PI vector is 4+4 felts wide.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven,
non-vacuous semantic lemma (`decryption_body_zero_iff`, TRUE iff `output = table - hash` on a
non-padding row, FALSE otherwise). `#assert_axioms decryption_body_zero_iff` ⊆ {}. NEW file;
imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.GarbledEvalEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 WindowExpr WindowConstraint emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (the reused 56-column `col::` / `ext_col::` map). -/

/-- Left input label element `i` (columns 0..7). -/
def LEFT (i : Nat) : Nat := 0 + i
/-- Right input label element `i` (columns 8..15). -/
def RIGHT (i : Nat) : Nat := 8 + i
/-- Gate index (column 16). -/
def GATE_INDEX : Nat := 16
/-- Hash-output digest element `i` (columns 17..24) — a FREE witness (see the named-carrier note). -/
def HASH_OUT (i : Nat) : Nat := 17 + i
/-- Garbled table entry (ciphertext) element `i` (columns 25..32). -/
def TABLE_ENTRY (i : Nat) : Nat := 25 + i
/-- Decrypted output label element `i` (columns 33..40). -/
def OUTPUT (i : Nat) : Nat := 33 + i
/-- Circuit-commitment binding block (4 felts, columns 41..44). -/
def CIRCUIT_COMMITMENT : Nat := 41
/-- Output-label-hash binding block (4 felts, columns 45..48). -/
def OUTPUT_LABEL_HASH : Nat := 45
/-- Gate-type selector: AND (column 49). -/
def IS_AND : Nat := 49
/-- Gate-type selector: OR (column 50). -/
def IS_OR : Nat := 50
/-- Gate-type selector: XOR (column 51). -/
def IS_XOR : Nat := 51
/-- Gate-type selector: NOT (column 52). -/
def IS_NOT : Nat := 52
/-- Chain flag: 1 iff this row's output feeds the next row's left input (column 53). -/
def CHAIN_FLAG : Nat := 53
/-- Gate-index delta (column 54). -/
def GATE_INDEX_DELTA : Nat := 54
/-- Padding flag: 1 on padding rows, relaxing the gated constraints (column 55). -/
def IS_PADDING : Nat := 55
/-- Total main-trace width (56). -/
def GARBLED_WIDTH : Nat := 56
/-- Public-input count: `circuit_commitment[0..4]` + `output_label_hash[0..4]` = 8. -/
def PI_COUNT : Nat := 8

/-! ## §2 — The constraint bodies (term-for-term twins of the DSL `ConstraintExpr`s). -/

/-- `(1 - is_padding)` — the `InvertedGated` selector factor. -/
def notPadding : EmittedExpr := .add (.const 1) (.mul (.const (-1)) (.var IS_PADDING))

/-- Decryption-correctness body, lane `i`:
`(1 - is_padding) · (output(i) - table_entry(i) + hash_out(i))`. -/
def decBody (i : Nat) : EmittedExpr :=
  .mul notPadding
    (.add (.var (OUTPUT i)) (.add (.mul (.const (-1)) (.var (TABLE_ENTRY i))) (.var (HASH_OUT i))))

/-- The 8 decryption gates (`ConstraintExpr::InvertedGated`, C9-C16). -/
def decryptionGates : List VmConstraint2 :=
  (List.range 8).map (fun i => .base (.gate (decBody i)))

/-- The `Binary` body for column `c`: `c · (c - 1)`. -/
def binBody (c : Nat) : EmittedExpr := .mul (.var c) (.add (.var c) (.const (-1)))

/-- The six boolean-selector gates (`ConstraintExpr::Binary`, C17-C22). -/
def selectorBinaryGates : List VmConstraint2 :=
  [ .base (.gate (binBody IS_AND))
  , .base (.gate (binBody IS_OR))
  , .base (.gate (binBody IS_XOR))
  , .base (.gate (binBody IS_NOT))
  , .base (.gate (binBody CHAIN_FLAG))
  , .base (.gate (binBody IS_PADDING)) ]

/-- Gate-type exclusivity body:
`(1 - is_padding) · (is_and + is_or + is_xor + is_not - 1)` (C23). -/
def exclusivityBody : EmittedExpr :=
  .mul notPadding
    (.add (.var IS_AND) (.add (.var IS_OR) (.add (.var IS_XOR) (.add (.var IS_NOT) (.const (-1))))))

/-- Wire-chaining window body, lane `i`: `chain_flag · (next.left(i) - output(i))` — the two-row
`Gated`/`Transition` leg (C24-C31). -/
def chainBody (i : Nat) : WindowExpr :=
  .mul (.loc CHAIN_FLAG) (.add (.nxt (LEFT i)) (.mul (.const (-1)) (.loc (OUTPUT i))))

/-- The 8 wire-chaining window gates (asserted on the transition, the last row exempt). -/
def chainingGates : List VmConstraint2 :=
  (List.range 8).map (fun i => .windowGate ⟨chainBody i, true⟩)

/-- Circuit-commitment first-row PI pins (C1-C4 + the matching boundaries). -/
def commitmentPins : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.piBinding VmRow.first (CIRCUIT_COMMITMENT + i) i))

/-- Output-label-hash first-row PI pins (C5-C8 + the matching boundaries). -/
def outputHashPins : List VmConstraint2 :=
  (List.range 4).map (fun i => .base (.piBinding VmRow.first (OUTPUT_LABEL_HASH + i) (4 + i)))

/-- First-row boundary `gate_index_delta == 0` (`BoundaryDef::Fixed`). -/
def gateIndexDeltaBoundary : VmConstraint2 := .base (.boundary VmRow.first (.var GATE_INDEX_DELTA))

/-! ## §3 — The descriptor. -/

/-- **`garbledEvalDesc`** — the production 56-column garbled-evaluation descriptor, emitted from
Lean. Constraint order mirrors `garbled_extended_descriptor`: the 8 first-row PI pins, the 8
decryption gates, the 6 boolean selectors, the exclusivity gate, the 8 wire-chaining window
gates, and the first-row `gate_index_delta` boundary. NO tables (the garbling hash is the named
executor-verified carrier — the descriptor proves the decryption algebra, not the Poseidon2). -/
def garbledEvalDesc : EffectVmDescriptor2 :=
  { name        := "dregg-garbled-evaluation-extended-dsl-v1"
  , traceWidth  := GARBLED_WIDTH
  , piCount     := PI_COUNT
  , tables      := []
  , constraints :=
      commitmentPins ++ outputHashPins ++ decryptionGates
        ++ selectorBinaryGates ++ [.base (.gate exclusivityBody)]
        ++ chainingGates ++ [gateIndexDeltaBoundary]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/garbled_eval_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the
Rust `assert_eq!(decoded, hand_built)` — neither can silently diverge. -/

#guard emitVmJson2 garbledEvalDesc ==
  "{\"name\":\"dregg-garbled-evaluation-extended-dsl-v1\",\"ir\":2,\"trace_width\":56,\"public_input_count\":8,\"tables\":[],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":41,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":42,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":43,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":44,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":45,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":46,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":47,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":48,\"pi_index\":7},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":33},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}},\"r\":{\"t\":\"var\",\"v\":17}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":34},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"var\",\"v\":18}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":35},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"var\",\"v\":19}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":36},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"var\",\"v\":20}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":37},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":29}},\"r\":{\"t\":\"var\",\"v\":21}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":38},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":30}},\"r\":{\"t\":\"var\",\"v\":22}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":39},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":31}},\"r\":{\"t\":\"var\",\"v\":23}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":40},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":32}},\"r\":{\"t\":\"var\",\"v\":24}}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":53},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":55},\"r\":{\"t\":\"const\",\"v\":-1}}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":55}}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":49},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":50},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":51},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":52},\"r\":{\"t\":\"const\",\"v\":-1}}}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":0},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":33}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":34}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":35}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":36}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":4},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":37}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":5},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":38}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":6},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":39}}}}},{\"t\":\"window_gate\",\"on_transition\":true,\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"loc\",\"c\":53},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"nxt\",\"c\":7},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"loc\",\"c\":40}}}}},{\"t\":\"boundary\",\"row\":\"first\",\"body\":{\"t\":\"var\",\"v\":54}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §5 — A genuinely-proven, non-vacuous semantic lemma (the decryption tooth). -/

/-- **The decryption-correctness crux.** The gated body vanishes over `ℤ` EXACTLY when the row is
padding OR the decryption algebra holds (`output = table_entry - hash_out`) — TRUE for an honest
non-padding evaluation, FALSE when a garbled ciphertext / digest is forged. This is the tooth the
mutation canary (`forged_table_entry_refuses`) drives on the emitted descriptor. -/
theorem decryption_body_zero_iff (i : Nat) (a : Assignment) :
    (decBody i).eval a = 0 ↔
      a IS_PADDING = 1 ∨ a (OUTPUT i) = a (TABLE_ENTRY i) - a (HASH_OUT i) := by
  simp only [decBody, notPadding, EmittedExpr.eval]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h0 | h1
    · left; omega
    · right; omega
  · rintro (h | h) <;> rw [h] <;> ring

-- Non-vacuity witnesses: the decryption gate ACCEPTS an honest non-padding row (5 = 8 - 3) and
-- REJECTS a forged ciphertext (5 ≠ 9 - 3).
#guard decide ((decBody 0).eval
  (fun i => if i = OUTPUT 0 then 5 else if i = TABLE_ENTRY 0 then 8
            else if i = HASH_OUT 0 then 3 else 0) = 0)
#guard decide (¬ ((decBody 0).eval
  (fun i => if i = OUTPUT 0 then 5 else if i = TABLE_ENTRY 0 then 9
            else if i = HASH_OUT 0 then 3 else 0) = 0))

/-! ## §6 — Shape pins (the Rust gate asserts the SAME shape on the decoded twin). -/

#guard garbledEvalDesc.name == "dregg-garbled-evaluation-extended-dsl-v1"
#guard garbledEvalDesc.traceWidth == 56
#guard garbledEvalDesc.piCount == 8
#guard garbledEvalDesc.constraints.length == 32
#guard (garbledEvalDesc.constraints.filter
          (fun c => match c with | .windowGate _ => true | _ => false)).length == 8
#guard (garbledEvalDesc.constraints.filter
          (fun c => match c with | .base (.piBinding _ _ _) => true | _ => false)).length == 8

#assert_axioms decryption_body_zero_iff

end Dregg2.Circuit.Emit.GarbledEvalEmit
