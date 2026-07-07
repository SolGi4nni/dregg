/-
# Dregg2.Circuit.Emit.Poseidon2HashEmit — the RAW Poseidon2 hash, emitted from Lean.

## What this file IS

The emit-from-Lean face of the deprecated hand AIR `Poseidon2Air` (`circuit/src/poseidon2_air.rs:54`):
"a public digest is the Poseidon2 hash of a public preimage". Where `MerkleMembershipEmit.lean` keeps
the preimage PRIVATE and pins only the root, this file is the standalone HASH primitive — both the
preimage and the digest are exposed as public inputs (the `Poseidon2Air.boundary_constraints` shape,
`poseidon2_air.rs:135-148`, which pins row-0 input columns to `PI[0..WIDTH]` and output columns to
`PI[WIDTH..2*WIDTH]`). The single permutation (`Poseidon2Air.eval_constraints`, `poseidon2_air.rs:114-120`,
which computes the WHOLE permutation natively) maps to ONE `Poseidon2Chip` lookup — `hash_2_to_1`'s exact
rate-4 seeding (`state[0..2] = (a,b)`, `state[4] = 2`, rest `0`; `poseidon2.rs:365` / the chip's
`hash2_state_c`, `descriptor_ir2.rs:3409`).

## Constraint → IR-v2 map (audited against `circuit/src/poseidon2_air.rs`)

  * `Poseidon2Air.eval_constraints` (the native permutation, out == permute(in))
        → ONE `VmConstraint2.lookup` on `TID_P2` (arity-2 absorb `[IN0,IN1]`, out0 = `DIGEST`, lanes 1..7
          witnessed) — the chip AIR binds `out0..out7` to the genuine permutation (`descriptor_ir2.rs:2525`),
          so a forged digest names no serving chip row → UNSAT.
  * `Poseidon2Air.boundary_constraints` (row-0 input pinned to input PIs, output pinned to output PIs)
        → three `VmConstraint2.base (.piBinding VmRow.first · ·)` pins: `IN0→PI0`, `IN1→PI1`, `DIGEST→PI2`.

The chip table (`TID_P2`) is Presence-detected from the lookup, so `tables` is empty (as `node8`/`deco` /
`MerkleMembershipEmit` leave it).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven, load-bearing
semantic lemma (`digest_forced`), the hash-binding lever `chip_lookup_sound` instantiated at this exact
lookup. `#assert_axioms digest_forced ⊆ {propext, Classical.choice, Quot.sound}` (actually `{propext,
Quot.sound}`). NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.Poseidon2HashEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   Table ChipTableSound chip_lookup_sound emitVmJson2)

set_option autoImplicit false

/-! ## §1 — The trace column layout (a single logical row; arity-2 absorb). -/

/-- Preimage element 0 (the hash's left input). -/
def IN0 : Nat := 0
/-- Preimage element 1 (the hash's right input). -/
def IN1 : Nat := 1
/-- The digest = `hash_2_to_1(IN0, IN1)` (chip lookup out0). -/
def DIGEST : Nat := 2
/-- The seven exposed permutation lane columns 1..7 of the chip lookup (out0 is `DIGEST`; the lanes
are witnessed by the chip AIR's `out[i] == lane[i]` equalities, `descriptor_ir2.rs:2529-2531`). -/
def LANES : List Nat := [3, 4, 5, 6, 7, 8, 9]

/-- Total main-trace width: 3 base columns (2 preimage + digest) + 7 chip lanes. -/
def HASH_WIDTH : Nat := 10

/-! ## §2 — The constraint list (one child→digest chip lookup · three boundary pins). -/

/-- The `preimage → digest` step: an arity-2 `Poseidon2Chip` lookup absorbing `[IN0, IN1]`, binding
out0 to `DIGEST` (the `hash_2_to_1` shape). -/
def hashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, chipLookupTuple [.var IN0, .var IN1] DIGEST LANES⟩

/-- Pin: preimage element 0 equals the public input `PI[0]` on the first row (the input boundary). -/
def in0Pin : VmConstraint2 := .base (.piBinding VmRow.first IN0 0)
/-- Pin: preimage element 1 equals the public input `PI[1]` on the first row. -/
def in1Pin : VmConstraint2 := .base (.piBinding VmRow.first IN1 1)
/-- Pin: the digest equals the public input `PI[2]` on the first row (the output boundary). -/
def digestPin : VmConstraint2 := .base (.piBinding VmRow.first DIGEST 2)

/-- **`poseidon2HashDesc`** — the standalone arity-2 Poseidon2-hash descriptor. Constraints: one
`preimage → digest` chip lookup, and the three boundary pins exposing the preimage and the digest as
public inputs (the `Poseidon2Air` shape). -/
def poseidon2HashDesc : EffectVmDescriptor2 :=
  { name        := "poseidon2-hash-arity2::poseidon2-v1"
  , traceWidth  := HASH_WIDTH
  , piCount     := 3
  , tables      := []
  , constraints := [hashLookup, in0Pin, in1Pin, digestPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3 — The byte-pinned wire golden (the Rust decoder ingests THIS string).

THE EQUALITY-GATE ANCHOR: this exact string is embedded verbatim in
`circuit-prove/tests/poseidon2_hash_emit_gate.rs` (`GOLDEN_JSON`), decoded there via
`parse_vm_descriptor2`, and proven. A drift on either side breaks THIS `#guard` (Lean) or the Rust
`assert_eq!(decoded, hand_built)`. -/

#guard emitVmJson2 poseidon2HashDesc ==
  "{\"name\":\"poseidon2-hash-arity2::poseidon2-v1\",\"ir\":2,\"trace_width\":10,\"public_input_count\":3,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"var\",\"v\":9}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, load-bearing semantic lemma (the hash-binding teeth).

Against a SOUND chip table, the emitted arity-2 lookup FORCES the digest column to carry the genuine
hash of the two preimage columns — the exact family lever ~15 hash-carrying descriptors depend on
(`chip_lookup_sound`, `DescriptorIR2.lean:1159`), instantiated at THIS lookup. This is the Lean face of
the chip AIR's `out0 == permute(seed)[0]` binding the Rust gate exercises end-to-end. -/
theorem digest_forced (hash : List ℤ → ℤ) (tbl : Table) (hSound : ChipTableSound hash tbl)
    (a : Assignment)
    (hmem : (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval a) ∈ tbl) :
    a DIGEST = hash [a IN0, a IN1] := by
  have h := chip_lookup_sound hash tbl hSound a [.var IN0, .var IN1] DIGEST LANES
    (by simp [CHIP_RATE]) hmem
  simpa [EmittedExpr.eval] using h

-- Non-vacuity of the emitted tuple — the digest + preimage columns are LOAD-BEARING (a forged
-- digest / preimage is a DIFFERENT lookup tuple → an unserved chip row), and columns the tuple does
-- NOT read cannot perturb it (a genuine TRUE-and-FALSE pair: the tuple reads EXACTLY IN0/IN1/DIGEST).
#guard decide
  ((chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = DIGEST then (7 : ℤ) else 0))
    ≠ (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = DIGEST then (8 : ℤ) else 0)))
#guard decide
  ((chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = IN0 then (7 : ℤ) else 0))
    ≠ (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = IN0 then (8 : ℤ) else 0)))
#guard decide
  ((chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = 50 then (7 : ℤ) else 0))
    = (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).map (·.eval (fun i => if i = 50 then (8 : ℤ) else 0)))

-- Shape pins.
#guard poseidon2HashDesc.traceWidth == HASH_WIDTH
#guard poseidon2HashDesc.piCount == 3
#guard poseidon2HashDesc.constraints.length == 4
#guard (chipLookupTuple [.var IN0, .var IN1] DIGEST LANES).length == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms digest_forced

end Dregg2.Circuit.Emit.Poseidon2HashEmit
