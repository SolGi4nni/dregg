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
        → ONE `VmConstraint2.lookup` on `TID_P2_NARROW` (arity-2 absorb `[IN0,IN1]`, out0 = `DIGEST`,
          NO lane columns) — the chip AIR binds `out0` to the genuine permutation
          (`descriptor_ir2.rs:2525`) and the narrow bus is served by the SAME chip rows
          (`descriptor_ir2.rs::narrow_hist`), so a forged digest names no serving chip row → UNSAT.
          E7 narrowing (`ChipNarrowLookup.lean`): the 7 exposed permutation lanes never entered the
          soundness conclusion, so dropping them is byte-changing but soundness-preserving.
  * `Poseidon2Air.boundary_constraints` (row-0 input pinned to input PIs, output pinned to output PIs)
        → three `VmConstraint2.base (.piBinding VmRow.first · ·)` pins: `IN0→PI0`, `IN1→PI1`, `DIGEST→PI2`.

The chip table (`TID_P2_NARROW`) is Presence-detected from the lookup, so `tables` is empty (as
`node8`/`deco` / `MerkleMembershipEmit` leave it).

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + one genuinely-proven, load-bearing
semantic lemma (`digest_forced`), the hash-binding lever `chip_lookup_sound` instantiated at this exact
lookup. `#assert_axioms digest_forced ⊆ {propext, Classical.choice, Quot.sound}` (actually `{propext,
Quot.sound}`). NEW file; imports read-only.
-/
import Dregg2.Circuit.ChipNarrowLookup

namespace Dregg2.Circuit.Emit.Poseidon2HashEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTupleNarrow poseidon2narrow
   CHIP_RATE CHIP_OUT_LANES Table ChipTableSound emitVmJson2)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable chip_lookup_narrow_sound_of_wide_table)

set_option autoImplicit false

/-! ## §1 — The trace column layout (a single logical row; arity-2 absorb). -/

/-- Preimage element 0 (the hash's left input). -/
def IN0 : Nat := 0
/-- Preimage element 1 (the hash's right input). -/
def IN1 : Nat := 1
/-- The digest = `hash_2_to_1(IN0, IN1)` (chip lookup out0). -/
def DIGEST : Nat := 2

/-- Total main-trace width: 3 base columns (2 preimage + digest). The 7 exposed permutation lane
columns the WIDE `TID_P2` tuple carried are GONE (E7 narrowing) — they were referenced only at lane
positions 18..24 of the 25-wide tuple and entered no soundness conclusion. -/
def HASH_WIDTH : Nat := 3

/-! ## §2 — The constraint list (one child→digest chip lookup · three boundary pins). -/

/-- The `preimage → digest` step: an arity-2 NARROW `Poseidon2Chip` lookup absorbing `[IN0, IN1]`,
binding out0 to `DIGEST` (the `hash_2_to_1` shape) on the 18-wide `poseidon2narrow` bus
(= `TID_P2_NARROW`), served by the SAME chip rows as the wide bus. -/
def hashLookup : VmConstraint2 :=
  .lookup ⟨poseidon2narrow, chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST⟩

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

THE EQUALITY-GATE ANCHOR: this exact string is committed at
`circuit/descriptors/by-name/poseidon2-hash-arity2.json`, included by Rust, decoded via
`parse_vm_descriptor2`, and proven. A drift breaks THIS `#guard` or the artifact parity test. -/

#guard emitVmJson2 poseidon2HashDesc ==
  "{\"name\":\"poseidon2-hash-arity2::poseidon2-v1\",\"ir\":2,\"trace_width\":3,\"public_input_count\":3,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":8,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":2}]},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":0,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":1,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — A genuinely-proven, load-bearing semantic lemma (the hash-binding teeth).

Against a SOUND chip table, the emitted arity-2 lookup FORCES the digest column to carry the genuine
hash of the two preimage columns — the exact family lever ~15 hash-carrying descriptors depend on
(`chip_lookup_sound`, `DescriptorIR2.lean:1159`), instantiated at THIS lookup. This is the Lean face of
the chip AIR's `out0 == permute(seed)[0]` binding the Rust gate exercises end-to-end. -/
theorem digest_forced (hash : List ℤ → ℤ) (tbl : Table) (hSound : ChipTableSound hash tbl)
    (a : Assignment)
    (hmem : (chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval a) ∈ narrowTable tbl) :
    a DIGEST = hash [a IN0, a IN1] := by
  have h := chip_lookup_narrow_sound_of_wide_table hash tbl hSound a [.var IN0, .var IN1] DIGEST
    (by simp [CHIP_RATE]) hmem
  simpa [EmittedExpr.eval] using h

-- Non-vacuity of the emitted tuple — the digest + preimage columns are LOAD-BEARING (a forged
-- digest / preimage is a DIFFERENT lookup tuple → an unserved chip row), and columns the tuple does
-- NOT read cannot perturb it (a genuine TRUE-and-FALSE pair: the tuple reads EXACTLY IN0/IN1/DIGEST).
#guard decide
  ((chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = DIGEST then (7 : ℤ) else 0))
    ≠ (chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = DIGEST then (8 : ℤ) else 0)))
#guard decide
  ((chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = IN0 then (7 : ℤ) else 0))
    ≠ (chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = IN0 then (8 : ℤ) else 0)))
#guard decide
  ((chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = 50 then (7 : ℤ) else 0))
    = (chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).map (·.eval (fun i => if i = 50 then (8 : ℤ) else 0)))

-- Shape pins.
#guard poseidon2HashDesc.traceWidth == HASH_WIDTH
#guard poseidon2HashDesc.piCount == 3
#guard poseidon2HashDesc.constraints.length == 4
-- The narrow tuple is 18-wide (arity + CHIP_RATE + out0) — exactly CHIP_OUT_LANES - 1 = 7 shorter
-- than the wide 25-wide chip tuple, and the descriptor is 7 main columns narrower for the same
-- forced digest equation.
#guard (chipLookupTupleNarrow [.var IN0, .var IN1] DIGEST).length == CHIP_RATE + 1 + 1
#guard HASH_WIDTH + (CHIP_OUT_LANES - 1) == 10
#guard poseidon2narrow.wireId == 8

#assert_axioms digest_forced

end Dregg2.Circuit.Emit.Poseidon2HashEmit
