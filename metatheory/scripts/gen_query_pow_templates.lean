/-
Generator for the QueryPow range/PoW templates consumed by the Go emit-path
replayer (chain/gnark/emitted_verifier_full.go, block 0 canonicity + block 4
`SampleBitsDecomposed` / `AssertPowBitsZero` -> queryPowReplay ->
ReplayTemplateWithWitness).

It renders the Lean-authored, ∀-refined `emitQueryPow n` (QueryPowEmit.lean --
`queryPow_refines n hn v : gHolds (emitQueryPow n) (powAsg v) ↔ v.val < 2^31 ∧
v.val % 2^n = 0`, and its hypothesis-free MultiField twin `queryPow_refines_native`)
through the proof-covered `emitGnarkJson` renderer to the committed template grammar
the generic replayer reads:

  * n = 0  -> emitted/query_pow_n0.json  : a bare 31-bit ToBinary range check
             (`queryPow_refines 0`: `gHolds ↔ v.val < 2^31`, since `v.val % 1 = 0`).
             Block 0 canonicity replays it TWICE (on v and on p-1-v -- the two
             31-bit range checks `AssertIsCanonical` is), and block 4's
             `SampleBitsDecomposed` query-index range check replays it once.
  * n = 16 -> emitted/query_pow_n16.json : the deployed query-grinding template
             (`deployedPowBits = 16`, ir2 `query_proof_of_work_bits`): the 31-bit
             range decomposition + the low-16 zero-pins. Block 4's
             `AssertPowBitsZero` replays it.

The single input (public var 0) is the checked value; vars 1..31 are the 31 ToBinary
decomposition bits -- the free internal witnesses the Go replayer supplies from a
values-only bit hint, pinned by the template's booleanity + recomposition (a wrong
fill is UNSAT, so the hint touches completeness, never soundness).

This is NOT part of `lake build` (it lives under scripts/, outside the globbed libs).
Regenerate with, from the metatheory/ directory:

    lake env lean --run scripts/gen_query_pow_templates.lean
-/
import Dregg2.Circuit.Emit.GnarkVerifier.QueryPowEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

open Dregg2.Circuit.Emit.GnarkVerifier

def emitOne (n : Nat) : IO Unit := do
  let json := emitGnarkJson (emitQueryPow n)
  let path := s!"../chain/gnark/emitted/query_pow_n{n}.json"
  IO.FS.writeFile path json
  IO.println s!"query_pow_n{n}: wrote {json.length} bytes to {path}"

def main : IO Unit := do
  emitOne 0
  emitOne deployedPowBits
