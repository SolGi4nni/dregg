/-
# EmitKimchiPoseidon2 — the Poseidon2-w16 artifact emitter.

Prints `KimchiPoseidon2.emitJson`: the Kimchi instruction stream the Lean generator produced for the
deployed BabyBear Poseidon2-w16 permutation, plus the input/output variable indices, the tracked
output bounds, and the generator's own witness at the KAT input.

The o1js consumer (`bridge/mina-zkapp/src/Poseidon2Native.ts`) TRANSCRIBES that stream into
`Gates.generic` / `Gates.rangeCheck0` calls and contains no Poseidon2 of its own — not a round
constant, not the diagonal, not the round structure. That is what keeps the permutation inside the
Lean-authored-AIR law instead of being a second implementation that happens to agree on two vectors.

⚑ ONE EMISSION SERVES EVERY INPUT. `emitPerm` takes a concrete input because it generates a WITNESS
alongside the circuit, but every emitted instruction carries variable indices and coefficients only:
allocation order comes from the round structure, `qLimbCount` from tracked BOUNDS, `bbAddSigned`'s
compensation from `pCeil` of a bound. None of them reads a value.

SCRATCH executable, the same shape as `EmitKimchiIncNonce.lean`:

    lake env lean --run EmitKimchiPoseidon2.lean \
      > ../bridge/mina-zkapp/src/generated/kimchi-poseidon2-w16.json
-/
import Dregg2.Circuit.Emit.KimchiPoseidon2

def main : IO Unit :=
  IO.println Dregg2.Circuit.Emit.KimchiPoseidon2.emitJson
