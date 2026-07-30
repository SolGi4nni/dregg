/-
# EmitKimchiIncNonce — the ROUTE-B artifact emitter.

Prints `KimchiEffectIncNonce.emitJson`: the Kimchi sub-gate program the Lean lowering produced for
the `incrementNonceA` EffectVM row, plus the column map and the proved row count.

The o1js consumer (`bridge/mina-zkapp/src/DreggIncNonceNative.ts`) TRANSCRIBES this array into
`Gates.generic` calls and contains no dregg semantics of its own — which is what keeps route B
inside the Lean-authored-AIR law.

SCRATCH executable: `lake env lean --run EmitKimchiIncNonce.lean`.
-/
import Dregg2.Circuit.Emit.KimchiEffectIncNonce

def main : IO Unit :=
  IO.println Dregg2.Circuit.Emit.KimchiEffectIncNonce.emitJson
