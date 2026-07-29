/-
SCRATCH executable: emit the CHALLENGE VECTOR that `EmitPastaDerive.lean`'s descriptors are built
against, as JSON decimal strings.

  lake env lean --run EmitPastaDeriveChals.lean [<block>]
      > ../circuit/tests/fixtures/pasta-sg-derive/chals-block<block>.json

⚑ WHY THIS IS A SEPARATE ARTIFACT AND NOT A CONSTANT IN THE RUST TEST. The 15 IPA challenges are
NOT in the descriptor: `PastaMsmScalarDerive.chalPinGates` binds them to PUBLIC INPUT slots
`29..163`, so the party that supplies them is the VERIFIER, not the prover and not the emitter.
The Rust harness therefore needs them as data — and a hand-transcribed copy of a 255-bit field
element is exactly the kind of thing that silently drifts.

⚑ AND THE COPY IS CHECKED, not trusted: `pasta_derive_prove.rs::manifest_digits_are_the_derived_
s_vector` recomputes `s_i = ∏_j c_j^{bit_j(i)}` from THIS file's output and compares it against
the DESCRIPTOR's own manifest digit column, row by row. A challenge vector that did not produce
that manifest fails there before any proof is attempted.

This file imports `MinaWrapOpeningGate` (through `PastaMsmScalarBound`) but NOT `MinaWrapSrsG`, so
it elaborates in seconds rather than in a minute.
-/
import Dregg2.Circuit.Emit.PastaMsmScalarDerive

open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq CHAL_F)
open Dregg2.Circuit.Emit.PastaMsmScalarBound (sNat)

/-- Block `0` is the REAL block's 15 IPA challenges; block `1` is A DIFFERENT BLOCK — the same
vector with one round's challenge bumped. Byte-identical to `EmitPastaDerive.lean`'s `CHALS`. -/
def CHALS (block : Nat) : List Fq :=
  if block == 0 then CHAL_F else CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)

#guard (CHALS 0).length == 15
#guard (CHALS 1).length == 15
#guard sNat (CHALS 0) 1 != sNat (CHALS 1) 1

def main (args : List String) : IO Unit := do
  let block := (args[0]?).bind String.toNat? |>.getD 0
  let cs    := CHALS block
  let body  := String.intercalate "," (cs.map (fun c => "\"" ++ toString c.val ++ "\""))
  IO.println ("{\"block\":" ++ toString block ++ ",\"challenges\":[" ++ body ++ "]}")
