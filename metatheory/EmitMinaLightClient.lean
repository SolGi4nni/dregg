/-
# EmitMinaLightClient — the byte source for the Mina light client's two descriptors.

`EmitByName.lean` remains the CANONICAL route for `circuit/descriptors/by-name/`, and these two
files are rows of its table. This emitter exists because that table's import closure is a superset
of this one: on 2026-08-05 `Dregg2/Circuit/Emit/BlindedMembershipEmit.lean` and
`Dregg2/Circuit/Emit/NoteSpendingLeafEmit.lean` were RED at HEAD (`VmRowEnv` gained a fourth,
defaulted `chal` field with the challenge leaf, and positional `⟨loc, nxt, pub⟩` constructions —
all of them inside `#guard`s — do not take a default), so `lake env lean --run EmitByName.lean`
could not run at all and the whole by-name surface was unemittable by anyone. Those are other
lanes' modules and this lane does not edit them.

The BYTES are identical either way: both emitters print `emitVmJson2` of the same descriptor
objects, and `EmitByName.lean`'s rows for these two files name exactly these definitions.

    lake env lean --run EmitMinaLightClient.lean verify > ../circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json
    lake env lean --run EmitMinaLightClient.lean link   > ../circuit/descriptors/by-name/dregg-mina-lightclient-link-v1.json

⚑ `verify` is the descriptor that changed on 2026-08-05: `PICKLES_OK` is gone, replaced by
`PICKLES_WITNESSED` (the residue, honestly named) plus `WRAP_FS_PROVED` and its **nine `proof_bind`
constraints** pinning the row's attested program to the semantic fingerprint of
`dregg-pasta-fq-wraplink::v1`, lane by lane. Width 30 → 49, PIs 20 → 29, constraints 50 → 69.
`link` is emitted here unchanged, so the pair can be regenerated together.
-/
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)

def main (args : List String) : IO Unit := do
  match args with
  | ["verify"] =>
      IO.println (emitVmJson2 Dregg2.Circuit.Emit.LightClientMinaAir.minaLcVerifyDesc)
  | ["link"] =>
      IO.println (emitVmJson2 Dregg2.Circuit.Emit.LightClientMinaLinkAir.minaLinkDesc)
  | _ =>
      IO.eprintln "usage: EmitMinaLightClient.lean (verify|link)"
      IO.Process.exit 2
