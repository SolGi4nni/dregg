/-
# `MinaBodyBitsEmit` — the ONE witness row of `dregg-mina-body-preimage-bits::v1`.

`Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` authors the AIR and proves both polarities on its
`bodyBitsRowOk` predicate; this driver renders the row that Lean already computed
(`MinaBodyPreimageBitsAir.realRow`, the real devnet block 540221's packed preimage) so the deployed
prover can be handed the SAME object rather than a Rust re-derivation of it.

⚠ **Rust does not decode a Mina protocol state.** The 2 381 bits are `Body.to_input`'s packed half
and the 302 limbs are the eleven packed field elements' base-256 digits; both come out of the Lean
binprot parse. A Rust-side reconstruction would be a twin, and this is the census's own answer to
that: emit the object, do not re-author it.

    cd metatheory
    lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures

writes `mina-body-preimage-bits-row.txt` — ONE line, 2 683 space-separated decimals, columns in
descriptor order (`BIT 0..2380` then `PLIMB` in publication order). The PI vector is the last 302
entries, so nothing else needs emitting.
-/
import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

open Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

def main (args : List String) : IO Unit := do
  let dir := args.getD 0 "../circuit/tests/fixtures"
  let cells := (List.range BODY_BITS_WIDTH).map (fun c => toString (realRow c))
  let line := String.intercalate " " cells
  let path := System.FilePath.mk dir / "mina-body-preimage-bits-row.txt"
  IO.FS.writeFile path (line ++ "\n")
  IO.println s!"wrote {path} — {BODY_BITS_WIDTH} cells ({NBITS} bits + {NLIMB} limbs)"
