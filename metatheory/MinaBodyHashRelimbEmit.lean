/-
# `MinaBodyHashRelimbEmit` — the ONE witness row of `dregg-mina-bodyhash-relimb::v1`, and its claim.

`Dregg2.Circuit.Emit.MinaBodyHashRelimbAir` authors the AIR and proves both polarities on its
`relimbRowOk` predicate; this driver renders the row Lean already computes
(`rowOfValue realBodyHash` — the real devnet block 540221's own `state_body_hash`) so the deployed
prover is handed the SAME object rather than a Rust re-derivation of it.

⚠ **Rust does not derive a `state_body_hash`.** The value is the terminal squeeze of the 25-link
body-hash chain (`MinaStateBodyHashChain.the_body_chain_ends_on_the_state_body_hash`), out of the
Lean binprot parse and the Lean Poseidon. A Rust-side reconstruction would be a twin.

    cd metatheory
    lake env lean --run MinaBodyHashRelimbEmit.lean ../circuit/tests/fixtures

Two files:

* `mina-bodyhash-relimb-row.txt` — ONE line, **295** decimals in COLUMN order
  (`BIT 0..253`, then `BYTE 0..31`, then `LANE 0..8`).
* `mina-bodyhash-relimb-pis.txt` — ONE line, **41** decimals in CLAIM order (`pubOfValue`): the 32
  byte slots the chain seam welds, then the 9 lane slots the link seam welds.

⚠ The claim is NOT a suffix of the row: it is `row[254..286] ++ row[286..295]`, which happens to be
the row's tail in order today — and emitting `pubOfValue` directly means no consumer has to depend
on that continuing to be true.
-/
import Dregg2.Circuit.Emit.MinaBodyHashRelimbAir
import Dregg2.Circuit.Emit.MinaStateBodyHashChain

open Dregg2.Circuit.Emit.MinaBodyHashRelimbAir

/-- The devnet block's own `state_body_hash` — the value both spellings re-limb. -/
def theBodyHash : Nat := Dregg2.Circuit.Emit.MinaStateBodyHashChain.realBodyHash

def main (args : List String) : IO Unit := do
  let dir := args.getD 0 "../circuit/tests/fixtures"
  let cells := (List.range RELIMB_WIDTH).map (fun c => toString (rowOfValue theBodyHash c))
  let rowPath := System.FilePath.mk dir / "mina-bodyhash-relimb-row.txt"
  IO.FS.writeFile rowPath (String.intercalate " " cells ++ "\n")
  IO.println s!"wrote {rowPath} — {RELIMB_WIDTH} cells \
    ({NBIT} bits + {NBYTE} bytes + {NLANE} lanes)"
  let pis := (List.range RELIMB_PI_COUNT).map (fun s => toString (pubOfValue theBodyHash s))
  let piPath := System.FilePath.mk dir / "mina-bodyhash-relimb-pis.txt"
  IO.FS.writeFile piPath (String.intercalate " " pis ++ "\n")
  IO.println s!"wrote {piPath} — {RELIMB_PI_COUNT} claim slots (32 bytes, then 9 lanes)"
