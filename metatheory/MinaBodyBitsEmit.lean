/-
# `MinaBodyBitsEmit` — the ONE witness row of `dregg-mina-body-preimage-bits::v1`, **and its claim**.

`Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir` authors the AIR and proves both polarities on its
`bodyBitsRowOk` predicate; this driver renders the row that Lean already computed
(`MinaBodyPreimageBitsAir.realRow`, the real devnet block 540221's packed preimage) so the deployed
prover can be handed the SAME object rather than a Rust re-derivation of it.

⚠ **Rust does not decode a Mina protocol state.** The 2 381 bits are `Body.to_input`'s packed half,
the 302 limbs are the eleven packed field elements' base-256 digits, and the 1 216 further limbs are
the 38 whole field elements'; all of it comes out of the Lean binprot parse. A Rust-side
reconstruction would be a twin, and this is the census's own answer to that: emit the object, do not
re-author it.

    cd metatheory
    lake env lean --run MinaBodyBitsEmit.lean ../circuit/tests/fixtures

## ⚑ TWO FILES SINCE 2026-08-10, AND THE SECOND ONE IS NOT A CONVENIENCE

* `mina-body-preimage-bits-row.txt` — ONE line, **3 899** decimals in COLUMN order
  (`BIT 0..2380`, then `PLIMB` in publication order, then `FLIMB`).
* `mina-body-preimage-bits-pis.txt` — ONE line, **1 518** decimals in CLAIM order, straight from
  `realPub`.

⚠ **The claim is no longer a suffix of the row, and a reader that slices one out of the other is
re-authoring the layout.** The 2026-08-09 flag day put the PI vector in ABSORB order — `[0, 1216)`
the 38 whole field elements, `[1216, 1518)` the packed ones — while the ROW keeps the packed limbs
BELOW the whole-field ones. So the claim is `row[2683..3899] ++ row[2381..2683]`, a REORDERING, and
the old docstring's *"the PI vector is the last 302 entries"* now names field element 38's limbs.
Emitting `realPub` directly means the consumer never has to know that, and the two files agree by
`MinaBodyPreimageBitsAir.the_honest_claim_is_the_honest_row` rather than by a Rust slice.
-/
import Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

open Dregg2.Circuit.Emit.MinaBodyPreimageBitsAir

def main (args : List String) : IO Unit := do
  let dir := args.getD 0 "../circuit/tests/fixtures"
  let cells := (List.range BODY_BITS_WIDTH).map (fun c => toString (realRow c))
  let rowPath := System.FilePath.mk dir / "mina-body-preimage-bits-row.txt"
  IO.FS.writeFile rowPath (String.intercalate " " cells ++ "\n")
  IO.println s!"wrote {rowPath} — {BODY_BITS_WIDTH} cells \
    ({NBITS} bits + {NLIMB} packed limbs + {NFLIMB} field limbs)"
  let pis := (List.range BODY_BITS_PI_COUNT).map (fun s => toString (realPub s))
  let piPath := System.FilePath.mk dir / "mina-body-preimage-bits-pis.txt"
  IO.FS.writeFile piPath (String.intercalate " " pis ++ "\n")
  IO.println s!"wrote {piPath} — {BODY_BITS_PI_COUNT} claim slots in ABSORB order"
