/-
# EmitSeamSpecs — the byte source for `circuit/descriptors/seams/`.

Prints one `<filename>\t<json>` line per emitted seam artifact plus the port census, so the seam
JSONs the Rust fold functions `include_str!` are REGENERABLE from the verified Lean objects — the
same snapshot→emit→diff posture the descriptors get from `EmitByName.lean`.

    lake env lean --run EmitSeamSpecs.lean            # print all rows
    lake exe emit_seam_specs                          # same, compiled

Install (from `metatheory/`):

    lake env lean --run EmitSeamSpecs.lean | while IFS=$'\t' read -r f j; do
      printf '%s' "$j" > "../circuit/descriptors/seams/$f"
    done

Law #1: the seams are AUTHORED and PROVED in `Dregg2.Circuit.Emit.MinaSeams` (S1 naming the
published slots, S2 the refutable composition); this file only SERIALIZES them. Rust reads
(`circuit-prove/src/seam.rs`); Rust authors nothing.

⚑ The gate on these bytes is `circuit-prove/tests/seam_specs.rs`: it re-validates every artifact
against the layouts the deployed readers use AND recomputes each end's fingerprint lanes from the
descriptor it names. A drifted artifact is a named red there; a drifted Lean object is a failed
`rfl`/`decide` in `MinaSeams`.
-/
import Dregg2.Circuit.Emit.MinaSeams

open Dregg2.Circuit.Emit.Seam
open Dregg2.Circuit.Emit.MinaSeams

def rows : List (String × String) :=
  [ ("seam-xi-endo-to-conjunction.json", xiSeam.toJson)
  , ("seam-chain-vprime-to-finalize.json", vPrimeSeam.toJson)
  , ("seam-chain-fresh-sponge.json", freshSpongeSeam.toJson)
  , ("seam-head-tip-to-link.json", headTipSeam.toJson)
  -- ⚠ `ports.json` carries only the SEAM-covered ports: `seam_specs.rs`'s gate 3 demands a
  -- registered `SeamSpec` cover every row, which is what makes the file a hard invariant. The
  -- head's two digest-shaped commitment ports (weld-covered, REFUSAL 4/15) and the link's two
  -- UNCOVERED body ports are censused in Lean (`the_head_commitment_ports_are_weld_covered`,
  -- `the_link_body_ports_have_no_registered_cover`) — putting an uncoverable row here would
  -- either red the gate permanently or force the gate to accept weld strings it cannot check.
  , ("ports.json",
      "[" ++ portSetJson "dregg-mina-wrap-conjunction::v1"
              Dregg2.Circuit.Emit.MinaWrapConjunctionAir.CJ_PI_COUNT
              conjunctionPortedAir.ports
              [xiSeam.name]
      ++ "," ++ portSetJson "dregg-mina-lightclient-verify::v1"
              HEAD_CLAIM_LEN
              [anchorPort, tipPort]
              [headTipSeam.name] ++ "]")
  ]

def main : IO Unit := do
  for (f, j) in rows do
    IO.println s!"{f}\t{j}"
