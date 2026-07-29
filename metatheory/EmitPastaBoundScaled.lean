/-
SCRATCH executable: emit ONE **contents-bound** sliced Pasta RCB descriptor as IR-v2 JSON at an
ARBITRARY slice width and plane count, over the REAL Mina devnet Wrap SRS generators.

  lake env lean --run EmitPastaBoundScaled.lean <n> <k> <w> <planes>
      > pasta-rcb-sg-bound-<k>-of-<n>-w<w>-p<planes>.json

This is `EmitPastaBound.lean` with `w` and `planes` lifted out of the literals, and NOTHING else:
the descriptor is still `Dregg2.Circuit.Emit.PastaMsmBound.boundRowDesc n k w planes
MinaWrapSrsG.SRS_G (SCAL n w planes)`, the same Lean `def` whose 82 constraints and whose forcing
theorems are row-count-INDEPENDENT (`row_tuple_is_its_manifest_row` is pure membership plus
`manifest_key_unique`; `w`, `planes` and `i` occur in no bound). This file AUTHORS NOTHING — it
renders.

⚠ WHY IT EXISTS. The deployed exact-public tooth used to spend ONE batch AIR instance per manifest
ROW, capped at `MAX_EXACT_PUBLIC_ROWS = 128`; since the balance is a PERMUTATION (manifest rows =
trace rows) that capped a contents-bound trace at 128 rows, i.e. 31 generators per slice.
`Ir2Air::ExactPublicTable` (2026-07-29) realizes a manifest as ONE multiplicity-bearing instance,
so the ceiling moved and the question "how many of the 32,768 generators can be contents-bound"
became a MEASUREMENT. This emitter is what supplies the ladder.

⚠ THE GEOMETRY IS NOT FREE. The trace height is `planes * (w + 1)` and p3 needs a power of two, so
`w + 1` and `planes` are both powers of two and `w = 2^m - 1`. `n * w` is therefore never exactly
32,768: the best four-way cover is `4 * 8191 = 32,764`. That is a structural property of the
one-doubling-row-per-plane schedule, not of the realization.

⚠ THE SCALARS ARE SYNTHETIC, THE GENERATORS ARE NOT — exactly as in `EmitPastaBound.lean`. `SCAL`
is a reproducible `planes`-bit sequence, not the block's s-vector; binding that is a different rung
(`MinaWrapSgCore.SVEC`) and nothing here touches it.

⚠ NOT IN `EmitByName.lean`, and must not be: it imports `MinaWrapSrsG` (32,768 pinned points,
~48 s to elaborate), allowlisted out of the `Dregg2` root by `scripts/lean-orphans-allow.txt`.
-/
import Dregg2.Circuit.Emit.PastaMsmBound
import Dregg2.Circuit.Emit.MinaWrapSrsG

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmBound (boundRowDesc)

/-- The demonstration scalars, generalized: `n * w` values of `planes` bits, reproducible, no
randomness in a build artifact. At `n=4, w=31, planes=4` this is `EmitPastaBound.lean`'s `SCAL`. -/
def SCAL (n w planes : Nat) : List Nat :=
  (List.range (n * w)).map (fun i => (7 + 13 * i) % 2 ^ planes)

def main (args : List String) : IO Unit := do
  let n      := (args[0]?).bind String.toNat? |>.getD 4
  let k      := (args[1]?).bind String.toNat? |>.getD 0
  let w      := (args[2]?).bind String.toNat? |>.getD 31
  let planes := (args[3]?).bind String.toNat? |>.getD 4
  IO.println (emitVmJson2
    (boundRowDesc n k w planes Dregg2.Circuit.Emit.MinaWrapSrsG.SRS_G (SCAL n w planes)))
