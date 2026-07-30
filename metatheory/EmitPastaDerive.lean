/-
SCRATCH executable: emit ONE **scalar-DERIVED**, curve-gated, contents-bound sliced Pasta RCB
descriptor as IR-v2 JSON, over the REAL Mina devnet Wrap SRS generators and the REAL 15 IPA
challenges the block's own Fq sponge produces.

  lake env lean --run EmitPastaDerive.lean <n> <k> <w> <planes> [<block>]
      > ../circuit/tests/fixtures/pasta-sg-derive/pasta-rcb-sg-derive-<k>-of-<n>.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmScalarDerive.deriveRowDesc 15 n k w planes
MinaWrapSrsG.SRS_G (SCAL …)` — `PastaMsmOnCurve.onCurveRowDesc`'s 98 constraints verbatim
(`deriveRowDesc_extends_onCurve` proves the prefix in the kernel), plus the `8 + 29·nb + 2·planes`
constraints that RECOMPUTE `s_GIDX = ∏_j c_j^{bit_j(GIDX)}` from the challenge vector ON THE WIRE,
decompose it into `planes` binary digits, and pin the row's conditional-add bit to the digit its
own bit-plane names. This file only RENDERS it; it authors nothing.

⚑ **THE CHALLENGES ARE NOT IN THE DESCRIPTOR.** They are `9·15 = 135` PUBLIC INPUTS (slots
`29..163`), pinned on row 0 by `chalPinGates` and threaded down by `chalThreadGates`. That is what
makes the fourth tamper possible at all: the verifier supplies the challenge vector, so a trace
that is internally consistent with a DIFFERENT block's challenges is refused by the wire.

⚠ SAME REASON AS `EmitPastaOnCurve.lean` FOR NOT BEING IN `EmitByName.lean`: it imports
`Dregg2.Circuit.Emit.MinaWrapSrsG` (32,768 pinned points), allowlisted out of the `Dregg2` root by
`scripts/lean-orphans-allow.txt`. The emitted artifacts are sha256-pinned in
`circuit/tests/pasta_derive_prove.rs` instead, which is the check that actually reads them.

⚠ THE GEOMETRY IS NOT FREE, and it is `EmitPastaBoundScaled.lean`'s: the trace height is
`planes * (w + 1)` and `prove_vm_descriptors2_batch` REFUSES a non-power-of-two height, so `w + 1`
and `planes` are both powers of two and `w = 2^m − 1`. `planes` must also cover the s-vector's bit
width, and an s-vector entry is an element of the Pallas SCALAR field, so `planes = 256` is the
first admissible value (`PastaMsmScalarBound.block_s_fits_255`). That fixes the deployed derived
shape at 256 planes and `w ∈ {1, 3, 7, …}`.

⚠ SLICES ARE CHOSEN, NOT TILED. `sliceLo w k = w·k`, and a slice at a SMALL `lo` only ever carries
generator indices with a few low bits set — under which the 10 high challenges are selected OUT on
every row and their `b = 1` arm is never exercised. The four slices the regen script emits are
spread across the SRS exactly so every one of the 15 challenges is selected on some row.
-/
import Dregg2.Circuit.Emit.PastaMsmScalarDerive
import Dregg2.Circuit.Emit.MinaWrapSrsG

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmScalarDerive (deriveRowDesc WD PID)
open Dregg2.Circuit.Emit.PastaMsmScalarBound (sNat)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq CHAL_F)
open Dregg2.Circuit.Emit.PastaMsmSliced (sliceLo)

/-- Block `0` is the REAL block's 15 IPA challenges (`MinaWrapOpeningGate.CHAL_F`, which
`derived_ipa_challenges` lifts from the block's own Fq sponge). Block `1` is A DIFFERENT BLOCK: the
same vector with one round's challenge bumped — the exact perturbation `PastaMsmScalarBound` §5
uses to show the s-vector moves. -/
def CHALS (block : Nat) : List Fq :=
  if block == 0 then CHAL_F else CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)

/-- The manifest's scalar column for THIS slice: the block's OWN s-vector at the `w` absolute
indices the slice consumes. `genManifest` reads it only at `[lo, lo + w)`, so the entries below
`lo` are never looked at and are left zero rather than materialised — `sAt` is `|cs|`
multiplications per entry and a 32,768-entry list is exactly what `PastaMsmScalarBound` exists to
avoid computing. -/
def SCAL (cs : List Fq) (lo w : Nat) : List Nat :=
  List.replicate lo 0 ++ (List.range w).map (fun t => sNat cs (lo + t))

-- ⚑ THE DEPLOYED DERIVED SHAPE, as an object, checked in the kernel before anything is rendered.
-- The canonicity certificate (`PastaMsmScalarDerive` §2.7) is `CBITS = 255` more columns and
-- `CBITS + 1 = 256` more constraints than the shape `9b88bc06e` proved: 1876 → 2131, 1053 → 1309.
#guard WD 15 256 == 2131
#guard PID 15 == 164
#guard 98 + (264 + 29 * 15 + 2 * 256) == 1309
#guard 256 * (3 + 1) == 1024
-- …and the challenge vector really is the block's 15.
#guard CHAL_F.length == 15
#guard (CHALS 1).length == 15
-- ⚑ The two blocks' s-vectors DISAGREE at an index slice 0 consumes, so the fourth tamper has
-- something to bite on. (Index 1 selects challenge 14, which is the one that moved.)
#guard sNat (CHALS 0) 1 != sNat (CHALS 1) 1

def main (args : List String) : IO Unit := do
  let n      := (args[0]?).bind String.toNat? |>.getD 10922
  let k      := (args[1]?).bind String.toNat? |>.getD 0
  let w      := (args[2]?).bind String.toNat? |>.getD 3
  let planes := (args[3]?).bind String.toNat? |>.getD 256
  let block  := (args[4]?).bind String.toNat? |>.getD 0
  let cs     := CHALS block
  IO.println (emitVmJson2
    (deriveRowDesc cs.length n k w planes Dregg2.Circuit.Emit.MinaWrapSrsG.SRS_G
      (SCAL cs (sliceLo w k) w)))
