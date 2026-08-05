/-
SCRATCH executable: emit the **BUCKETED** Pasta MSM descriptor as IR-v2 JSON, over REAL Mina Wrap
SRS generators.

  lake env lean --run EmitPastaBucketed.lean <n> <nbits> <c>
      > ../circuit/tests/fixtures/pasta-msm-bucketed/pasta-msm-bucketed-c<c>.json

The descriptor is `Dregg2.Circuit.Emit.PastaMsmBucketed.bucketedRowDesc n nbits c
MinaWrapSrsG.SRS_G SCAL` — `PastaMsmWindowed.windowedRowDesc`'s 45 constraints as a PREFIX (so the
RCB complete add is the same already-proved object), plus the mode pins, the operand selects, the
two accumulator threads, the sweep counter and THREE exact-public lookups whose manifests carry the
schedule, the `(window, generator, digit)` grid and the real generator limbs.

This file only RENDERS it; it authors nothing.

⚠ NOT IN `EmitByName.lean` AND MUST NOT BE, for the same reason `EmitPastaBound.lean` is not: it
imports `MinaWrapSrsG` (32,768 pinned points, ~32 s just to elaborate, allowlisted out of the
`Dregg2` root by `scripts/lean-orphans-allow.txt`). The emitted artifacts are sha256-pinned in
`circuit/tests/pasta_msm_bucketed_prove.rs` instead, which is the check that actually reads them.

⚠ THE SCALARS ARE SYNTHETIC, THE GENERATORS ARE NOT — identical status to `EmitPastaBound.lean`.
`SCAL` is a reproducible sequence, not a block's s-vector; binding the s-vector to the block's IPA
challenges is `PastaMsmScalarDerive`'s rung, and `PastaMsmBucketed` §7.3 states the weld.

Heights are chosen so `bucketedRows n nbits c` is a POWER OF TWO, because the deployed prover
refuses a non-power-of-two base trace and a permutation manifest's length IS the trace height:

    n = 27, nbits = 4, c = 2  ⇒  W = 2, winLen = 2 + 27 + 3  = 32,  rows = 64
    n = 54, nbits = 6, c = 3  ⇒  W = 2, winLen = 3 + 54 + 7  = 64,  rows = 128
-/
import Dregg2.Circuit.Emit.PastaMsmBucketed
import Dregg2.Circuit.Emit.MinaWrapSrsG
import Dregg2.Circuit.Emit.MinaStepSrsG

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.PastaMsmBucketed (bucketedRowDesc bucketedRowDescVesta)

/-- The demonstration scalars: reproducible, no randomness in a build artifact. ⚠ REDUCED BELOW
`2 ^ (c · W)` — a scalar wider than the windows cover would have its top bits silently dropped by
`scalarDigitC`, and the trace would then prove a DIFFERENT MSM than the one the caller meant. -/
def SCAL (n m : Nat) : List Nat := (List.range n).map (fun i => (7 + 13 * i) % m)

/-- ⚑ `--windowed` emits the INHERITED row template alongside, into this campaign's OWN fixture
directory. `circuit/descriptors/by-name/pasta-rcb-windowed.json` already exists and is the same
object — but a by-name artifact is a SHARED file on the descriptor-drift gate's hot path, and on
2026-08-05 a sibling lane's `challenges` wire field made every one of them refuse to load until
they are re-emitted. A test that compares its own prefix against a shared artifact inherits that
lane's flag days; owning the comparand is what `circuit/tests/fixtures/pasta-sg-bound/` does and
this follows it. -/
def main (args : List String) : IO Unit := do
  if args[0]? == some "--windowed" then
    IO.println (emitVmJson2 Dregg2.Circuit.Emit.PastaMsmWindowed.windowedRowDesc)
    return
  let n     := (args[0]?).bind String.toNat? |>.getD 27
  let nbits := (args[1]?).bind String.toNat? |>.getD 4
  let c     := (args[2]?).bind String.toNat? |>.getD 2
  let w     := Dregg2.Circuit.Emit.PastaMsmBucketed.windowsOf nbits c
  let scal  := SCAL n (2 ^ (c * w))
  -- ⚑ THE CURVE IS PART OF THE COMMAND, because it is part of the object. `vesta` takes the
  -- STEP/Tick generators (`MinaStepSrsG`, the 65,536 points `accumulator_check` runs against);
  -- anything else takes the WRAP/Tock ones. Emitting the wrong pair is a silent wrong-curve proof,
  -- so the generator list is chosen HERE, next to the gadget, and never defaulted.
  if args[3]? == some "vesta" then
    IO.println (emitVmJson2
      (bucketedRowDescVesta n nbits c Dregg2.Circuit.Emit.MinaStepSrsG.SRS_G scal))
  else
    IO.println (emitVmJson2
      (bucketedRowDesc n nbits c Dregg2.Circuit.Emit.MinaWrapSrsG.SRS_G scal))
