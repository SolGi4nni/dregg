/-
# EmitWideRegistryProbe — ADDITIVE full wide-registry descriptor emit (STAGED slice 2).

Prints ONE TSV line per WIDE member, in the EXACT order + key set of the live `V3_STAGED_REGISTRY_TSV`
(`EmitRotationV3.lean`), so the wide registry is a member-for-member, name-stable COVER of the live V3
registry (57 members):

  `<live key>\t<member.name>\t<emitVmJson2 (wide member)>`

Each wide member is the proven `wideAppend host bb (bb+91)` of the corresponding live descriptor — the
two 13×8 BEFORE/AFTER carriers + the 16 wide commit PIs (the 8-felt ~124-bit before/after anchors)
appended past the host, NO narrowing. The emit order is the live order:

  * positions 0..44 — `v3RegistryCapOpenWide` (the 45 emit-source members, §9);
  * position 45 — `transferCapOpenTBVmDescriptor2R24` (the turn-identity-pinned transfer cap-open),
                  wide-wrapped at its transfer FACE base;
  * position 46 — `heapWriteVmDescriptor2R24` (the Class-A sorted-Merkle splice), wide-wrapped at its
                  heap-splice FACE base;
  * positions 47..55 — the WRITE-bearing cap-open tail (`v3RegistryCapOpenWriteWide`, §10) MINUS
                  `grantCapWriteCapOpen` (NOT a live `V3_STAGED_REGISTRY_TSV` member — reconciled out);
  * position 56 — `supplyMintVmDescriptor2R24` (the dedicated `sel.MINT` mint), wide-wrapped at its
                  mint FACE base.

This is the byte source of the ADDITIVE Rust artifact `circuit/descriptors/rotation-wide-registry-
staged.tsv` the per-family wide-roundtrip slice consumes — NOTHING on the live 1-felt wire path changes
(`v3RegistryCapOpen` / the live TSV / FP / VK are UNTOUCHED). The wide transfer single-line TSV
(`EmitWideTransferProbe.lean`) stays beside this, byte-identical (row 0).

SCRATCH executable: `lake env lean --run EmitWideRegistryProbe.lean`.
-/
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.CapOpenTurnPins
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.HeapOpenEmit
import Dregg2.Circuit.RotatedKernelRefinementExercise

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide v3RegistryCapOpenWriteWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend)

def main : IO Unit := do
  -- positions 0..44: the 45 emit-source wide members (`v3RegistryCapOpenWide`), keyed by the live
  -- registry key (`burnVmDescriptor2R24` etc., `#guard`-proven name-stable with `v3RegistryCapOpen`).
  for (key, d) in v3RegistryCapOpenWide do
    IO.println s!"{key}\t{d.name}\t{emitVmJson2 d}"
  -- position 45: `transferCapOpenTB` made 8-felt-wide. The host is the SAME `effCapOpenV3TB transferV3
  -- … EFF_TRANSFER` the live `EmitRotationV3.lean` emits (the +2 turn-identity columns / +3 PI pins);
  -- the BEFORE limbs are laid by `rotateV3 transferV3` at the transfer FACE width, so `bb =
  -- transferVmDescriptor.traceWidth` (the SAME base as `transferCapOpenEff`, position 42).
  let tbBB := Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth
  let tbHost := Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB
    Dregg2.Circuit.Emit.CapOpenEmit.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff-tb" Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER
  let tbWide := wideAppend tbHost tbBB (tbBB + 91)
  IO.println s!"transferCapOpenTBVmDescriptor2R24\t{tbWide.name}\t{emitVmJson2 tbWide}"
  -- position 46: `heapWrite` (the after-spine membership-forcing heap-write descriptor, OPTION I) made
  -- 8-felt-wide — EXACTLY as cap deploys `effCapOpenWriteV3`. The host is `effHeapWriteV3 heapWriteV3
  -- …-write-heapopen`: the Class-A splice base (`heapWriteV3` = graduated+rotated splice + the splice
  -- `MapOp`) WIDENED by the heap-open READ appendix + the AFTER-spine membership appendix, so the
  -- DEPLOYED descriptor's `Satisfied2` FORCES the faithful 8-felt heap-write over the full ~124-bit
  -- BEFORE/AFTER root blocks (`HeapOpenEmit.effHeapWriteV3_forces_write8`) — never the lane-0 squeeze the
  -- map_op-only path would leave. `rotateV3` lays the BEFORE limbs at the splice FACE width, so `bb =
  -- heapWriteSpliceVmDescriptor.traceWidth (= EFFECT_VM_WIDTH)`, aligning the after-spine's committed
  -- heap-root blocks (`heapRootGroupCol (EFFECT_VM_WIDTH + 91)`) with the wide AFTER rotated carrier.
  let hwBB := Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor.traceWidth
  let hwHost := Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
    Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
    "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen"
  let hwWide := wideAppend hwHost hwBB (hwBB + 91)
  IO.println s!"heapWriteVmDescriptor2R24\t{hwWide.name}\t{emitVmJson2 hwWide}"
  -- positions 47..55: the WRITE-bearing cap-open tail (`v3RegistryCapOpenWriteWide`, §10) made
  -- 8-felt-wide, in its own order, EXCEPT `grantCapWriteCapOpen` — which is NOT a member of the live
  -- `V3_STAGED_REGISTRY_TSV`, so it is reconciled OUT to keep the wide registry a member-for-member
  -- cover of live. The remaining 9 land exactly at live positions 47..55.
  for (key, d) in v3RegistryCapOpenWriteWide do
    if key != "grantCapWriteCapOpenVmDescriptor2R24" then
      IO.println s!"{key}\t{d.name}\t{emitVmJson2 d}"
  -- position 56: `supplyMint` (the dedicated `sel.MINT` mint) made 8-felt-wide. `supplyMintV3 =
  -- withSelectorGate sel.MINT (v3OfFrozen mintTickFace)`; the BEFORE limbs are laid at the mint FACE
  -- width, so `bb = mintTickFace.traceWidth` (the SAME base as the cohort `mint` member, position 2).
  let smBB := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintTickFace.traceWidth
  let smWide := wideAppend Dregg2.Circuit.Emit.EffectVmEmitRotationV3.supplyMintV3 smBB (smBB + 91)
  IO.println s!"supplyMintVmDescriptor2R24\t{smWide.name}\t{emitVmJson2 smWide}"
