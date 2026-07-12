/-
# EmitWideRegistryProbe — ADDITIVE full wide-registry descriptor emit (STAGED slice 2).

Prints ONE TSV line per WIDE member, in the EXACT order + key set of the live `V3_STAGED_REGISTRY_TSV`
(`EmitRotationV3.lean`), so the wide registry is a member-for-member, name-stable COVER of the live V3
registry (57 members):

  `<live key>\t<member.name>\t<emitVmJson2 (wide member)>`

Each wide member is the proven `wideAppend host bb (bb+239)` of the corresponding live descriptor — the
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
import Dregg2.Circuit.Emit.FieldsOpenEmit
import Dregg2.Circuit.Emit.AccumulatorInsertEmit
import Dregg2.Circuit.Emit.CarrierComposed
import Dregg2.Circuit.Emit.AvailWideMembers
import Dregg2.Circuit.RotatedKernelRefinementExercise
-- THE GENTIAN DEPLOYED-DEFAULT FLIP: the capacity-floor refuse, lifted to ride the WIDE bare cohort
-- (aux blocks PAST the wide member width — past the two 13×8 wide carriers). Welded onto exactly the
-- 36 bare cohort members (the settle-as-transfer/burn dodge routes), mirroring the V3 `v3RegistryRefused
-- ++ drop 36`. See Dregg2.Deos.BareCohortFloorRefuseWide.declared_capacity_unsat_wide.
import Dregg2.Deos.BareCohortFloorRefuseWide

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2 EffectVmDescriptor2)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide v3RegistryCapOpenWriteWide)
open Dregg2.Circuit.Emit.EffectVmEmitRotationWide (wideAppend)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (withDfaRcPins)

/-- The 36 bare cohort keys (the settle-as-transfer/burn dodge routes) — the members the WIDE flag-day
refuse is welded onto, mirroring the V3 `v3RegistryRefused`. The cap-open tail / write / satisfaction /
supplyMint members are NOT bare routes and are left unwelded. -/
def bareCohortKeys : List String :=
  Dregg2.Circuit.Emit.EffectVmEmitRotationV3.v3RegistryBare.map (·.1)

/-- Weld the WIDE capacity-floor refuse onto a wide member IFF its key is a bare cohort route. A
non-cohort key (cap-open / write / supplyMint / satisfaction) is returned untouched. -/
def weldWide (key : String) (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  if bareCohortKeys.contains key then
    Dregg2.Deos.BareCohortFloorRefuseWide.gentianWideBareRefuse d
  else d

def main : IO Unit := do
  -- positions 0..44: the 45 emit-source wide members (`v3RegistryCapOpenWide`), keyed by the live
  -- registry key (`burnVmDescriptor2R24` etc., `#guard`-proven name-stable with `v3RegistryCapOpen`).
  -- OPTION I (fields): position 7 (`refusalVmDescriptor2R24`) is REPLACED IN PLACE by the after-spine
  -- membership-forcing `effFieldsWriteV3 refusalFieldsWriteV3 …` (EXACTLY as heap deploys `effHeapWriteV3`
  -- at position 46 and cap deploys `effCapOpenWriteV3`) — the DEPLOYED refusal descriptor's `Satisfied2`
  -- FORCES the faithful 8-felt fields-write over the full ~124-bit BEFORE/AFTER fields-root blocks
  -- (`FieldsOpenEmit.effFieldsWriteV3_forces_write8`), never the lane-0 squeeze the map_op-only host would
  -- leave. The wide member stays keyed `refusalVmDescriptor2R24` (member count UNCHANGED at 57); only the
  -- host (name + width) grows — the base `refusalFieldsWriteV3` (829) widened by the fields-open READ
  -- appendix (329) + the AFTER-spine appendix (143) → host 1301, wide 1669. `bb` is the refusal FACE width
  -- (`refusalVmDescriptor.traceWidth = EFFECT_VM_WIDTH = 188`), aligning the after-spine's committed
  -- fields-root blocks (`fieldsRootGroupCol (EFFECT_VM_WIDTH + 239)`) with the wide AFTER rotated carrier.
  for (key, d) in v3RegistryCapOpenWide do
    if key == "refusalVmDescriptor2R24" then
      -- rc-EMIT FIX: the welded host rides the uniform DSL rc wrap (`withDfaRcPins`, 4 additive
      -- tail pins — host PIs THEN rc THEN the 16 wide anchors), matching the live cohort member +
      -- the producer's PI layout (per-effect extras first, rc last-pre-wide). Without the wrap the
      -- emitted row dropped the 4 rc PIs the producer publishes (70 ≠ the live 74).
      let rfHost := withDfaRcPins (Dregg2.Circuit.Emit.FieldsOpenEmit.effFieldsWriteV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalFieldsWriteV3
        "dregg-effectvm-refusal-v1-rot24-v3-write-fieldsopen")
      let rfBB := Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor.traceWidth
      let rfWide := wideAppend rfHost rfBB (rfBB + 239)
      IO.println s!"{key}\t{(weldWide key rfWide).name}\t{emitVmJson2 (weldWide key rfWide)}"
    -- §J′ (INSERT-shaped accumulator deploy): positions 3/4/22 (noteSpend/noteCreate/createCell) are
    -- REPLACED IN PLACE by the insert-shaped `effAccumInsertV3 … base …` host (EXACTLY as refusal is
    -- advanced to `effFieldsWriteV3`, heap to `effHeapWriteV3`, cap to `effCapOpenWriteV3`). The DEPLOYED
    -- accumulator descriptor's `Satisfied2` TRACE-FORCES the spliced-leaf membership in the REBUILT AFTER
    -- tree over the full ~124-bit BEFORE/AFTER accumulator-root groups
    -- (`AccumulatorInsertEmit.effAccumInsertV3_forces_write8`), over the GENUINE sorted fresh-key insert
    -- (NOT the non-fitting update-at-key shape) — NEVER the lane-0 squeeze the map_op-only host leaves.
    -- The wide member stays keyed by its live registry key (member count UNCHANGED at 57); only the host
    -- (name + width) grows by the heap-open READ appendix. `bb` is each accumulator's v1 FACE width (the
    -- SAME `bb` `v3RegistryWideBB` uses), aligning the wide AFTER carrier's committed accumulator-root
    -- block with the rotated AFTER block the read appendix welds to.
    else if key == "noteSpendVmDescriptor2R24" then
      -- rc-EMIT FIX (all three §J′ inserts): the insert host rides `withDfaRcPins` — the trio's
      -- committed rows dropped the 4 rc PIs the live members + producer carry (63 ≠ 67).
      let nsHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
        (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
        "dregg-effectvm-noteSpend-v1-rot24-v3-insert-heapopen")
      let nsBB := Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptor.traceWidth
      let nsWide := wideAppend nsHost nsBB (nsBB + 239)
      IO.println s!"{key}\t{(weldWide key nsWide).name}\t{emitVmJson2 (weldWide key nsWide)}"
    else if key == "noteCreateVmDescriptor2R24" then
      let ncHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
        "dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen")
      let ncBB := Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.noteCreateVmDescriptor.traceWidth
      let ncWide := wideAppend ncHost ncBB (ncBB + 239)
      IO.println s!"{key}\t{(weldWide key ncWide).name}\t{emitVmJson2 (weldWide key ncWide)}"
    else if key == "createCellVmDescriptor2R24" then
      let ccHost := withDfaRcPins (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
        "dregg-effectvm-createCell-v1-rot24-v3-insert-heapopen")
      let ccBB := Dregg2.Circuit.Emit.EffectVmEmitCreateCell.createCellActorVmDescriptor.traceWidth
      let ccWide := wideAppend ccHost ccBB (ccBB + 239)
      IO.println s!"{key}\t{(weldWide key ccWide).name}\t{emitVmJson2 (weldWide key ccWide)}"
    -- THE v12 BIG-BANG IN-PLACE REPLACEMENTS (the refusal precedent): the sovereign + transfer
    -- rows advance to the DEPLOYED teeth-exposing members under their LIVE keys (member count
    -- UNCHANGED at 57; the narrow live TSV / FP / VK untouched — the wide slice is the fold lane).
    else if key == "makeSovereignVmDescriptor2R24" then
      -- The DEPLOYED wide sovereign (`CarrierComposed.makeSovereignV3DeployedWide`): rc + the 4
      -- KEY_COMMIT teeth PI pins (58..61 = `SOVEREIGN_KEY_COMMIT_PI_LO`, cols 113..=116) AHEAD of
      -- the 16 wide anchors (62..77) + the in-AIR KEY_COMMIT chip gate (digest appendix at the
      -- wide end, dgBase 1771; width 1803). piCount 74 → 78.
      let msWide := Dregg2.Circuit.Emit.CarrierComposed.makeSovereignV3DeployedWide
      IO.println s!"{key}\t{(weldWide key msWide).name}\t{emitVmJson2 (weldWide key msWide)}"
    else if key == "transferVmDescriptor2R24" then
      -- AVAILABILITY RETARGET (the wide-transfer wrap-forgery closure): the wide membership-teeth
      -- transfer REBUILT over the §11.7 borrow-weld face (`AvailWideMembers.
      -- transferV3MembershipAvailWide` — teeth PIs 50..51 UNCHANGED, rc pins at the avail-shifted
      -- carrier, teeth cols 2617..2618 past the avail carriers; width 2619, piCount 68). The
      -- capacity-floor refuse rides the AVAIL caveat base (`cavBaseOf AVAIL_WIDTH = 676` — the
      -- fixed-base `gentianWideBareRefuse` would decode the WRONG columns on the widened face),
      -- i.e. the committed row is `AvailWideMembers.transferAvailWideRefused`, whose availability
      -- discharge + refuse teeth are proven (`RotatedKernelRefinementAvailWide`,
      -- `declared_*_unsat_availWideRefused`). PI-EXPOSURE leg only (the FOLD edge binds).
      let trWide := Dregg2.Circuit.Emit.AvailWideMembers.transferAvailWideRefused
      IO.println s!"{key}\t{trWide.name}\t{emitVmJson2 trWide}"
    else if key == "burnVmDescriptor2R24" then
      -- AVAILABILITY RETARGET, the WIDE-BURN twin (the LAST wrap-class member): the crown burn
      -- host rebuilt over the §8¾ borrow-weld face (`AvailWideMembers.burnV3AvailWide` — 66 PIs
      -- UNCHANGED, burn carries no membership teeth; rc pins at the burn-avail-shifted carrier;
      -- width 2607 → 2615). The capacity-floor refuse rides the burn AVAIL caveat base
      -- (`cavBaseOf 196 = 674` — the fixed-base `gentianWideBareRefuse` would decode the WRONG
      -- columns on the widened face), i.e. the committed row is
      -- `AvailWideMembers.burnAvailWideRefused`, whose availability discharge + refuse teeth are
      -- proven (`RotatedKernelRefinementMintBurnAvailWide`,
      -- `declared_*_unsat_burnAvailWideRefused`).
      let buWide := Dregg2.Circuit.Emit.AvailWideMembers.burnAvailWideRefused
      IO.println s!"{key}\t{buWide.name}\t{emitVmJson2 buWide}"
    else
      IO.println s!"{key}\t{(weldWide key d).name}\t{emitVmJson2 (weldWide key d)}"
  -- position 45: `transferCapOpenTB` made 8-felt-wide, RETARGETED to the AVAIL base (the
  -- wide-transfer wrap-forgery closure): `effCapOpenV3TB (v3OfFrozenWide transferVmDescriptorAvail)
  -- … EFF_TRANSFER` (+2 turn-identity columns / +3 PI pins, all parametric in the base), wide-appended
  -- at the AVAIL face base (`bb = AVAIL_WIDTH = 198` — rotateV3 lays the rotated limbs at the
  -- hardened FACE width). `AvailWideMembers.tbAvailWide_row_v1` forces the hardened v1 denotation.
  let tbWide := Dregg2.Circuit.Emit.AvailWideMembers.transferCapOpenTBAvailWide
  IO.println s!"transferCapOpenTBVmDescriptor2R24\t{tbWide.name}\t{emitVmJson2 tbWide}"
  -- position 46: `heapWrite` (the after-spine membership-forcing heap-write descriptor, OPTION I) made
  -- 8-felt-wide — EXACTLY as cap deploys `effCapOpenWriteV3`. The host is `effHeapWriteV3 heapWriteV3
  -- …-write-heapopen`: the Class-A splice base (`heapWriteV3` = graduated+rotated splice + the splice
  -- `MapOp`) WIDENED by the heap-open READ appendix + the AFTER-spine membership appendix, so the
  -- DEPLOYED descriptor's `Satisfied2` FORCES the faithful 8-felt heap-write over the full ~124-bit
  -- BEFORE/AFTER root blocks (`HeapOpenEmit.effHeapWriteV3_forces_write8`) — never the lane-0 squeeze the
  -- map_op-only path would leave. `rotateV3` lays the BEFORE limbs at the splice FACE width, so `bb =
  -- heapWriteSpliceVmDescriptor.traceWidth (= EFFECT_VM_WIDTH)`, aligning the after-spine's committed
  -- heap-root blocks (`heapRootGroupCol (EFFECT_VM_WIDTH + 239)`) with the wide AFTER rotated carrier.
  let hwBB := Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor.traceWidth
  let hwHost := Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
    Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
    "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen"
  let hwWide := wideAppend hwHost hwBB (hwBB + 239)
  IO.println s!"heapWriteVmDescriptor2R24\t{hwWide.name}\t{emitVmJson2 hwWide}"
  -- positions 47..55: the WRITE-bearing cap-open tail (`v3RegistryCapOpenWriteWide`, §10) made
  -- 8-felt-wide, in its own order, EXCEPT `grantCapWriteCapOpen` — which is NOT a member of the live
  -- `V3_STAGED_REGISTRY_TSV`, so it is reconciled OUT to keep the wide registry a member-for-member
  -- cover of live. The remaining 9 land exactly at live positions 47..55.
  for (key, d) in v3RegistryCapOpenWriteWide do
    if key != "grantCapWriteCapOpenVmDescriptor2R24" then
      IO.println s!"{key}\t{(weldWide key d).name}\t{emitVmJson2 (weldWide key d)}"
  -- position 56: `supplyMint` (the dedicated `sel.MINT` mint) made 8-felt-wide. `supplyMintV3 =
  -- withSelectorGate sel.MINT (v3OfFrozen mintTickFace)`; the BEFORE limbs are laid at the mint FACE
  -- width, so `bb = mintTickFace.traceWidth` (the SAME base as the cohort `mint` member, position 2).
  let smBB := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintTickFace.traceWidth
  let smWide := wideAppend Dregg2.Circuit.Emit.EffectVmEmitRotationV3.supplyMintV3 smBB (smBB + 239)
  IO.println s!"supplyMintVmDescriptor2R24\t{smWide.name}\t{emitVmJson2 smWide}"
