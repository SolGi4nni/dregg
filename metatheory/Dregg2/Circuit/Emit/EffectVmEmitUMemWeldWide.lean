/-
# Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide — the Lean-emitted WIDE+UMEM WELDED registry
(STAGED, VK-RISK-FREE): the MISSING VERIFIER LEG's grounded descriptor set.

The WIDE+umem weld (`prove_wide_umem_welded_staged` + the IVC fold) had a producer leg and an IVC
leg but NO Lean-emitted, byte-pinned descriptor set the wire verifier could iterate — so a welded
proof verified under no DEPLOYED descriptor (only against the descriptor the producer just built,
or the leg's own carried copy). This module CLOSES that: it welds the universal-memory cohort leg
INTO every member of the verified `CapOpenEmit.v3RegistryCapOpenWide` (the 45-member 8-felt wide
registry), IN LEAN — so the welded VK is Lean-grounded (the ONE-Lean-derived-circuit/VK invariant),
NOT hand-welded in Rust. The driver `EmitWideUMemWeldRegistryProbe.lean` writes these exact bytes to
`circuit/descriptors/rotation-wide-umem-welded-registry-staged.tsv`, pinned by
`WIDE_UMEM_WELD_REGISTRY_FP` (the sha256 the Rust side asserts) + the per-member parity tooth
(Rust's `weld_umem_into_wide_descriptor` of the bare member byte-equals the Lean-emitted welded
member). The Rust verify paths (`verify_effect_vm_rotated_with_cutover`, the IVC `admit_welded_leg`)
iterate THIS registry as a NEW accepted form beside the bare wide registry.

## The weld (the Lean twin of Rust `weld_umem_into_descriptor_with_suffix(_, dom, …, cohort:=false)`)

Purely ADDITIVE: append the single-domain cohort `umemOp` over 7 fresh main columns
`[base .. base+7)` (`base` = the wide trace width, PAST the wide carriers) + the `umemory` /
`umem_boundary` tables onto the wide member. It NEVER touches `public_input_count` nor any existing
constraint, so the wide member's whole PI vector + every PI binding (incl. all 16 wide-commit
`PiBinding`s = the 8-felt ~124-bit before/after anchors) survive UNCHANGED — the no-narrowing
property the VK epoch refused to cross. The single-domain `dom` the welded member carries is the
domain that member's effect touches (heap 1 / caps 2 / nullifiers 3, per `turn/src/umem.rs`).

## VK-RISK-FREE

A NEW registry constant BESIDE the deployed wide registry: no VK bump, nothing on the live wire,
`umem_witness_enabled` untouched. The deployed default prover/verifier stay bare until the gated VK
epoch (the owner's separate go).
-/
import Dregg2.Circuit.Emit.CapOpenEmit
import Dregg2.Circuit.Emit.CapOpenTurnPins
import Dregg2.Circuit.Emit.HeapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit
import Dregg2.Circuit.Emit.AccumulatorInsertEmit
import Dregg2.Circuit.Emit.CarrierComposed
import Dregg2.Circuit.RotatedKernelRefinementExercise

namespace Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Crypto.UniversalMemory (Domain)
open Dregg2.Circuit.Emit.CapOpenEmit (v3RegistryCapOpenWide v3RegistryCapOpenWriteWide)

set_option autoImplicit false

/-- The staged WIDE+umem weld name suffix (mirrors the Rust `WIDE_UMEM_WELD_SUFFIX`). A descriptor
whose `name` ends with this is the WIDE single-domain rotated+umem weld. -/
def wideUMemWeldSuffix : String := "-umem-wide-welded-staged"

/-- The single-domain universal-memory domain a wide member's effect touches, keyed by the LIVE
registry key. Mirrors the per-cell domain map of `turn/src/umem.rs` the cohort emitter uses: a UKey's
`domain()` decides the plane, and the `caps` plane (domain 2) is `CapSlot`/`Delegate`/`DelegationSnapshot`/
`DelegationEpoch`/`Permissions`/`VerificationKey`/`Program`/`CapTombstone`/`Factory`, the `heap` plane
(domain 1) is `Field`/`Balance`/`Nonce`/`Lifecycle`/`Identity`/… So:

  * the capability verbs (grant / attenuate / revoke / introduce / delegate / refresh / spawn, with
    their CapOpen / Write twins) touch the `caps` plane via `CapSlot`/`Delegate`/`Program`;
  * **`setPerms` / `setVK` ALSO touch the `caps` plane** — their projection diff is a single
    `UKey::Permissions` / `UKey::VerificationKey` write, both `UDomain::Caps` (`turn/src/umem.rs`
    `UKey::domain`). The producer's welded leg therefore reconciles domain 2; a welded entry declaring
    `heap` here binds NO descriptor on the deployed wire (the 9th flip-refusal `a5df2470`). They are
    NOT name-prefixed by a cap verb, so they are matched explicitly;
  * every OTHER cohort member's single-domain state touch is a `heap`-domain write (e.g. cellSeal /
    cellUnseal / cellDestroy / receiptArchive move `Lifecycle`; transfer / burn / mint move `Balance`).

The multi-domain note/bridge verbs are NOT single-domain-weldable (the producer fails closed on them),
so their welded entry is unexercisable — keyed `heap` as a harmless placeholder. -/
def wideKeyUMemDomain (key : String) : Domain :=
  if "grant".isPrefixOf key || "attenuate".isPrefixOf key || "revoke".isPrefixOf key
      || "introduce".isPrefixOf key || "delegate".isPrefixOf key || "refresh".isPrefixOf key
      || "spawn".isPrefixOf key || "setPerms".isPrefixOf key || "setVK".isPrefixOf key then
    Domain.caps
  else
    Domain.heap

/-- **The purely-ADDITIVE WIDE+umem weld.** The Lean twin of Rust
`weld_umem_into_descriptor_with_suffix(d, dom, WIDE_UMEM_WELD_SUFFIX, cohort := false)`: append the
single-domain cohort `umemOp` over 7 fresh main columns `[base .. base+7)` (`base = d.traceWidth`,
PAST the wide carriers) + the `umemory` (arity 8) / `umem_boundary` (arity 7, GENERAL — the wide
single-domain weld uses the general boundary, `cohort = false`) tables. The MAIN table arity is
bumped to the welded width; every OTHER table + EVERY existing constraint (incl. all 16 wide-commit
`PiBinding`s) survives untouched, and `piCount` is UNCHANGED — so the 8-felt anchors ride through at
the SAME PI offsets. NO narrowing. -/
def weldUMemIntoWide (d : EffectVmDescriptor2) (dom : Domain) : EffectVmDescriptor2 :=
  let base := d.traceWidth
  { d with
    name        := d.name ++ wideUMemWeldSuffix
    traceWidth  := base + 7
    tables      :=
      d.tables.map (fun t => if t.id = TableId.main then { t with arity := base + 7 } else t)
        ++ [umemTableDef, umemBoundaryTableDef]
    constraints :=
      d.constraints ++
        [ .umemOp
            { guard := .var (base + 6)
            , domain := dom
            , key := .var base
            , present := .var (base + 1)
            , value := .var (base + 2)
            , prevPresent := .var (base + 3)
            , prevValue := .var (base + 4)
            , prevSerial := .var (base + 5)
            , kind := Dregg2.Crypto.MemoryChecking.Kind.write } ] }

/-- The §10 WRITE-bearing cap-open tail key the wide registry RECONCILES OUT (`grantCapWriteCapOpen` is
NOT a live `V3_STAGED_REGISTRY_TSV` member, so it has no bare wide twin in `WIDE_REGISTRY_STAGED_TSV`).
The welded write tail mirrors the wide registry's membership, so it drops the same key. -/
def grantCapWriteKey : String := "grantCapWriteCapOpenVmDescriptor2R24"

/-- **The welded WRITE-bearing cap-open tail (STAGED).** The §10 `v3RegistryCapOpenWriteWide` members
(the `…WriteCapOpenVmDescriptor2R24` wrappers a domain-2 cap WRITE turn actually routes to on the
deployed wire, plus the `spawnCapOpen` / `exerciseCapOpen` read legs) welded with the CAPS domain,
MINUS `grantCapWriteCapOpen` (reconciled out, exactly as `EmitWideRegistryProbe` does — it is not a
bare `WIDE_REGISTRY_STAGED_TSV` member). These are the welded twins the wire verifier resolves for the
write-routed cap siblings (delegate/grantCap, introduce, refreshDelegation, revokeCapability,
revokeDelegation): without them a write-routed welded proof verified under NO cohort descriptor. -/
def weldedWriteTail : List (String × EffectVmDescriptor2) :=
  (v3RegistryCapOpenWriteWide.filter (fun e => e.1 != grantCapWriteKey)).map
    (fun e => (e.1, weldUMemIntoWide e.2 (wideKeyUMemDomain e.1)))

/-- **The 3 LIVE-ONLY wide members the bare wide registry carries beyond `v3RegistryCapOpenWide` + the
write tail.** `WIDE_REGISTRY_STAGED_TSV` is a 57-member cover of the live V3 registry: the 45
`v3RegistryCapOpenWide` crown + the 9 §10 write-tail wrappers + THESE three —
`transferCapOpenTBVmDescriptor2R24` (the turn-identity-pinned transfer cap-open),
`heapWriteVmDescriptor2R24` (the AFTER-SPINE membership-forcing heap-write `effHeapWriteV3 heapWriteV3
…` over the Class-A sorted-Merkle splice base), `supplyMintVmDescriptor2R24` (the
dedicated `sel.MINT` mint). They have NO `v3RegistryCapOpenWide` / `…WriteWide` emit source, so the
welded twin set omitted them — yet each is a deployed wide member a turn routes to, so a welded proof
routed to one bound NO cohort descriptor on the wire. Built at the SAME wide geometry
`EmitWideRegistryProbe` emits them (the byte-identical wide host = the bare wide member), so the Rust
`weld_umem_into_wide_descriptor` of the bare member byte-matches the welded twin. -/
def liveOnlyWideHosts : List (String × EffectVmDescriptor2) :=
  let tbBB := Dregg2.Circuit.Emit.EffectVmEmitTransfer.transferVmDescriptor.traceWidth
  let tbHost := Dregg2.Circuit.Emit.CapOpenTurnPins.effCapOpenV3TB
    Dregg2.Circuit.Emit.CapOpenEmit.transferV3
    "dregg-effectvm-transfer-v1-rot24-v3-capopen-eff-tb" Dregg2.Circuit.Emit.CapOpenEmit.EFF_TRANSFER
  let tbWide := Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend tbHost tbBB (tbBB + 227)
  -- heapWrite: the AFTER-SPINE membership-forcing heap-write host (`effHeapWriteV3 heapWriteV3 …`),
  -- EXACTLY the bare `EmitWideRegistryProbe` position-46 host — the Class-A splice base widened by the
  -- heap-open READ appendix + the AFTER-spine membership appendix, so the deployed descriptor's
  -- `Satisfied2` FORCES the faithful 8-felt heap-write (`HeapOpenEmit.effHeapWriteV3_forces_write8`),
  -- never the lane-0 squeeze the raw map_op-only splice host left. `ab = bb + 227` (`B_SPAN`).
  let hwBB := Dregg2.Circuit.Emit.EffectVmEmitHeapRoot.heapWriteSpliceVmDescriptor.traceWidth
  let hwHost := Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
    Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
    "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen"
  let hwWide := Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend hwHost hwBB (hwBB + 227)
  let smBB := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintTickFace.traceWidth
  let smWide := Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.supplyMintV3 smBB (smBB + 227)
  [ ("transferCapOpenTBVmDescriptor2R24", tbWide)
  , ("heapWriteVmDescriptor2R24", hwWide)
  , ("supplyMintVmDescriptor2R24", smWide) ]

/-- **The welded LIVE-ONLY tail (STAGED).** The 3 `liveOnlyWideHosts` welded with the heap domain each
touches (`wideKeyUMemDomain` returns `heap` for all three — transfer / heap-splice / mint move
`Balance` / `Lifecycle`, NOT the caps plane). These complete the welded twin set to a member-for-member
57/57 cover of the bare wide registry: with them, a welded proof routed to ANY deployed wide member
resolves a Lean-grounded welded descriptor. -/
def weldedLiveOnlyTail : List (String × EffectVmDescriptor2) :=
  liveOnlyWideHosts.map (fun e => (e.1, weldUMemIntoWide e.2 (wideKeyUMemDomain e.1)))

/-- **The AFTER-SPINE refusal wide host.** The bare wide registry (`EmitWideRegistryProbe`) REPLACES the
position-7 `refusalVmDescriptor2R24` crown member IN PLACE with the after-spine membership-forcing
`effFieldsWriteV3 refusalFieldsWriteV3 …` (EXACTLY as heap deploys `effHeapWriteV3` and cap deploys
`effCapOpenWriteV3`): the DEPLOYED refusal descriptor's `Satisfied2` FORCES the faithful 8-felt
fields-write over the full ~124-bit BEFORE/AFTER fields-root blocks
(`FieldsOpenEmit.effFieldsWriteV3_forces_write8`). Built at the SAME geometry the bare emit uses —
`bb = refusalVmDescriptor.traceWidth`, `ab = bb + 227` (`B_SPAN`) — so the welded twin welds onto the
GENUINE after-spine wide, not the stale record-pin refusal (`v3RegistryCapOpenWide`'s own position-7
entry is the pre-after-spine refusal; the bare emit + this welded emit both override it). -/
def refusalAfterSpineWide : EffectVmDescriptor2 :=
  -- rc-EMIT (the bare-probe mirror): the welded host rides `withDfaRcPins` exactly as the bare
  -- `EmitWideRegistryProbe` row does, so the weld parity (welded == Rust weld of bare) holds.
  let rfHost := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins
    (Dregg2.Circuit.Emit.FieldsOpenEmit.effFieldsWriteV3
      Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalFieldsWriteV3
      "dregg-effectvm-refusal-v1-rot24-v3-write-fieldsopen")
  let rfBB := Dregg2.Circuit.Emit.EffectVmEmitRefusal.refusalVmDescriptor.traceWidth
  Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend rfHost rfBB (rfBB + 227)

/-- **The §J′ INSERT-shaped accumulator wide hosts** — the insert twins of `refusalAfterSpineWide`. Each
is `wideAppend (effAccumInsertV3 groupCol keyCol valueCol baseV3 …) bb (bb+151)` at the accumulator's v1
FACE `bb` (the SAME geometry the bare emit + `v3RegistryWideBB` use). The DEPLOYED accumulator descriptor
FORCES the faithful 8-felt INSERT over the genuine sorted fresh-key insert (`effAccumInsertV3_forces_
write8`), NEVER the lane-0 squeeze. Key-stable swaps into `crownWideHosts` (positions 3/4/22). -/
def noteSpendInsertWide : EffectVmDescriptor2 :=
  let host := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins
    (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
    (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
      Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
    (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
    "dregg-effectvm-noteSpend-v1-rot24-v3-insert-heapopen")
  let bb := Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.noteSpendVmDescriptor.traceWidth
  Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend host bb (bb + 227)

def noteCreateInsertWide : EffectVmDescriptor2 :=
  let host := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins
    (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
    (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
      Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
    none
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
    "dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen")
  let bb := Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.noteCreateVmDescriptor.traceWidth
  Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend host bb (bb + 227)

def createCellInsertWide : EffectVmDescriptor2 :=
  let host := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins
    (Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
    none
    Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
    "dregg-effectvm-createCell-v1-rot24-v3-insert-heapopen")
  let bb := Dregg2.Circuit.Emit.EffectVmEmitCreateCell.createCellActorVmDescriptor.traceWidth
  Dregg2.Circuit.Emit.EffectVmEmitRotationWide.wideAppend host bb (bb + 227)

/-- **The 45 AUTHORITY-crown wide HOSTS** — `v3RegistryCapOpenWide` with the position-7 refusal member
REPLACED by the after-spine `refusalAfterSpineWide` AND the §J′ accumulator positions (3/4/22:
noteSpend/noteCreate/createCell) REPLACED by their insert-shaped `effAccumInsertV3` wide hosts
(key-stable, so the by-name resolver is unchanged), mirroring the bare `EmitWideRegistryProbe` overrides.
Every OTHER crown member is a faithful after-spine wide already (the cap-open crown carries the 8-felt
anchors), so only refusal + the three accumulators need the swap. -/
def crownWideHosts : List (String × EffectVmDescriptor2) :=
  v3RegistryCapOpenWide.map (fun e =>
    if e.1 == "refusalVmDescriptor2R24" then (e.1, refusalAfterSpineWide)
    else if e.1 == "noteSpendVmDescriptor2R24" then (e.1, noteSpendInsertWide)
    else if e.1 == "noteCreateVmDescriptor2R24" then (e.1, noteCreateInsertWide)
    else if e.1 == "createCellVmDescriptor2R24" then (e.1, createCellInsertWide)
    -- The v12 big-bang teeth-exposing advances (the bare-probe mirror, weld-parity-preserving):
    -- the transfer crown host is the membership-teeth member (claim PIs 50..51, teeth columns
    -- past the carriers) and the makeSovereign crown host the KEY_COMMIT-gated member (teeth PIs
    -- 58..61 + the chip gate's digest appendix at the wide end) — the umem weld appends its 7
    -- columns PAST each (at the teeth/appendix end), additive as everywhere.
    else if e.1 == "transferVmDescriptor2R24" then
      (e.1, Dregg2.Circuit.Emit.CarrierComposed.transferV3MembershipWide)
    else if e.1 == "makeSovereignVmDescriptor2R24" then
      (e.1, Dregg2.Circuit.Emit.CarrierComposed.makeSovereignV3DeployedWide)
    else e)

/-- **The Lean-emitted WIDE+UMEM WELDED registry (STAGED).** The welded twin of the wire's WIDE
cap-open registry: every `crownWideHosts` AUTHORITY-crown member (the 45 `v3RegistryCapOpenWide`
members with refusal advanced to the after-spine fields-write host) welded with the domain its effect
touches, PLUS the §10 WRITE-bearing cap-open tail welded the same way (`weldedWriteTail`) — the write
wrappers the deployed wire routes the write-bearing cap siblings to (already the after-spine
`effCapOpenWriteV3` hosts) — PLUS the 3 live-only wide members (`weldedLiveOnlyTail`, transfer /
after-spine heap-write / mint) the bare wide registry carries beyond those two sets, completing the
57/57 cover. Keyed by the SAME live registry key (name-stable, so the by-name executor verifier
resolves the welded member as `<live key>`). The driver writes these exact bytes to the staged TSV. -/
def weldedWideRegistry : List (String × EffectVmDescriptor2) :=
  crownWideHosts.map (fun e => (e.1, weldUMemIntoWide e.2 (wideKeyUMemDomain e.1)))
    ++ weldedWriteTail
    ++ weldedLiveOnlyTail

/-! ## STRUCTURAL pins (the committed-descriptor discipline — the byte-level pin is the Rust
`WIDE_UMEM_WELD_REGISTRY_FP` sha256 over the whole emitted TSV, matching how `WIDE_REGISTRY_STAGED`
is pinned; these `#guard`s pin the SHAPE the bytes realize). -/

-- Cover: the 45 AUTHORITY-crown wide members + the 9 WRITE-tail wrappers (the §10 write tail MINUS
-- `grantCapWriteCapOpen`) + the 3 LIVE-ONLY wide members — a member-for-member 57/57 cover of the bare
-- wide registry, name-stable on the keys with their bare wide twins.
#guard weldedWideRegistry.length == 57
#guard weldedWriteTail.length == 9
#guard weldedLiveOnlyTail.length == 3
#guard (weldedWideRegistry.take 45).map (·.1) == v3RegistryCapOpenWide.map (·.1)
#guard ((weldedWideRegistry.drop 45).take 9).map (·.1) ==
  (v3RegistryCapOpenWriteWide.filter (fun e => e.1 != grantCapWriteKey)).map (·.1)
#guard (weldedWideRegistry.drop 54).map (·.1) ==
  ["transferCapOpenTBVmDescriptor2R24", "heapWriteVmDescriptor2R24", "supplyMintVmDescriptor2R24"]
-- Every welded member carries the staged weld marker + EXACTLY ONE welded umem op.
#guard weldedWideRegistry.all (fun e => e.2.name.endsWith wideUMemWeldSuffix)
#guard weldedWideRegistry.all (fun e => (umemOpsOf e.2).length == 1)
-- THE NO-NARROWING INVARIANT: the weld is additive — `traceWidth = host + 7` and `piCount` is
-- UNCHANGED (the 16 wide-commit PIs / the 8-felt anchors ride through at the same offsets). Checked on
-- the crown members, the welded write tail, AND the 3 live-only welded twins.
#guard (crownWideHosts.zip (weldedWideRegistry.take 45)).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
-- The refusal crown host is the AFTER-SPINE fields-write wide (host + 7 over the after-spine host, NOT
-- the stale `v3RegistryCapOpenWide` position-7 record-pin refusal); the other 44 crown hosts are
-- `v3RegistryCapOpenWide`'s own members, so the crown keys stay name-stable.
#guard crownWideHosts.map (·.1) == v3RegistryCapOpenWide.map (·.1)
#guard (crownWideHosts.filter (·.1 == "refusalVmDescriptor2R24")).map (·.2.traceWidth)
  == [refusalAfterSpineWide.traceWidth]
#guard ((v3RegistryCapOpenWriteWide.filter (fun e => e.1 != grantCapWriteKey)).zip
    ((weldedWideRegistry.drop 45).take 9)).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
#guard (liveOnlyWideHosts.zip (weldedWideRegistry.drop 54)).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
-- The welded member declares the two universal-memory tables (umemory id 6, umem_boundary id 7).
#guard weldedWideRegistry.all (fun e =>
  e.2.tables.any (fun t => t.id = TableId.custom UMEM_TID) ∧
  e.2.tables.any (fun t => t.id = TableId.custom 2 ∧ t.name == "umem_boundary"))

end Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
