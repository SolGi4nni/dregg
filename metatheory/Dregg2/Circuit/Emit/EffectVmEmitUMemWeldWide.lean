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

/-- **The Lean-emitted WIDE+UMEM WELDED registry (STAGED).** The welded twin of the wire's WIDE
cap-open registry: every `v3RegistryCapOpenWide` AUTHORITY-crown member welded with the domain its
effect touches, PLUS the §10 WRITE-bearing cap-open tail welded the same way (`weldedWriteTail`) — the
write wrappers the deployed wire routes the write-bearing cap siblings to. Keyed by the SAME live
registry key (name-stable, so the by-name executor verifier resolves the welded member as `<live
key>`). The driver writes these exact bytes to the staged TSV. -/
def weldedWideRegistry : List (String × EffectVmDescriptor2) :=
  v3RegistryCapOpenWide.map (fun e => (e.1, weldUMemIntoWide e.2 (wideKeyUMemDomain e.1)))
    ++ weldedWriteTail

/-! ## STRUCTURAL pins (the committed-descriptor discipline — the byte-level pin is the Rust
`WIDE_UMEM_WELD_REGISTRY_FP` sha256 over the whole emitted TSV, matching how `WIDE_REGISTRY_STAGED`
is pinned; these `#guard`s pin the SHAPE the bytes realize). -/

-- Cover: the 45 AUTHORITY-crown wide members + the 9 WRITE-tail wrappers (the §10 write tail MINUS
-- `grantCapWriteCapOpen`), name-stable on the keys with their bare wide twins.
#guard weldedWideRegistry.length == 54
#guard weldedWriteTail.length == 9
#guard (weldedWideRegistry.take 45).map (·.1) == v3RegistryCapOpenWide.map (·.1)
#guard (weldedWideRegistry.drop 45).map (·.1) ==
  (v3RegistryCapOpenWriteWide.filter (fun e => e.1 != grantCapWriteKey)).map (·.1)
-- Every welded member carries the staged weld marker + EXACTLY ONE welded umem op.
#guard weldedWideRegistry.all (fun e => e.2.name.endsWith wideUMemWeldSuffix)
#guard weldedWideRegistry.all (fun e => (umemOpsOf e.2).length == 1)
-- THE NO-NARROWING INVARIANT: the weld is additive — `traceWidth = host + 7` and `piCount` is
-- UNCHANGED (the 16 wide-commit PIs / the 8-felt anchors ride through at the same offsets). Checked on
-- BOTH the crown members and the welded write tail.
#guard (v3RegistryCapOpenWide.zip (weldedWideRegistry.take 45)).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
#guard ((v3RegistryCapOpenWriteWide.filter (fun e => e.1 != grantCapWriteKey)).zip
    (weldedWideRegistry.drop 45)).all
  (fun p => p.2.2.traceWidth == p.1.2.traceWidth + 7 ∧ p.2.2.piCount == p.1.2.piCount)
-- The welded member declares the two universal-memory tables (umemory id 6, umem_boundary id 7).
#guard weldedWideRegistry.all (fun e =>
  e.2.tables.any (fun t => t.id = TableId.custom UMEM_TID) ∧
  e.2.tables.any (fun t => t.id = TableId.custom 2 ∧ t.name == "umem_boundary"))

end Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide
