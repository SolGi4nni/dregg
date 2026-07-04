/-
# Dregg2.Circuit.CircuitSoundnessAssembled — the COMPOSITION CAPSTONE.

`CircuitSoundness.lightclient_unfoolable` is the apex: from a verifying batch + the named floors it
concludes a genuine kernel transition committing to the published `(pi.pre, pi.post)`. But it carries
the per-effect refinement family `hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e)` as an
OPAQUE hypothesis. This module makes that `∀` EXPLICIT, ENUMERATED, and NAMED.

## What is assembled

  1. **`Rfix : Registry`** — the live `v3Registry` lookup as a `Nat`-indexed `Registry` (the descriptor
     each per-effect rung is about). `Rfix e` is the rotated descriptor at the effect tag `e`
     (`ActionDispatch.actionTag`'s convention); out-of-range indices fall back to the transfer slot
     (the registry is total as a function — every effect index resolves to a real `EffectVmDescriptor2`,
     so `vkOfRegistry Rfix` is well-defined). The fix descriptors (the committed-root-limb variants) and
     the phase-D cap descriptors are the SAME `v3Registry` entries the rungs are stated against, so
     `Rfix` IS the per-effect descriptor each rung discharges.

  2. **`kstepAll : EffectIdx → RecChainedState → RecChainedState → Prop`** — the assembled dispatcher.
     We take `kstepAll := CircuitSoundness.dispatchArm`, the generic dispatcher arm
     (`∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`) the whole-turn apex
     `lightclient_turn_unfoolable_forest` is already stated at. Its `e = 0` (transfer) arm is upgradable
     to the FAITHFUL `dispatchArmFacet` via `RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`
     (the deployed two-axis authority gate), recorded here as the faithful-tier note.

  3. **`EffectDecodeBridge S hash R e`** — the per-effect decode bridge, NAMED. It is EXACTLY
     `descriptorRefines S hash (R e) (kstepAll e)` — the apex-shaped per-effect rung. The honest content:
     each landed per-effect rung (`transfer_descriptorRefines`, `delegate_descriptorRefines`, …)
     concludes its leaf `Spec` from a per-effect ENCODE decode (`rotatedEncodes` /
     `DelegateCapsTreeEncodes` / …), NOT from `StateDecode`. The commitment surface `StateDecode`
     commits the LEDGER ROOT only; the limb-level encode data (the guard fields, the cap-tree opening,
     the per-row column reads) is the genuine residue `StateDecode` cannot carry. So the bridge is NOT
     `StateDecode ⟹ <effect>Encode` (a category error: `StateDecode pc pre post` does not even mention
     the trace `t`, while `<effect>Encode` is a predicate ABOUT `t`'s columns) — the genuine bridge is
     `Satisfied2 (R e) … t ⟹ <effect>Encode`, the per-effect circuit-witness column-read extraction
     (the `WitnessDecodes`-class limb decode the honest prover's trace supplies, certified by
     `StarkSound`); `StateDecode` only supplies the kernel boundary the encode is matched against. NONE
     of the 36 effects bridges from `StateDecode` alone, so the bridge is carried for EVERY effect as the
     named per-effect residual `EffectDecodeBridge`.

     This capstone carries the family OPAQUE (`∀ e, EffectDecodeBridge` as a hypothesis); the closure
     stack REDUCES it. `ClosureAll.effectDecodeBridge_of_closedLogExtract` discharges each
     `EffectDecodeBridge e` from a `ClosedLogExtract e` (= `Satisfied2 (R e) + StateDecodeLog ⟹ kstepAll
     e`), and `ClosureFanoutGenuine.closedLogExtract_all_genuine` discharges `∀ e, ClosedLogExtract` for
     all 36 effects from a `ClosureReadouts` bundle of the per-effect `<e>TraceReadout`
     (`Satisfied2 ⟹ <e>Encodes`) floors, each slot CALLING its proven `<e>_closedLog` /
     `*_descriptorRefines_sat` rung. `ClosureFinal.lightclient_unfoolable_circuit_sound` then collapses
     the `∀ e` over-ask to ONE floor at the published `pi.effect`. So the post-reduction carried set is
     `StarkSound` + `Poseidon2SpongeCR`/`logHashInjective` (standard CR) + the per-effect
     `Satisfied2 ⟹ encode` readout (standard SNARK-witness class) — NOT a `StateDecode`-bridge residual,
     and NOT a new crypto carrier.

  4. **`hrefinesAll`** — `∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)`, assembled from the
     per-effect bridge family `(∀ e, EffectDecodeBridge S hash Rfix e)`. Since `EffectDecodeBridge` IS
     the per-effect `descriptorRefines`, this is the explicit enumeration of the apex's carried `∀` — the
     OPAQUE hypothesis is now a NAMED, per-effect family with its content spelled out.

  5. **`lightclient_unfoolable_assembled`** — the apex instantiated at `Rfix`/`kstepAll`/`hrefinesAll`.
     Its carried floors are EXPLICIT: `StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields,
     `WitnessDecodes`, and the enumerated `EffectDecodeBridge` family. The whole-turn version
     `lightclient_turn_unfoolable_forest_assembled` lifts the same to a verified turn.

## The honest carried-floors ledger

  * `[StarkSound hash Rfix]` — the audited p3 batch-STARK extraction (REALIZABLE, named, not faked).
  * `Poseidon2SpongeCR hash` + the `CommitSurface` CR fields — the decode faithfulness floor (REALIZABLE).
  * `WitnessDecodes hash Rfix S pi` — the witness→kernel-state EXISTENCE rung (REALIZABLE, named).
  * **`∀ e, EffectDecodeBridge S hash Rfix e`** — THE ENUMERATED per-effect decode bridge family. This
    is the apex's old opaque `hrefines` made an explicit, per-effect residual set. Each `e`'s bridge is
    the genuine `Satisfied2 (R e) … t ⟹ <effect>Encode` circuit-witness column-read extraction the
    commitment surface cannot certify (NOT `StateDecode ⟹ <effect>Encode` — `StateDecode` has no `t`).
    The LOGICAL CORE of each rung (`<effect>Encode ⟹ <effect>Spec ⟹ dispatchArm e`) is fully landed in
    the `RotatedKernelRefinement*` family; the bridge is precisely the missing decode-extraction half —
    and it is REDUCED, for all 36 effects, to the named `<e>TraceReadout` (`WitnessDecodes`-class)
    floors in `ClosureFanoutGenuine`/`ClosureFinal` (see §3). This capstone is the OPAQUE-`∀` waypoint;
    the reduced apex is `ClosureFinal.lightclient_unfoolable_circuit_sound`.

This is the honest capstone: the apex stands mod ONE named, enumerated family (`EffectDecodeBridge`)
plus the standard crypto/extraction floors — NOT an opaque carried `∀`.

## Axiom hygiene

`#assert_axioms` on the capstone theorems ⊆ {propext, Classical.choice, Quot.sound}. The named carriers
(`StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields, `WitnessDecodes`, the
`EffectDecodeBridge` family) are HYPOTHESES, not axioms — they do not appear in the axiom set.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.RotatedKernelRefinementFacet
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.RotatedKernelRefinementExercise
import Dregg2.Circuit.Emit.HeapOpenEmit
import Dregg2.Circuit.Emit.FieldsOpenEmit
import Dregg2.Circuit.Emit.AccumulatorInsertEmit
import Dregg2.Circuit.Emit.EffectVmEmitNoteSpend
import Dregg2.Circuit.Emit.EffectVmEmitNoteCreate
import Dregg2.Circuit.Emit.CarrierComposed

namespace Dregg2.Circuit.CircuitSoundnessAssembled

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Exec.TurnExecutorFull (execFullTurnA)
open Dregg2.Exec (RecChainedState)

set_option autoImplicit false

/-! ## §1 — `Rfix`: the live `v3Registry` as a total, `actionTag`-keyed `Registry`.

The apex's `Registry` is `EffectIdx → EffectVmDescriptor2` (a TOTAL function, so `vkOfRegistry` /
`StarkSound.extract` are well-defined at every published effect index). The deployed registry
`EffectVmEmitRotationV3.v3Registry` is a `List (String × EffectVmDescriptor2)` keyed by descriptor
NAME — and its LIST POSITION does NOT coincide with `ActionDispatch.actionTag` (position 1 is `burn`
while `burn`'s tag is `4`; position 2 is `mint` while `mint`'s tag is `3`; only transfer aligns at 0).
The per-effect `*_closedLog`/`ClosedLogExtract` rungs are stated at `actionTag` (`kstepAll <tag>`,
consuming `Satisfied2 (R <tag>)`), so a position-keyed `Rfix` would land each rung at the WRONG
descriptor for every effect except transfer. `Rfix` therefore re-keys by `actionTag`: `Rfix e` is the
genuine `v3Registry` descriptor for the effect whose `ActionDispatch.actionTag` is `e`.

`actionTagToPos` is the explicit `actionTag ↦ registry-position` table (the inverse of the registry's
declaration order). `Rfix e` looks up `v3Registry` at `actionTagToPos e`. Tags with no own rotated
descriptor (the `Scap`/`compressN`-parametric rungs — delegate, revoke, the lifecycle/birth/note family)
point at the `v3Registry` entry their effect family rides (introduce for delegate, the cap revoke for
revoke, …), so `vkOfRegistry Rfix` ranges over exactly the deployed descriptor set; `heapWrite` (tag 56)
NOW has its OWN LIVE Class-A descriptor `heapWriteV3` (the heap-root recompute), at `v3RegistryHeap` tail
position 45 — `Rfix 56 = heapWriteV3` (GAP-2 close). Off-range tags fall back to transfer, so `Rfix` is
total. The key correspondence — `Rfix 0 = transferV3Membership` (the v12 big-bang teeth-exposing
transfer, tail position 60; peels to `transferV3`) — holds by `rfl`, so
`closedLogExtract_transfer` lands at its genuine descriptor via the peel. -/

/-- The transfer descriptor (the fallback for off-range tags; tag `0`). -/
def transferDescr : EffectVmDescriptor2 :=
  Dregg2.Circuit.RotatedKernelRefinement.transferV3

/-- **`v3RegistryHeap`** — the deployed registry EXTENDED with heapWrite at the tail (position 45). The
45-member `v3RegistryCapOpen` (the cap-fanout + LIVE effect-general legs) is the cap cluster's; heapWrite
is the LAST registry effect, its genuine Class-A descriptor `heapWriteV3` (the three heap-root recompute
sites, rotated+graduated). Positions 0..44 are UNCHANGED, so every `Rfix_*` rfl-correspondence is
preserved; `actionTagToPos 56` re-keys to 45 so `Rfix 56` resolves to `heapWriteV3` (no longer the
transfer fallback). -/
def v3RegistryHeap : List (String × EffectVmDescriptor2) :=
  Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpen
    ++ [("heapWriteVmDescriptor2R24",
         -- OPTION I: the DEPLOYED heap-write descriptor is the after-spine membership
         -- `effHeapWriteV3 heapWriteV3 …` (EXACTLY as cap deploys `effCapOpenWriteV3`), so `Rfix 56`
         -- quantifies over the descriptor a light client actually verifies — whose `Satisfied2` FORCES
         -- the faithful 8-felt heap-write (`RotatedKernelRefinementCapFamily.heapWrite_forces_write8_sat`
         -- via `HeapOpenEmit.effHeapWriteV3_forces_write8`), NOT the lane-0 squeeze the map_op-only host
         -- would leave.
         Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
           Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
           "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen"),
        -- The WRITE-FORCING cap-open wrappers (positions 46..49): the fan-out cap-open authority
        -- appendix over the MOVING write base (`grantCapWriteV3`/`introduceWriteV3`/`delegateAttenV3`/
        -- `revokeDelegationWriteV3`), so the DEPLOYED descriptor FORCES the cap-tree write (guarantee A),
        -- not just the authority read. `actionTagToPos` re-keys tags 1/10/11/14 here; the authority-only
        -- wrappers at positions 36..38 + the shared 39 stay for tag 2 (revoke) + the live prover route.
        ("delegateWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.delegateWriteCapOpenV3),
        ("introduceWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.introduceWriteCapOpenV3),
        ("delegateAttenWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.delegateAttenWriteCapOpenV3),
        ("revokeDelegationWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3),
        -- The refreshDelegation WRITE-FORCING wrapper (position 50): the DELEGATIONS-tree UPDATE-write
        -- FORCED on the moving genuine face (the `delegRoot_runtime_column_pending` close — guarantee A).
        -- `actionTagToPos 55` re-keys here; the authority-only `refreshDelegationCapOpenV3` (pos 40) stays
        -- for the live prover route.
        ("refreshDelegationWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.refreshDelegationWriteCapOpenV3),
        -- The SetProgram record-pin descriptor (position 51): the LIVE Class-A program-install
        -- (`setProgramV3 = graduateV1 (rotateV3WithRecordPin B_RECORD_DIGEST setVKVmDescriptor)`).
        -- SetProgram rides the setVK runtime row but pins the cell `program` slot into the authority
        -- residue (B_RECORD_DIGEST). `actionTagToPos 13` re-keys HERE so `Rfix 13 = setProgramV3`.
        ("setProgramVmDescriptor2R24",
         Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setProgramV3),
        -- The spawn WRITE-FORCING cap-open wrapper (position 52): the spawn actor face REBASED onto the
        -- cap-WRITE rotation (`spawnWriteV3`: cap-root limb 25 freed) + the cells grow-gate INSERT (the
        -- accounts insert, limb 0) + the cap-tree handoff INSERT (the parent→child cap edge, limb 25) +
        -- the EFF_DELEGATION_OPS authority appendix. So the DEPLOYED descriptor FORCES the parent→child
        -- CAPABILITY HANDOFF (guarantee A) — the close of the spawn cap-handoff residual. `actionTagToPos
        -- 19` re-keys HERE so `Rfix 19 = spawnWriteCapOpenV3`; the authority-only spawn descriptor stays
        -- for the live prover route, light-client-REJECTED.
        ("spawnWriteCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.spawnWriteCapOpenV3),
        -- The exercise cap-open descriptor (position 53): the FROZEN exercise base + the EFF_EXERCISE
        -- authority appendix (the depth-16 cap-membership crown forcing the exercise hold-gate
        -- `exerciseGuard`'s `confersEdgeTo target` membership in-circuit — `leaf.target = src` + the
        -- facet bit). `actionTagToPos 16` re-keys HERE so `Rfix 16 = exerciseCapOpenV3`: the LAST named
        -- cap-open residual CLOSED. The authority-only `exerciseVmDescriptor2R24` (position 10) stays for
        -- the bare registry slot; the apex's `StarkSound hash Rfix` now quantifies over the crown-bearing
        -- descriptor the SDK route `exerciseViaCapabilityCapOpenVmDescriptor2R24` proves through.
        ("exerciseCapOpenVmDescriptor2R24",
         Dregg2.Circuit.Emit.CapOpenEmit.exerciseCapOpenV3),
        -- The DEDICATED SUPPLY-MINT descriptor (position 54, SUPPLY-MODEL.md Stage 2b): the SAME
        -- proven credit/tick/freeze body as `mintVmDescriptor2R24` (pos 2) but gated on the DEDICATED
        -- supply selector `sel.MINT = 14`, so the supply-creation effect `Effect::Mint` proves under
        -- its OWN selector rather than riding BridgeMint's slot. `actionTagToPos 3` (mint) re-keys
        -- HERE so `Rfix 3 = supplyMintV3`; tag 20 (bridgeMint) keeps pos 2 (its own descriptor).
        -- Positions 0..53 are UNCHANGED, so every prior `Rfix_*` rfl-correspondence is preserved.
        ("supplyMintVmDescriptor2R24",
         Dregg2.Circuit.Emit.EffectVmEmitRotationV3.supplyMintV3),
        -- The DEPLOYED REFUSAL FIELDS-WRITE descriptor (position 55, OPTION I): the after-spine
        -- membership `effFieldsWriteV3 refusalFieldsWriteV3 …` (EXACTLY as heap deploys `effHeapWriteV3`
        -- and cap deploys `effCapOpenWriteV3`). `actionTagToPos 39` re-keys HERE so `Rfix 39` quantifies
        -- over the descriptor a light client actually verifies — whose `Satisfied2` FORCES the faithful
        -- 8-felt fields-write (`RotatedKernelRefinementCapFamily.refusalWrite_forces_write8_sat` via
        -- `FieldsOpenEmit.effFieldsWriteV3_forces_write8`) over the full ~124-bit BEFORE/AFTER fields-root
        -- blocks, NOT the lane-0 squeeze the map_op-only host would leave. The THIRD faithful 8-felt
        -- Merkle root, deployed. The cohort's authority-only `refusalFieldsWriteV3` [pos 7] stays for the
        -- live prover route + the bare slot. Positions 0..54 are UNCHANGED, so every prior `Rfix_*`
        -- rfl-correspondence is preserved.
        ("refusalFieldsWriteVmDescriptor2R24",
         Dregg2.Circuit.Emit.FieldsOpenEmit.effFieldsWriteV3
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalFieldsWriteV3
           "dregg-effectvm-refusal-v1-rot24-v3-write-fieldsopen"),
        -- The THREE DEDICATED ACCUMULATOR INSERT descriptors (positions 56/57/58, §J′): the
        -- insert-shaped `effAccumInsertV3` over the genuine sorted FRESH-KEY insert (the accumulators
        -- are NOT update-at-key — no shared before/after path, a genuine obstruction the update-shaped
        -- `effAccumWriteV3` could not fit). The DEPLOYED descriptor's `Satisfied2` TRACE-FORCES the
        -- spliced-leaf membership in the REBUILT AFTER tree over the FULL committed 8-felt BEFORE/AFTER
        -- accumulator-root groups (`AccumulatorInsertEmit.effAccumInsertV3_forces_write8`, consumed by
        -- `RotatedKernelRefinementCapFamily.{nullifier,commitments,cells}Insert_forces_write8_sat`),
        -- NEVER the lane-0 squeeze. `actionTagToPos {27,28,17}` re-key HERE so `Rfix {27,28,17}`
        -- quantify over the insert hosts a light client actually verifies; the bare `noteSpendV3` /
        -- `noteCreateV3` / `createCellV3` [positions 3/4/22] stay for the live prover route + bare slot.
        -- Positions 0..55 are UNCHANGED, so every prior `Rfix_*` rfl-correspondence is preserved.
        ("noteSpendInsertVmDescriptor2R24",
         Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
           (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
             Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
           (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
           "dregg-effectvm-noteSpend-v1-rot24-v3-insert-heapopen"),
        ("noteCreateInsertVmDescriptor2R24",
         Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
           (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
             Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
           none
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
           "dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen"),
        ("createCellInsertVmDescriptor2R24",
         Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
           none
           Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
           "dregg-effectvm-createCell-v1-rot24-v3-insert-heapopen"),
        -- The DEPLOYED SOVEREIGN member (position 59, the v12 big-bang): the record-pin base + the
        -- cohort rc wrap + the 4 KEY_COMMIT teeth PI pins (58..61, the annotated
        -- `SOVEREIGN_KEY_COMMIT_PI_LO`) + the in-AIR KEY_COMMIT chip-compress gate — the THIRD EDGE:
        -- a satisfying `Satisfied2` FORCES each published teeth PI == `canonical_32_to_felts_4` of
        -- the COMMITTED `B_PUBKEY8` octet (`CarrierComposed.makeSovereignV3Deployed_publishes_key_
        -- commit`), so the fold-bound owner-key claim is welded to the committed authority, not a
        -- free column. `actionTagToPos 38` re-keys HERE so `Rfix 38` quantifies over the descriptor
        -- a light client actually verifies; the cohort's `makeSovereignVmDescriptor2R24` [pos 21]
        -- stays for the bare slot. The full peel (`satisfied2_of_makeSovereignV3Deployed`: gate →
        -- teeth pins → rc) lifts every base-level rung. Positions 0..58 are UNCHANGED, so every
        -- prior `Rfix_*` rfl-correspondence is preserved.
        ("makeSovereignDeployedVmDescriptor2R24",
         Dregg2.Circuit.Emit.CarrierComposed.makeSovereignV3Deployed),
        -- The DEPLOYED MEMBERSHIP-TEETH TRANSFER member (position 60, the v12 big-bang): the cohort
        -- transfer + rc + the two `(sender_leaf, authorized_root)` teeth PI pins (50..51, the
        -- annotated `MEMBERSHIP_CLAIM_PI_LO`). HONEST SCOPE (CarrierComposed §5, the fail-open law
        -- named): the PI EXPOSURE leg only — the FOLD edge (the chain prover's Membership arm)
        -- binds the published tuple to a re-proven `dsl::membership` STARK; the in-AIR sender/root
        -- welds stay the named `MembershipAuthRootEdge` seams. `actionTagToPos 0` re-keys HERE so
        -- `Rfix 0` quantifies over the teeth-exposing transfer a light client actually verifies;
        -- the peel (`satisfied2_of_transferV3Membership`) lifts the transfer rung. Positions 0..59
        -- are UNCHANGED, so every prior `Rfix_*` rfl-correspondence is preserved.
        ("transferMembershipVmDescriptor2R24",
         Dregg2.Circuit.Emit.CarrierComposed.transferV3Membership)]

theorem v3RegistryHeap_length : v3RegistryHeap.length = 61 := by
  simp [v3RegistryHeap, Dregg2.Circuit.Emit.CapOpenEmit.v3RegistryCapOpen_length]

/-- The heapWrite member lands at tail position 45 — `Rfix 56` resolves THERE. -/
theorem v3RegistryHeap_heapWrite :
    (v3RegistryHeap[45]?.map (·.2))
      = some (Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
          Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
          "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen") := rfl

/-- **`actionTagToPos` — the `actionTag ↦ v3Registry-position` table.** The inverse of the registry's
declaration order (which is NOT `actionTag` order). Effects with no own rotated descriptor map to the
`v3Registry` entry their family rides; `heapWrite` (tag 56) and off-range tags map past the registry
(→ the transfer fallback in `Rfix`). -/
def actionTagToPos : EffectIdx → Nat
  | 0  => 60   -- transfer        → transferMembershipVmDescriptor2R24 (the v12 big-bang DEPLOYED
               --                   membership-teeth transfer, `v3RegistryHeap` tail pos 60: the rc
               --                   cohort transfer + the 2 `(sender_leaf, authorized_root)` teeth
               --                   PI pins at 50..51 (`MEMBERSHIP_CLAIM_PI_LO`). The bare cohort
               --                   transfer [pos 0] stays for the live prover route + the fallback.)
  | 1  => 46   -- delegate        → delegateWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE: the cap-open
               --                   authority appendix over the MOVING `grantCapWriteV3` base, so the
               --                   DEPLOYED descriptor FORCES the cap-tree insert write — guarantee A —
               --                   AND the authority leg forces authorizedFacetEffB … (1 <<< EFF_DELEGATION_OPS))
  | 2  => 49   -- revoke          → revokeDelegationWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE: the
               --                   SHARED `revokeDelegationWriteV3` remove base + EFF_DELEGATION_OPS
               --                   appendix; the cap-tree REMOVE FORCED on the moving genuine face —
               --                   guarantee A circuit-bound. `.revoke holder t` and `.revokeDelegationA
               --                   holder t` lower to the SAME `RevokeSpec`/`removeEdgeCaps` kernel step,
               --                   so tag 2 rides the identical write-bearing descriptor as tag 14.)
  | 3  => 54   -- mint            → supplyMintVmDescriptor2R24 (the DEDICATED-selector supply-mint
               --                   member, `v3RegistryHeap` tail pos 54, SUPPLY-MODEL.md Stage 2b;
               --                   `Rfix 3 = supplyMintV3 = withSelectorGate sel.MINT mintV3`, the
               --                   SAME proven body as pos 2 but on the dedicated `sel.MINT = 14`
               --                   selector. Tag 20 (bridgeMint) keeps pos 2 for its own slot.)
  | 4  => 1    -- burn            → burnVmDescriptor2R24
  | 5  => 28   -- setField        → setFieldVmDescriptor2-0R24
  | 6  => 27   -- emitEvent       → emitEventVmDescriptor2R24
  | 7  => 13   -- incrementNonce  → incrementNonceVmDescriptor2R24
  | 8  => 8    -- setPermissions  → setPermsVmDescriptor2R24
  | 9  => 9    -- setVK           → setVKVmDescriptor2R24
  | 10 => 47   -- introduce       → introduceWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE: introduce
               --                   WRITE base `introduceWriteV3` + EFF_INTRODUCE appendix; the cap-tree
               --                   insert FORCED on the moving genuine face — guarantee A circuit-forced)
  | 11 => 48   -- delegateAtten   → delegateAttenWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE:
               --                   `delegateAttenV3` write base + EFF_GRANT_CAPABILITY appendix; the
               --                   insert + the `granted ⊑ held` non-amp FORCED — guarantee A circuit-forced)
  | 12 => 43   -- attenuate       → attenuateCapOpenEffVmDescriptor2R24 (F5: the LIVE IN-CIRCUIT
               --                   authority descriptor — the genuine-submask + decoded-tier cap-open
               --                   the deployed prover routes AND the apex authority leg refines)
  | 14 => 49   -- revokeDelegation→ revokeDelegationWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE:
               --                   `revokeDelegationWriteV3` remove base + EFF_DELEGATION_OPS appendix;
               --                   the cap-tree REMOVE FORCED on the moving genuine face — guarantee A)
  | 16 => 53   -- exercise        → exerciseCapOpenVmDescriptor2R24 (the FROZEN exercise base + the
               --                   EFF_EXERCISE authority appendix; the depth-16 cap-membership crown
               --                   FORCES the exercise hold-gate `exerciseGuard`'s `confersEdgeTo target`
               --                   membership in-circuit — the LAST named cap-open residual CLOSED. The
               --                   authority-only `exerciseVmDescriptor2R24` [pos 10] stays for the live
               --                   prover route + the bare slot.)
  | 17 => 58   -- createCell      → createCellInsertVmDescriptor2R24 (§J′: the DEPLOYED cells-accumulator
               --                   INSERT host `effAccumInsertV3 cellsRootGroupCol …`, `v3RegistryHeap`
               --                   tail pos 58; `Rfix 17` FORCES the faithful 8-felt cells-insert over the
               --                   genuine sorted fresh-key insert. The bare `createCellV3` [pos 22] stays.)
  | 18 => 23   -- factory         → factoryVmDescriptor2R24
  | 19 => 52   -- spawn           → spawnWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE: the spawn actor
               --                   face on the cap-WRITE rotation `spawnWriteV3` + the cells grow-gate
               --                   INSERT + the cap-tree handoff INSERT + EFF_DELEGATION_OPS appendix;
               --                   the parent→child CAPABILITY HANDOFF FORCED in-circuit — guarantee A,
               --                   the spawn cap-handoff close)
  | 20 => 2    -- bridgeMint      → mintVmDescriptor2R24 (refines MintASpec)
  | 24 => 41   -- revokeCapability→ revokeCapabilityCapOpenVmDescriptor2R24 (FAN-OUT: revokeCapability
               --                   base + EFF_REVOKE_CAPABILITY appendix; bit 1<<3, DISTINCT from the
               --                   revoke(Delegation) EFF_DELEGATION_OPS fan-out at pos 39. The Lean
               --                   tag is the wire `sel::REVOKE_CAPABILITY` selector value 24 — the
               --                   tag `cap_open_route_for_run` routes a `RevokeCapability` run to.)
  | 27 => 56   -- noteSpend       → noteSpendInsertVmDescriptor2R24 (§J′: the DEPLOYED nullifier-accumulator
               --                   INSERT host `effAccumInsertV3 nullifierRootGroupCol …`, `v3RegistryHeap`
               --                   tail pos 56; `Rfix 27` FORCES the faithful 8-felt nullifier-insert over
               --                   the genuine sorted fresh-key insert. The bare `noteSpendV3` [pos 3] stays.)
  | 28 => 57   -- noteCreate      → noteCreateInsertVmDescriptor2R24 (§J′: the DEPLOYED commitments-accumulator
               --                   INSERT host `effAccumInsertV3 commitmentsRootGroupCol …`, `v3RegistryHeap`
               --                   tail pos 57; `Rfix 28` FORCES the faithful 8-felt commitments-insert. The
               --                   bare `noteCreateV3` [pos 4] stays for the live prover route.)
  | 38 => 59   -- makeSovereign   → makeSovereignDeployedVmDescriptor2R24 (the v12 big-bang DEPLOYED
               --                   sovereign, `v3RegistryHeap` tail pos 59: rc + the 4 KEY_COMMIT
               --                   teeth PI pins at 58..61 (`SOVEREIGN_KEY_COMMIT_PI_LO`) + the
               --                   in-AIR KEY_COMMIT chip-compress gate welding the published teeth
               --                   to the committed `B_PUBKEY8` octet. The cohort member [pos 21]
               --                   stays for the bare slot.)
  | 39 => 55   -- refusal          → refusalFieldsWriteVmDescriptor2R24 (OPTION I: the DEPLOYED after-spine
               --                   fields-write `effFieldsWriteV3 refusalFieldsWriteV3 …`, `v3RegistryHeap`
               --                   tail pos 55; `Rfix 39` FORCES the faithful 8-felt fields-write over the
               --                   full ~124-bit BEFORE/AFTER fields-root blocks — the THIRD faithful root.
               --                   The cohort's `refusalFieldsWriteV3` [pos 7] stays for the live prover route.)
  | 40 => 25   -- receiptArchive  → receiptArchiveVmDescriptor2R24
  | 47 => 11   -- pipelinedSend   → pipelinedSendVmDescriptor2R24
  | 52 => 5    -- cellSeal        → cellSealVmDescriptor2R24
  | 53 => 26   -- cellUnseal      → cellUnsealVmDescriptor2R24
  | 54 => 6    -- cellDestroy     → cellDestroyVmDescriptor2R24
  | 55 => 50   -- refreshDelegation→ refreshDelegationWriteCapOpenVmDescriptor2R24 (FAN-OUT WRITE:
               --                   `refreshDelegationWriteV3` DELEG-tree UPDATE base + EFF_DELEGATION_OPS
               --                   appendix; the DELEGATIONS-tree write FORCED in-circuit — guarantee A,
               --                   the `delegRoot_runtime_column_pending` close)
  | 56 => 45   -- heapWrite        → heapWriteVmDescriptor2R24 (the LIVE Class-A heap-root recompute
               --                   descriptor, `v3RegistryHeap` tail; `Rfix 56 = heapWriteV3`)
  | 13 => 51   -- setProgram       → setProgramVmDescriptor2R24 (the LIVE Class-A program-install
               --                   record-pin descriptor, `v3RegistryHeap` tail; `Rfix 13 = setProgramV3`)
  | _  => 1000 -- off-range: past the registry → transfer fallback

/-- **`Rfix` — the live registry as a total, `actionTag`-keyed lookup.** `Rfix e` is the rotated
`v3Registry` descriptor for the effect whose `ActionDispatch.actionTag` is `e` (NOT the descriptor at
LIST POSITION `e` — declaration order ≠ tag order). The lookup goes through `actionTagToPos`; tags with
no own descriptor (heapWrite, off-range) fall back to the transfer descriptor, so `Rfix` is total. This
lands each per-effect rung (stated at `actionTag`) at its GENUINE descriptor — in particular
`Rfix 0 = transferV3Membership` (the v12 teeth-exposing transfer) by `rfl`. -/
def Rfix : Registry := fun e =>
  match v3RegistryHeap[actionTagToPos e]? with
  | some (_, d) => d
  | none => transferDescr

/-- `Rfix` is total: every effect index resolves to a real descriptor (so `vkOfRegistry Rfix` and the
`StarkSound`/`WitnessDecodes` floors are well-defined at every published index). Holds by construction
(`match` is total). -/
theorem Rfix_total (e : EffectIdx) : ∃ d : EffectVmDescriptor2, Rfix e = d := ⟨Rfix e, rfl⟩

/-- **`Rfix_transfer` — the key correspondence: the transfer tag lands at the DEPLOYED
membership-teeth transfer.** `actionTag (.balanceA …) = 0` and `actionTagToPos 0 = 60`, and
`v3RegistryHeap`'s position-60 entry is `CarrierComposed.transferV3Membership` — the transfer
descriptor `v3OfFrozen transferVmDescriptor = transferV3` wrapped through the uniform DSL rc-EMIT
(`withDfaRcPins`, 4 additive pins) THEN the two membership teeth PI pins (`withMembershipTeethPins`,
the `(sender_leaf, authorized_root)` claim slots 50..51 — `MEMBERSHIP_CLAIM_PI_LO`, the v12
big-bang exposure). Both wraps only APPEND `.piBinding` pins
(`CarrierComposed.satisfied2_of_transferV3Membership` peels the chain), so `Rfix 0` IS the genuine
transfer descriptor UP TO the additive pins — the rung at the transfer tag discharges its
refinement about the right descriptor via the peel. -/
theorem Rfix_transfer :
    Rfix 0 = Dregg2.Circuit.Emit.CarrierComposed.transferV3Membership := rfl

/-- **`Rfix_makeSovereign` — the v12 big-bang: makeSovereign (tag 38) ranges over its OWN DEPLOYED
key-commit descriptor.** `actionTagToPos 38 = 59` and `v3RegistryHeap`'s position-59 entry is
`CarrierComposed.makeSovereignV3Deployed` — the record-pin base + rc + the 4 KEY_COMMIT teeth PI
pins (58..61, `SOVEREIGN_KEY_COMMIT_PI_LO`) + the in-AIR KEY_COMMIT chip-compress gate. So the
apex's `StarkSound hash Rfix` quantifies over the descriptor a light client actually verifies —
whose `Satisfied2` FORCES each published teeth PI == `canonical_32_to_felts_4` of the COMMITTED
BEFORE `B_PUBKEY8` octet (`CarrierComposed.makeSovereignV3Deployed_publishes_key_commit`): the
fold-bound owner-key claim is welded in-AIR to the committed authority, never a free column. The
cohort's bare member [pos 21] stays for the live prover route + the bare slot. -/
theorem Rfix_makeSovereign :
    Rfix 38 = Dregg2.Circuit.Emit.CarrierComposed.makeSovereignV3Deployed := rfl

/-- **`Rfix_heapWrite` — GAP-2 + OPTION I: heapWrite (tag 56) ranges over its OWN DEPLOYED descriptor.**
`actionTagToPos 56 = 45` and `v3RegistryHeap`'s position-45 entry is now the DEPLOYED after-spine
membership descriptor `effHeapWriteV3 heapWriteV3 …` (EXACTLY as cap deploys `effCapOpenWriteV3`). So
`vkOfRegistry Rfix` / the apex's `StarkSound hash Rfix` quantify over the descriptor a light client
actually verifies, and the heapWrite rung
(`RotatedKernelRefinementCapFamily.heapWrite_forces_write8_sat`) discharges its refinement about the
RIGHT one: a satisfying `Satisfied2 (Rfix 56)` FORCES the faithful 8-felt `heapWritesTo8` over the FULL
committed BEFORE/AFTER heap-root blocks (`HeapOpenEmit.effHeapWriteV3_forces_write8`) — NEVER the lane-0
squeeze the map_op-only host would leave. The second faithful 8-felt Merkle root, deployed. -/
theorem Rfix_heapWrite :
    Rfix 56 = Dregg2.Circuit.Emit.HeapOpenEmit.effHeapWriteV3
        Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
        "dregg-effectvm-heapWrite-v1-rot24-v3-write-heapopen" := rfl

/-- **`Rfix_refusal` — OPTION I: refusal (tag 39) ranges over its OWN DEPLOYED fields-write descriptor.**
`actionTagToPos 39 = 55` and `v3RegistryHeap`'s position-55 entry is the DEPLOYED after-spine membership
descriptor `effFieldsWriteV3 refusalFieldsWriteV3 …` (EXACTLY as heap deploys `effHeapWriteV3`). So
`vkOfRegistry Rfix` / the apex's `StarkSound hash Rfix` quantify over the descriptor a light client
actually verifies, and the refusal rung
(`RotatedKernelRefinementCapFamily.refusalWrite_forces_write8_sat`) discharges its refinement about the
RIGHT one: a satisfying `Satisfied2 (Rfix 39)` FORCES the faithful 8-felt `fieldsWritesTo8` over the FULL
committed BEFORE/AFTER fields-root blocks (`FieldsOpenEmit.effFieldsWriteV3_forces_write8`) — NEVER the
lane-0 squeeze the map_op-only host would leave. The THIRD and LAST faithful 8-felt Merkle root, deployed:
all three named roots (cap · heap · fields) now faithful. -/
theorem Rfix_refusal :
    Rfix 39 = Dregg2.Circuit.Emit.FieldsOpenEmit.effFieldsWriteV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalFieldsWriteV3
        "dregg-effectvm-refusal-v1-rot24-v3-write-fieldsopen" := rfl

/-- **`Rfix_noteSpendInsert` — §J′: noteSpend (tag 27) ranges over its OWN DEPLOYED nullifier-accumulator
INSERT descriptor.** `actionTagToPos 27 = 56` and `v3RegistryHeap`'s position-56 entry is the DEPLOYED
insert-shaped `effAccumInsertV3 nullifierRootGroupCol NULLIFIER_PARAM_COL (prmCol NOTE_VALUE_LO)
noteSpendV3 …` (the insert twin of how heap deploys `effHeapWriteV3`). So the apex's `StarkSound hash
Rfix` quantifies over the descriptor a light client verifies, and the nullifier-insert rung
(`RotatedKernelRefinementCapFamily.nullifierInsert_forces_write8_sat`) discharges its refinement about
the RIGHT one: a satisfying `Satisfied2 (Rfix 27)` FORCES the faithful 8-felt INSERT `accumInserts8`
over the FULL committed BEFORE/AFTER nullifier-root groups (`AccumulatorInsertEmit.effAccumInsertV3_
forces_write8`) — NEVER the lane-0 squeeze, and over the GENUINE sorted fresh-key insert (NOT the
non-fitting update-at-key shape). The FOURTH faithful 8-felt Merkle root, deployed. -/
theorem Rfix_noteSpendInsert :
    Rfix 27 = Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.nullifierRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NULLIFIER_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.param.NOTE_VALUE_LO)
        (some Dregg2.Circuit.Emit.EffectVmEmitNoteSpend.SEL_NOTE_SPEND)
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
        "dregg-effectvm-noteSpend-v1-rot24-v3-insert-heapopen" := rfl

/-- **`Rfix_noteCreateInsert` — §J′: noteCreate (tag 28) ranges over its OWN DEPLOYED commitments-
accumulator INSERT descriptor.** `actionTagToPos 28 = 57`; a satisfying `Satisfied2 (Rfix 28)` FORCES
the faithful 8-felt INSERT over the committed BEFORE/AFTER commitments-root groups
(`RotatedKernelRefinementCapFamily.commitmentsInsert_forces_write8_sat`) — the FIFTH faithful root. -/
theorem Rfix_noteCreateInsert :
    Rfix 28 = Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.commitmentsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.COMMITMENT_KEY_PARAM_COL
        (Dregg2.Circuit.Emit.EffectVmEmit.prmCol
          Dregg2.Circuit.Emit.EffectVmEmitNoteCreate.param.NOTE_VALUE_LO)
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
        "dregg-effectvm-noteCreate-v1-rot24-v3-insert-heapopen" := rfl

/-- **`Rfix_createCellInsert` — §J′: createCell (tag 17) ranges over its OWN DEPLOYED cells-accumulator
INSERT descriptor.** `actionTagToPos 17 = 58`; a satisfying `Satisfied2 (Rfix 17)` FORCES the faithful
8-felt INSERT over the committed BEFORE/AFTER cells-root groups
(`RotatedKernelRefinementCapFamily.cellsInsert_forces_write8_sat`) — the SIXTH faithful root. With this
all six named roots (cap · heap · fields · nullifier · commitments · cells) are deployed faithful: the
three update-at-key writes force `heapWritesTo8`, the three accumulators force `accumInserts8`. -/
theorem Rfix_createCellInsert :
    Rfix 17 = Dregg2.Circuit.Emit.AccumulatorInsertEmit.effAccumInsertV3
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellsRootGroupCol
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.NEW_CELL_KEY_PARAM_COL
        none
        Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
        "dregg-effectvm-createCell-v1-rot24-v3-insert-heapopen" := rfl

/-- **`Rfix_setProgram` — SetProgram (tag 13) ranges over its OWN LIVE descriptor.** `actionTagToPos
13 = 51` and `v3RegistryHeap`'s position-51 entry is the genuine Class-A `setProgramV3` (the program
record-pin, `RotatedKernelRefinementProgram.setProgram_descriptorRefines_sat`). So `Rfix 13` is no
longer the transfer fallback: the SetProgram rung discharges its refinement about the RIGHT descriptor,
and `vkOfRegistry Rfix` now quantifies over the deployed SetProgram descriptor. -/
theorem Rfix_setProgram :
    Rfix 13 = Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setProgramV3 := rfl

/-- **`Rfix_capOpen` — F5: the apex's registry RANGES OVER the LIVE in-circuit authority descriptor.**
The attenuate tag (`12`) re-keys to `v3RegistryCapOpen` position `43` — the LIVE cap-open authority
member `attenuateCapOpenEffV3` (the genuine-submask + decoded-tier descriptor carrying the depth-16
in-circuit cap-membership open). So `vkOfRegistry Rfix` / the apex's `StarkSound hash Rfix` quantify
over the SAME descriptor the deployed prover routes AND the apex authority leg refines
(`transferCapOpenEffV3_authorizes`): the one in-circuit authority gadget is INSIDE the registry the
light-client apex commits, not beside it — and it is the LIVE one, not a pinned twin. -/
theorem Rfix_capOpen : Rfix 12 = Dregg2.Circuit.Emit.CapOpenEmit.attenuateCapOpenEffV3 := rfl

/-- **`Rfix_exercise_capOpen` — exercise (tag 16) RANGES OVER its LIVE cap-open authority descriptor.**
`actionTagToPos 16 = 53` and `v3RegistryHeap`'s position-53 entry is `exerciseCapOpenV3` (the frozen
exercise base + the EFF_EXERCISE depth-16 cap-membership crown). So `Rfix 16` is no longer the bare
authority-free `exerciseV3`: `vkOfRegistry Rfix` / the apex's `StarkSound hash Rfix` now quantify over the
crown-bearing descriptor the SDK route proves through AND the apex hold-gate rung forces
(`RotatedKernelRefinementExerciseAuth.exercise_descriptorRefines_capOpenSat`). The exercise hold-gate is
FORCED in-circuit — the LAST named cap-open residual CLOSED. -/
theorem Rfix_exercise_capOpen :
    Rfix 16 = Dregg2.Circuit.Emit.CapOpenEmit.exerciseCapOpenV3 := rfl

/-! ### The 6 FAN-OUT cap-effect tags route to their LIVE cap-open authority descriptors.

Each cap-authorized fan-out tag re-keys (via `actionTagToPos`) to its `…CapOpenV3` fan-out descriptor
(`v3RegistryCapOpen` positions 36..40), so `vkOfRegistry Rfix` / the apex's `StarkSound hash Rfix` quantify
over the SAME descriptor the deployed prover routes (`cap_open_route_for_run`) AND the apex authority leg
forces (`…CapOpenV3_authorizes` ⟹ `authorizedFacetEffB … (1 <<< n)`). Their authority is FORCED in-circuit
at the effect's OWN bit, no longer riding the toy gate. (`revokeCapability` [position 41] is the SEVENTH
fan-out tag — Lean tag `24` = the wire `sel::REVOKE_CAPABILITY` selector — re-keyed below; its authority is
forced at its OWN bit `1 <<< EFF_REVOKE_CAPABILITY = 1 <<< 3` and its genuine kernel transition is the shared
`RevokeSpec` removeEdge step it lowers to. NO longer unreachable.) The fan-out descriptor is `base +
appendix` (the appendix appends columns and reads NO base column — `effCapOpenV3_satisfiedEff`), so each
tag's VALUE/`ClosedLog` rung — carried `Satisfied2 hash (Rfix <tag>)`-parametrically in
`ClosureFanoutGenuine` — composes verbatim over the re-keyed descriptor (the base columns the readout
reads are unchanged; the trace merely carries the extra appendix columns). -/

/-- delegate (tag 1) routes to the WRITE-FORCING delegate fan-out cap-open (`delegateWriteCapOpenV3`,
position 46) — the cap-tree insert FORCED, guarantee A circuit-bound. -/
theorem Rfix_delegate_capOpen : Rfix 1 = Dregg2.Circuit.Emit.CapOpenEmit.delegateWriteCapOpenV3 := rfl
/-- revoke (tag 2) routes to the WRITE-FORCING revoke fan-out cap-open (`revokeDelegationWriteCapOpenV3`,
position 49 — the SAME write-bearing descriptor tag 14 rides). `.revoke holder t` lowers to the SAME shared
`RevokeSpec`/`removeEdgeCaps` kernel step as `.revokeDelegationA holder t`, so the cap-tree REMOVE is FORCED
on the moving genuine face — guarantee A circuit-bound, no longer the frozen `revokeCapOpenV3`. -/
theorem Rfix_revoke_capOpen :
    Rfix 2 = Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3 := rfl
/-- introduce (tag 10) routes to the WRITE-FORCING introduce fan-out cap-open (`introduceWriteCapOpenV3`,
position 47); the cap-tree insert FORCED on the moving genuine face. -/
theorem Rfix_introduce_capOpen : Rfix 10 = Dregg2.Circuit.Emit.CapOpenEmit.introduceWriteCapOpenV3 := rfl
/-- delegateAtten (tag 11) routes to the WRITE-FORCING delegateAtten fan-out cap-open
(`delegateAttenWriteCapOpenV3`, pos 48) — the insert + `granted ⊑ held` non-amp FORCED. -/
theorem Rfix_grantCap_capOpen : Rfix 11 = Dregg2.Circuit.Emit.CapOpenEmit.delegateAttenWriteCapOpenV3 := rfl
/-- revokeDelegation (tag 14) routes to the WRITE-FORCING revokeDelegation fan-out cap-open
(`revokeDelegationWriteCapOpenV3`, position 49) — the cap-tree REMOVE FORCED on the moving genuine face. -/
theorem Rfix_revokeDelegation_capOpen :
    Rfix 14 = Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3 := rfl
/-- refreshDelegation (tag 55) routes to the WRITE-FORCING refresh fan-out cap-open
(`refreshDelegationWriteCapOpenV3`, position 50) — the DELEGATIONS-tree UPDATE-write FORCED on the moving
genuine face (the `delegRoot_runtime_column_pending` close, guarantee A circuit-forced). -/
theorem Rfix_refreshDelegation_capOpen :
    Rfix 55 = Dregg2.Circuit.Emit.CapOpenEmit.refreshDelegationWriteCapOpenV3 := rfl
/-- revokeCapability (tag 24 = the wire `sel::REVOKE_CAPABILITY`) routes to the LIVE revokeCapability
fan-out cap-open (`revokeCapabilityCapOpenV3`, position 41) — DISTINCT from the revoke(Delegation)
fan-out (pos 39), binding the cap to its OWN bit `EFF_REVOKE_CAPABILITY = 3`. So `vkOfRegistry Rfix`
ranges over the position-41 descriptor the deployed prover routes (`cap_open_route_for_run`) — the
previously-unreachable keystone is now in the apex's registry image. -/
theorem Rfix_revokeCapability_capOpen :
    Rfix 24 = Dregg2.Circuit.Emit.CapOpenEmit.revokeCapabilityCapOpenV3 := rfl
/-- spawn (tag 19) routes to the WRITE-FORCING spawn fan-out cap-open (`spawnWriteCapOpenV3`, position 52)
— the parent→child CAPABILITY HANDOFF cap-tree INSERT FORCED in-circuit (the spawn cap-handoff close),
no longer the frozen-`cap_root` `spawnVmDescriptor2R24`. So `vkOfRegistry Rfix` / the apex's `StarkSound
hash Rfix` quantify over the descriptor that FORCES the handoff — removing the cap-insert gate REDS the
apex spawn rung. -/
theorem Rfix_spawn_capOpen :
    Rfix 19 = Dregg2.Circuit.Emit.CapOpenEmit.spawnWriteCapOpenV3 := rfl

/-! ## §2 — `kstepAll`: the assembled dispatcher arm.

We take the assembled kernel step to be the generic dispatcher arm `CircuitSoundness.dispatchArm`
(`∃ fa, actionTag fa = e ∧ fullActionStep pre fa post`) — the relation the whole-turn apex
`lightclient_turn_unfoolable_forest` is already stated at, and into which every per-effect leaf `Spec`
lowers (`transfer_descriptorRefines_fullActionStep`, `delegate_execFullA`, …). The `e = 0` (transfer)
arm upgrades to the FAITHFUL `dispatchArmFacet` (deployed two-axis authority) via
`RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`. -/

/-- **`kstepAll`** — the assembled kernel step: the generic dispatcher arm at each effect. Its `e = 0`
transfer arm is faithful-upgradable (`dispatchArmFacet`); every effect's leaf `Spec` lowers into it. -/
def kstepAll : EffectIdx → RecChainedState → RecChainedState → Prop := dispatchArm

@[simp] theorem kstepAll_eq (e : EffectIdx) (pre post : RecChainedState) :
    kstepAll e pre post = dispatchArm e pre post := rfl

/-! ## §3 — `EffectDecodeBridge`: the per-effect decode bridge (NAMED, enumerated).

`EffectDecodeBridge S hash R e` is the per-effect refinement rung in APEX SHAPE: it is exactly
`descriptorRefines S hash (R e) (kstepAll e)`. This is the honest residual.

The logical CORE of every effect — `<effect>Encode ⟹ <effect>Spec ⟹ dispatchArm e` — is fully landed
in the `RotatedKernelRefinement*` family (`transfer_descriptorRefines` / `delegate_descriptorRefines` /
`attenuate_descriptorRefines_exact` / `revoke_descriptorRefines` / … through all 36 cohort members + the
8 `setField` slots). What is NOT landed is the bridge from the apex's `StateDecode S pc pre post` (the
LEDGER-ROOT commitment binding) to the per-effect ENCODE predicate each rung consumes (`rotatedEncodes`,
`DelegateCapsTreeEncodes`, `rotatedEncodesIncNonce`, …): the encode carries limb-level column reads, the
cap-tree opening, and the guard fields the commitment surface does NOT commit. Bridging
`StateDecode ⟹ <effect>Encode` is the genuine remaining content — the `WitnessDecodes`-class
decode-extraction, per effect.

We carry it as ONE named per-effect family. NO effect bridges cleanly from `StateDecode` alone (the
ledger root never determines the cap-tree leaf assignment, the per-row columns, or the guard), so all
36 effects (44 indices counting the 8 `setField` slots) are genuine `EffectDecodeBridge` residuals. -/

/-- **`EffectDecodeBridge S hash R e` — the per-effect decode bridge (NAMED).** Exactly the apex-shaped
per-effect refinement `descriptorRefines S hash (R e) (kstepAll e)`: any `Satisfied2` witness of the
descriptor `R e` whose published commitments `StateDecode`-decode to `pre`/`post` forces
`kstepAll e pre post`. The genuine content is the `StateDecode ⟹ <effect>Encode` extraction (the
limb-level decode the LEDGER-root commitment cannot certify); the rung's logical core
(`<effect>Encode ⟹ dispatchArm e`) is landed in `RotatedKernelRefinement*`. Carried, named, not faked. -/
def EffectDecodeBridge (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry) (e : EffectIdx) : Prop :=
  descriptorRefines S hash (R e) (kstepAll e)

@[simp] theorem effectDecodeBridge_eq (S : CommitSurface) (hash : List ℤ → ℤ) (R : Registry)
    (e : EffectIdx) :
    EffectDecodeBridge S hash R e = descriptorRefines S hash (R e) (kstepAll e) := rfl

/-! ## §4 — `hrefinesAll`: assemble the per-effect bridge family into the apex's `∀`.

Given the named per-effect bridge family `(∀ e, EffectDecodeBridge S hash Rfix e)`, the apex's carried
`hrefines : ∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)` is IMMEDIATE — `EffectDecodeBridge` IS
that `descriptorRefines`. This is the enumeration of the previously-opaque `∀`: it is now a per-effect
NAMED family whose content (the `StateDecode ⟹ <effect>Encode` decode bridge) is spelled out. -/

/-- **`hrefinesAll` — the apex's per-effect family, ENUMERATED.** From the named per-effect decode-bridge
family, the registry-wide refinement `∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)` the apex
carries. The previously-opaque `∀` is now an explicit per-effect residual set. -/
theorem hrefinesAll (S : CommitSurface) (hash : List ℤ → ℤ)
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e) :
    ∀ e, descriptorRefines S hash (Rfix e) (kstepAll e) :=
  hbridge

/-! ## §5 — `lightclient_unfoolable_assembled`: the apex at `Rfix`/`kstepAll`/`hrefinesAll`.

The capstone. From a verifying batch against `vkOfRegistry Rfix` + the named floors
(`StarkSound`, `Poseidon2SpongeCR`, the `CommitSurface` CR fields, `WitnessDecodes`) + the ENUMERATED
per-effect decode-bridge family (`∀ e, EffectDecodeBridge S hash Rfix e`), there EXIST decoded endpoints
and a genuine kernel transition `kstepAll pi.effect pre post` whose endpoints commit to the published
`(pi.pre, pi.post)`. The light client RAN NOTHING. -/

theorem lightclient_unfoolable_assembled
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash Rfix S pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  lightclient_unfoolable hash S Rfix hCR kstepAll (hrefinesAll S hash hbridge) pi π hwitdec hacc

/-! ## §6 — the whole-turn capstone (forest shape), at `dispatchArm = kstepAll`.

`kstepAll = dispatchArm`, so the whole-turn apex `lightclient_turn_unfoolable_forest` instantiates at
`Rfix` directly. A verified turn (`TurnDecodeChain` — every step's circuit `Satisfied2`, decoded, seams
agreeing) whose per-step effect indices are identified (`hidx`) + the turn-level endpoint pinning
(`TurnEndpoints`) + the named floors + the ENUMERATED per-effect bridge family yields a GENUINE executor
run `execFullTurnA start acts = some fin` whose endpoints commit to the published turn-level
`(pre, post)`. -/

theorem lightclient_turn_unfoolable_forest_assembled
    (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (hbridge : ∀ e, EffectDecodeBridge S hash Rfix e)
    {start fin : RecChainedState} (c : TurnDecodeChain hash S start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = Rfix e)
    (te : TurnEndpoints hash S c) :
    ∃ (acts : List Dregg2.Exec.TurnExecutorFull.FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = S.commit s.kernel te.tp.turn ∧
      te.tp.pubPost = S.commit s'.kernel te.tp.turn :=
  lightclient_turn_unfoolable_forest hash S Rfix hCR (hrefinesAll S hash hbridge) c hidx te

/-! ## §7 — the FAITHFUL transfer-tier note (the `e = 0` arm upgrade).

`kstepAll 0 = dispatchArm 0` lowers FROM the faithful `dispatchArmFacet` (the deployed two-axis
`authorizedFacetB` authority) by `RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm`. So the
transfer arm of the capstone is upgradable to the deployed authority tier — recorded as a lemma so the
faithful-tier path is explicit, not merely asserted. -/

/-- **`kstepAll_transfer_from_faithful` — the transfer arm lowers from the FAITHFUL facet arm.** A
faithful transfer step (`dispatchArmFacet`, authority via the deployed two-axis `authorizedFacetB`) at
the transfer tag `e = 0`, plus the toy-executor authority side-condition, entails the assembled
`kstepAll 0` arm. The faithful authority is the STRONGER fact; this records that the transfer slot of the
capstone carries the deployed-tier gate. -/
theorem kstepAll_transfer_from_faithful
    (fcaps : Dregg2.Exec.FacetAuthority.FacetCaps)
    (provided : Dregg2.Exec.FacetAuthority.AuthProvided)
    (pre post : RecChainedState)
    (h : RotatedKernelRefinementFacet.dispatchArmFacet fcaps provided 0 pre post)
    (htoy : ∀ tr : Dregg2.Exec.Turn,
      (∃ a, RotatedKernelRefinementFacet.BalanceMovementSpecFacet fcaps provided pre tr a post) →
      Dregg2.Exec.authorizedB pre.kernel.caps tr = true) :
    kstepAll 0 pre post :=
  RotatedKernelRefinementFacet.dispatchArmFacet_to_dispatchArm fcaps provided 0 pre post rfl h htoy

/-! ## §7b — `revokeCapability`: the SEVENTH fan-out tag, REACHABLE + bit-3 authority FORCED.

`revokeCapability` (Lean tag `24` = the wire `sel::REVOKE_CAPABILITY` selector; registry position `41`,
pinned by `Rfix_revokeCapability_capOpen`) is the cap-authorized REVOCATION whose authority binds the OWN
bit `EFF_REVOKE_CAPABILITY = 3` — DISTINCT from the `revoke(Delegation)` fan-out (`EFF_DELEGATION_OPS = 16`,
pos 39). At the KERNEL it shares the `revoke` removeEdge step (`RevokeSpec` — the same shared mutator that
`revoke`/`revokeDelegationA` lower to, `execFullA_revoke_iff_spec`/`execFullA_revokeDelegation_iff_spec`),
so its VALUE leg needs NO new executor action — it lowers to the GENUINE `.revoke` kernel step (`dispatchArm
2`). Only the AUTHORITY bit differs, and THAT is forced in-circuit at bit 3 from the live position-41 cap-open
descriptor (`revokeCapabilityCapOpenV3 = effCapOpenV3 revokeCapabilityBaseV3 … EFF_REVOKE_CAPABILITY`) via the
parametric `effAuthoritySource_authorizes` — exactly the mechanism the other 6 fan-out effects use, NOT the toy
gate, NOT a safely-rejected-but-unreachable keystone.

The reachability is GENUINE (not a fail-closed stub): a verifying `revokeCapability` turn yields a real
`removeEdge` kernel transition AT tag 2 (the shared revoke kind it executes as) with its OWN-bit authority
discharged from the in-circuit cap-open. -/

open Dregg2.Circuit.Spec.AuthorityRevocation (RevokeSpec)
open Dregg2.Circuit.Emit.CapOpenEmit (revokeCapabilityCapOpenV3 revokeCapabilityBaseV3 EFF_REVOKE_CAPABILITY)
open Dregg2.Circuit.RotatedKernelRefinementFacet
  (EffAuthoritySourceCanon effAuthoritySourceCanon_authorizes)
open Dregg2.Exec.FacetAuthority (FacetCaps AuthProvided authorizedFacetEffB)

/-- **`revokeCapabilityArm fcaps provided pre tr post`** — the FAITHFUL `revokeCapability` dispatch arm at
position 41. The VALUE leg is the GENUINE shared revoke kernel step `RevokeSpec` (`removeEdge` on the
`tr.holder`/`tr.t` edge — the very transition `.revoke` executes); the AUTHORITY leg is the deployed two-axis
`authorizedFacetEffB fcaps provided (1 <<< EFF_REVOKE_CAPABILITY)` at the effect's OWN bit `3`. The
revokeCapability turn's `(holder, t)` is read off the carried `tr` (`tr.src`/`tr.dst`), the same `(actor ⇒
src)` edge the cap-open opens. -/
def revokeCapabilityArm (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Dregg2.Exec.Turn) (post : RecChainedState) : Prop :=
  RevokeSpec pre tr.src tr.dst post
  ∧ authorizedFacetEffB fcaps provided (1 <<< EFF_REVOKE_CAPABILITY) tr = true

/-- **`revokeCapabilityArm_authority_forced` — bit-3 authority is FORCED from the in-circuit cap-open.**
From the GENUINE shared revoke value step (`RevokeSpec`) PLUS the position-41 cap-open authority source
(`EffAuthoritySource … revokeCapabilityBaseV3 … EFF_REVOKE_CAPABILITY` — the in-circuit depth-16 cap-membership
open of the live `revokeCapabilityCapOpenV3` descriptor), the faithful `revokeCapabilityArm` holds: the
authority leg is DISCHARGED at the effect's own bit by `effAuthoritySource_authorizes`, no longer riding the
toy gate. -/
theorem revokeCapabilityArm_authority_forced (hash : List ℤ → ℤ)
    (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Dregg2.Exec.Turn) (post : RecChainedState)
    (hval : RevokeSpec pre tr.src tr.dst post)
    (src0 : EffAuthoritySourceCanon hash fcaps provided pre tr
      revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY) :
    revokeCapabilityArm fcaps provided pre tr post :=
  ⟨hval, effAuthoritySourceCanon_authorizes hash fcaps provided pre tr
    revokeCapabilityBaseV3 "dregg-effectvm-revokeCapability-v1-rot24-v3-capopen" EFF_REVOKE_CAPABILITY src0⟩

/-- **`revokeCapabilityArm_to_dispatch` — the faithful arm LOWERS to the GENUINE kernel revoke step.** A
`revokeCapabilityArm` entails the assembled `kstepAll 2` (`= dispatchArm 2`): the shared `RevokeSpec` value
leg IS the `.revoke` arm of `fullActionStep`, so the witness `fa := .revoke tr.src tr.dst` (whose `actionTag`
is `2`) lands a genuine `removeEdge` kernel transition. This makes `revokeCapability` REACHABLE through the
real revoke kind it executes as — its authority bit (3) is the STRONGER fact carried by the arm. -/
theorem revokeCapabilityArm_to_dispatch (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Dregg2.Exec.Turn) (post : RecChainedState)
    (h : revokeCapabilityArm fcaps provided pre tr post) :
    kstepAll 2 pre post := by
  obtain ⟨hval, _hauth⟩ := h
  exact ⟨Dregg2.Exec.TurnExecutorFull.FullActionA.revoke tr.src tr.dst, rfl, hval⟩

/-- **`revokeCapabilityArm_rejects_wrong_facet` (the both-polarity TOOTH).** If the deployed general gate
REJECTS the turn at the revokeCapability bit (`authorizedFacetEffB fcaps provided (1 <<< EFF_REVOKE_CAPABILITY)
tr = false`), then NO post-state is a faithful `revokeCapabilityArm` step — the bit-3 authority leg genuinely
BITES (a cap permitting only `revoke(Delegation)` / a wrong tier / a missing cap cannot discharge a
revokeCapability). The negative polarity of `revokeCapabilityArm_authority_forced`. -/
theorem revokeCapabilityArm_rejects_wrong_facet (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Dregg2.Exec.Turn) (post : RecChainedState)
    (hbad : authorizedFacetEffB fcaps provided (1 <<< EFF_REVOKE_CAPABILITY) tr = false) :
    ¬ revokeCapabilityArm fcaps provided pre tr post := by
  rintro ⟨_, hauth⟩
  rw [hbad] at hauth
  exact Bool.noConfusion hauth

/-- **`revokeCapabilityArm_nonvacuous` — the faithful arm FIRES (value + authority both real).** Given a
GENUINE shared revoke step and a turn the deployed gate ADMITS at bit 3, the arm is inhabited — so the
reachability is not a vacuous fail-closed stub. -/
theorem revokeCapabilityArm_nonvacuous (fcaps : FacetCaps) (provided : AuthProvided)
    (pre : RecChainedState) (tr : Dregg2.Exec.Turn) (post : RecChainedState)
    (hval : RevokeSpec pre tr.src tr.dst post)
    (hauth : authorizedFacetEffB fcaps provided (1 <<< EFF_REVOKE_CAPABILITY) tr = true) :
    revokeCapabilityArm fcaps provided pre tr post :=
  ⟨hval, hauth⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms Rfix_total
#assert_axioms Rfix_transfer
#assert_axioms Rfix_makeSovereign
#assert_axioms Rfix_heapWrite
#assert_axioms Rfix_noteSpendInsert
#assert_axioms Rfix_noteCreateInsert
#assert_axioms Rfix_createCellInsert
#assert_axioms v3RegistryHeap_length
#assert_axioms v3RegistryHeap_heapWrite
#assert_axioms Rfix_capOpen
#assert_axioms Rfix_delegate_capOpen
#assert_axioms Rfix_revoke_capOpen
#assert_axioms Rfix_introduce_capOpen
#assert_axioms Rfix_grantCap_capOpen
#assert_axioms Rfix_revokeDelegation_capOpen
#assert_axioms Rfix_refreshDelegation_capOpen
#assert_axioms Rfix_revokeCapability_capOpen
#assert_axioms hrefinesAll
#assert_axioms lightclient_unfoolable_assembled
#assert_axioms lightclient_turn_unfoolable_forest_assembled
#assert_axioms kstepAll_transfer_from_faithful
#assert_axioms revokeCapabilityArm_authority_forced
#assert_axioms revokeCapabilityArm_to_dispatch
#assert_axioms revokeCapabilityArm_rejects_wrong_facet
#assert_axioms revokeCapabilityArm_nonvacuous

end Dregg2.Circuit.CircuitSoundnessAssembled
