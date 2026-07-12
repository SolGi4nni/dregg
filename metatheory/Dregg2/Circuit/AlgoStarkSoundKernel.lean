/-
# `Dregg2.Circuit.AlgoStarkSoundKernel` — THE CAPSTONE: `AlgoStarkSound hash Rfix` over the REAL
deployed registry, assembled from the per-effect fan-out machinery. "The kernel is STARK-sound
modulo the named floor", as ONE object: `verifyAlgo`-accept at ANY published effect tag ⟹ a genuine
`Satisfied2` witness of THAT tag's DEPLOYED descriptor committing to the published `(pre, post)`.

## The one-line honest claim

`algoStarkSound_kernel` is a REAL `AlgoStarkSound hash Rfix …` term (no `sorry`, no carrier, no
re-assumed `StarkSound`/`AlgoStarkSound`), where `Rfix` is the LIVE registry
(`CircuitSoundnessAssembled.Rfix` — the `actionTag`-keyed total lookup over the 61-member
`v3RegistryHeap`, the SAME registry the soundness apex `lightclient_unfoolable_assembled` and
`vkOfRegistry` quantify over). Its residual `Prop` hypotheses are EXACTLY (per effect tag `e`):

  1. `Poseidon2SpongeCR sponge` + `Poseidon2SpongeCR hash` — the ONE shared commitment-binding
     hash floor (FRI-commitment sponge / constraint-semantics hash; in deployment the same
     Poseidon2 sponge);
  2. `FriLdtExtract … (tr e) (Rfix e)`   — the ∀-d FRI-LDT-@-deployed extraction bundle at the
     DEPLOYED descriptor of tag `e` (`AlgoStarkSoundGeneral`);
  3. `BusModelFamily … (tr e) (Rfix e)`  — the per-used-table LogUp bus models at `Rfix e`;
  4. `MapReconcileFamily … (tr e) (Rfix e)` — the MapOps-AIR reconcile modeler data
     (`AlgoStarkSoundFanoutMemory`); NON-vacuous exactly at the mapOp-carrying deployed members
     (the three §J′ accumulator-insert hosts, tags 17/27/28; heapWrite 56; the refusal
     fields-write 39; spawnWrite 19; factory 18) and VACUOUS at every lookup-shaped member;
  5. `MapTableAssembly … (tr e) (Rfix e)` — the table-assembly faithfulness pair (committed
     memory table EMPTY + committed mapOps table = the gathered `mapLog`); at a lookup-shaped
     member `mapLog (Rfix e) = []`, so this degenerates to exactly the `MemMapFree`
     aux-emptiness pair the mem-free fan-out carries.

This is the UNION of the per-effect residuals of `AlgoStarkSoundFanoutMemFree` /
`AlgoStarkSoundFanoutMemory` — the honest kernel-soundness floor. Everything else (`hood`, `hbus`,
`MainAirAcceptF`, per-descriptor column layout, the Blum memory legs over the empty log) is DERIVED
by the committed ∀-d modelers, per accepting batch, inside `algoStarkSound_of_mapShape` /
`algoStarkSound_of_bricks`. NO `StarkSound` is re-assumed anywhere.

## The dispatch (how the registry-level class is assembled)

`AlgoStarkSound`'s `extract` only ever consults the descriptor at the PUBLISHED tag `pi.effect`, so
the class at `Rfix` follows POINTWISE from the family of slice instances
(`algoStarkSound_of_pointwise`: `(∀ e, AlgoStarkSound hash (fun _ => Rfix e) …) → AlgoStarkSound
hash Rfix …` — definitional, no floor). Per tag, the slice instance is the general per-effect
assembler `AlgoStarkSoundFanoutMemory.algoStarkSound_of_mapShape` AT THE DEPLOYED descriptor
`Rfix e`, fed with THIS FILE's per-deployed-member side conditions (`rfix_sideConditions` — the
case split over the effect tag, one arm per live tag + the transfer fallback for unrouted tags).

## ★ The per-DEPLOYED-member side conditions are the file's real content

The fan-out files' instances are stated at the BARE per-effect faces (`mintV3`, `attenuateV3`,
`noteSpendV3`, …). The DEPLOYED registry member at a tag is that face under ADDITIVE wraps: the
flag-day capacity-floor refuse + rc pins (the 36-member welded cohort), the cap-open authority
appendix + insert/remove/after-spine welds (the cap family), the heap/fields/accumulator
after-spine membership hosts (OPTION I / §J′), the membership-teeth / KEY_COMMIT pins (the v12
carriers). Faking the dispatch by pretending `Rfix e` = the bare face would prove soundness of the
WRONG descriptor — so this file instead EXTENDS each bare face's committed shape fact through
every deployed wrap (each wrap only appends `.base` gates/pins and explicit `.lookup`s — proven
structurally per wrap, `lb_shape`), obtaining `KernelSideConditions (Rfix e)` for every tag, and
lets the SAME general assembler fire at the genuine deployed descriptor. The bare-face shape facts
are REUSED from the committed fan-outs (`burn_sideConditions`, `noteSpendV3_shape`, …), never
re-proven; no constraint list is ever evaluated.

## THE SetFieldDyn FINDING (the brief's "carry SetFieldDyn as a named slot" — NOT NEEDED)

`Rfix`'s tag image does NOT contain the `.memOp`-carrying `setFieldDynV3`/`setFieldDynForcedV3`
(bare-cohort position 19) nor the `.proofBind`-carrying `customV3` (position 18): no `actionTag`
routes to those positions (`actionTagToPos` has no arm for them), and the DEPLOYED setField tag 5
rides the STATIC slot-0 tick face (welded cohort position 28). So the registry capstone needs NO
SetFieldDyn slot and NO higher-order-pole LogUp leg: the memOp/proofBind families are OUTSIDE the
deployed registry's dispatch image. The falsifier `setFieldDynV3_not_mapShape` proves the shape
classification would genuinely FAIL there — the exclusion is honest, not definitional luck.

## Non-vacuity

The load-bearing premises fire and bite: `AlgoStarkSoundInstance.mainAirAccept_respecting` /
`mainAirAccept_biting` (the FRI-side extraction conjunct is inhabited on honest data and
falsifiable on a tampered gate), `AlgoStarkSoundFanoutMemFree.attenuateV3_has_lookup` (a GENUINE
non-arith lookup is routed through the bus modeler at the deployed attenuate base), and
`setFieldDynV3_not_mapShape` here (the shape fact is falsifiable). The kernel object concludes
`Satisfied2 hash (Rfix pi.effect) …` — the SAME rich predicate every per-effect refinement rung
consumes — so it composes directly under the apex.

## Discipline

Sorry-free; no `decide`/`Fintype`/`Finset.univ` over field-sized objects; BabyBear arithmetic never
computed (every proof is constructor-shape structural). NEW file; imports read-only; builds
targeted (`lake build Dregg2.Circuit.AlgoStarkSoundKernel`).
-/
import Dregg2.Circuit.AlgoStarkSoundFanoutMemFree
import Dregg2.Circuit.AlgoStarkSoundFanoutMemory
import Dregg2.Circuit.CircuitSoundnessAssembled

namespace Dregg2.Circuit.AlgoStarkSoundKernel

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriChecks FriCore FieldArith fullChecks)
open Dregg2.Circuit.CircuitSoundness (Registry BatchPublicInputs BatchProof EffectIdx)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 Lookup MapOp VmTrace)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral (FriLdtExtract BusModelFamily)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemFree
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory
  (MapReconcileFamily MapTableAssembly algoStarkSound_of_mapShape noteSpendV3_shape
   noteCreateV3_shape createCellV3_shape factoryV3_shape spawnWriteV3_shape
   refusalFieldsWriteV3_shape heapWriteV3_shape)
open Dregg2.Circuit.CircuitSoundnessAssembled (Rfix transferDescr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.Emit.EffectVmEmitV2 (fieldWriteOp)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (setFieldDynV3)
open Dregg2.Circuit.Emit.CapOpenEmit
  (capOpenConstraintsEff afterSpineConstraints afterCapRootWelds beforeCapRootWelds)
open Dregg2.Circuit.Emit.HeapOpenEmit (heapOpenConstraints afterSpineConstraintsH)
open Dregg2.Circuit.Emit.FieldsOpenEmit (fieldsOpenConstraints afterSpineConstraintsF)
open Dregg2.Circuit.Emit.AccumulatorInsertEmit (accumInsertConstraints)
open Dregg2.Deos.BareCohortFloorRefuseDeployed (deployedRefuseGates gentianDeployedBareRefuse)
open Dregg2.Circuit.Emit.CarrierOctetGates (keyCommitConstraints)

set_option autoImplicit false

/-! ## §0 — THE POINTWISE COMPOSITION: `AlgoStarkSound` at every slice ⟹ at the registry.

`extract` only consults `R pi.effect`, and the slice registry `fun _ => R e` agrees with `R` at
`e` DEFINITIONALLY, so the registry-level class is the pointwise family — no floor, no dispatch
residue. This is the glue that turns the per-effect fan-out into the kernel object. -/

/-- **`algoStarkSound_of_pointwise`** — the registry-level class from the family of per-tag slice
instances. Purely definitional (beta at the published tag); NO hypothesis beyond the family. -/
theorem algoStarkSound_of_pointwise
    (hash : List ℤ → ℤ) (R : Registry)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (checks : FriChecks ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (h : ∀ e : EffectIdx, AlgoStarkSound hash (fun _ => R e) perm RATE toNat params vk checks
        initState logN view) :
    AlgoStarkSound hash R perm RATE toNat params vk checks initState logN view :=
  ⟨fun pi π hacc => (h pi.effect).extract pi π hacc⟩

/-! ## §1 — the shape language: `MapShape` (every non-arith constraint is a `.lookup` or a
`.mapOp`) + the closure bricks. `MapShape` is EXACTLY the `hshape` slot of the general per-effect
assembler `algoStarkSound_of_mapShape`; `LookupShaped` (the mem-free fan-out's shape) lifts into
it. No constraint list is ever evaluated: everything is constructor-shape structural. -/

/-- The lookup-or-mapOp non-arith shape — the `hshape` input of `algoStarkSound_of_mapShape`. -/
abbrev MapShape (cs : List VmConstraint2) : Prop :=
  ∀ c ∈ cs, ¬ isArith c →
    (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m)

/-- Every all-lookup (mem-free) shape is a fortiori lookup-or-mapOp. -/
theorem mapShape_of_lookupShaped {cs : List VmConstraint2} (h : LookupShaped cs) :
    MapShape cs := fun c hc hA => Or.inl (h c hc hA)

/-- `MapShape` is closed under append. -/
theorem mapShape_append {cs₁ cs₂ : List VmConstraint2}
    (h₁ : MapShape cs₁) (h₂ : MapShape cs₂) : MapShape (cs₁ ++ cs₂) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

/-- The wrap-peeling workhorse: a shaped core stays shaped under an appended all-lookup/arith
block (every deployed wrap appends only `.base` gates/pins and explicit `.lookup`s). -/
theorem mapShape_append_lookupShaped {cs₁ cs₂ : List VmConstraint2}
    (h₁ : MapShape cs₁) (h₂ : LookupShaped cs₂) : MapShape (cs₁ ++ cs₂) :=
  mapShape_append h₁ (mapShape_of_lookupShaped h₂)

/-- Cons-brick: a `.lookup` head. -/
theorem lookupShaped_lookup_cons (l : Lookup) {cs : List VmConstraint2}
    (h : LookupShaped cs) : LookupShaped (VmConstraint2.lookup l :: cs) := by
  intro c hc hA
  cases hc with
  | head => exact ⟨l, rfl⟩
  | tail _ hc => exact h c hc hA

/-- Cons-brick: a `.base` head (arith — never reaches the non-arith arm). -/
theorem lookupShaped_base_cons (c₀ : VmConstraint) {cs : List VmConstraint2}
    (h : LookupShaped cs) : LookupShaped (VmConstraint2.base c₀ :: cs) := by
  intro c hc hA
  cases hc with
  | head => exact absurd trivial hA
  | tail _ hc => exact h c hc hA

/-- `lb_shape` — discharge `LookupShaped` for a CONCRETE appendix list by whnf cons-recursion:
every deployed appendix (cap-open / after-spine / refuse / heap / fields / accumulator /
key-commit) is a closed cons/append/map spine of `.base`s and `.lookup`s, so the two cons-bricks
walk it head-by-head (the heads reduce definitionally; payloads are never evaluated — this is
list-STRUCTURE recursion, no field arithmetic, no `decide`). -/
macro "lb_shape" : tactic =>
  `(tactic| repeat first
      | exact lookupShaped_nil
      | apply lookupShaped_lookup_cons
      | apply lookupShaped_base_cons)

/-! ## §2 — the DEPLOYED-WRAP shape receipts: every appendix a registry wrap appends is
`LookupShaped`. One lemma per named appendix; each is `lb_shape` (structure-only). -/

/-- The effect-general cap-open authority appendix (1 leaf lookup + 16 node lookups + 64 boolean/
pin/recon gates) is lookup-shaped. -/
theorem lookupShaped_capOpenConstraintsEff (w n : Nat) :
    LookupShaped (capOpenConstraintsEff w n) := by lb_shape

/-- The cap after-spine write appendix (after leaf/node lookups + root pins + leaf/root welds +
key bind) is lookup-shaped. -/
theorem lookupShaped_afterSpineConstraints (w : Nat) :
    LookupShaped (afterSpineConstraints w) := by lb_shape

/-- The 8 AFTER cap-root welds (the INSERT-shaped keystone appendix) are all-arith. -/
theorem lookupShaped_afterCapRootWelds (w : Nat) :
    LookupShaped (afterCapRootWelds w) := by lb_shape

/-- The 8 BEFORE cap-root welds (the REMOVE-shaped keystone appendix) are all-arith. -/
theorem lookupShaped_beforeCapRootWelds (w : Nat) :
    LookupShaped (beforeCapRootWelds w) := by lb_shape

/-- The flag-day three-block capacity-floor refuse weld (39 decode/OR-fold/refuse gates) is
all-arith. -/
theorem lookupShaped_deployedRefuseGates (auxBase : Nat) :
    LookupShaped (deployedRefuseGates auxBase) := by lb_shape

/-- The heap-open read appendix (leaf lookup + node lookups + dir/root-pin gates). -/
theorem lookupShaped_heapOpenConstraints (w : Nat) :
    LookupShaped (heapOpenConstraints w) := by lb_shape

/-- The heap after-spine write appendix. -/
theorem lookupShaped_afterSpineConstraintsH (w : Nat) :
    LookupShaped (afterSpineConstraintsH w) := by lb_shape

/-- The fields-open read appendix. -/
theorem lookupShaped_fieldsOpenConstraints (w : Nat) :
    LookupShaped (fieldsOpenConstraints w) := by lb_shape

/-- The fields after-spine write appendix. -/
theorem lookupShaped_afterSpineConstraintsF (w : Nat) :
    LookupShaped (afterSpineConstraintsF w) := by lb_shape

/-- The §J′ accumulator-insert appendix (8 AFTER-group welds + the selector-gated key/value
binds) is all-arith. -/
theorem lookupShaped_accumInsertConstraints (groupCol : Nat → Fin 8 → Nat)
    (keyCol valueCol : Nat) (sel : Option Nat) (w : Nat) :
    LookupShaped (accumInsertConstraints groupCol keyCol valueCol sel w) := by lb_shape

/-- The sovereign KEY_COMMIT chip-compress appendix (4 chip lookups + 4 teeth-eq gates). -/
theorem lookupShaped_keyCommitConstraints (blockBase octetBase dgBase teethPiLo : Nat) :
    LookupShaped (keyCommitConstraints blockBase octetBase dgBase teethPiLo) := by lb_shape

/-! ## §3 — the per-DEPLOYED-member side conditions.

`KernelSideConditions (Rfix e)` is the WHOLE per-tag obligation of the general assembler: the two
graduated column facts (`rfl` — every wrap is a `{ base with … }` update that inherits
`hashSites`/`ranges`) and the lookup-or-mapOp shape (the bare face's committed fan-out shape fact,
extended through the deployed wraps by the §2 receipts). -/

/-- The whole per-tag obligation of `algoStarkSound_of_mapShape` at a deployed member. -/
abbrev KernelSideConditions (d : EffectVmDescriptor2) : Prop :=
  (d.hashSites = [] ∧ d.ranges = []) ∧ MapShape d.constraints

/-- The welded-cohort lift: a mem-free bare face's fan-out package extends through the flag-day
weld (`bare ++ refuse-gates ++ rc-pins`). -/
theorem kernelSide_refused (d : EffectVmDescriptor2) (hside : MemFreeSideConditions d) :
    KernelSideConditions
      (Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withDfaRcPins (gentianDeployedBareRefuse d)) :=
  ⟨⟨hside.1.1, hside.1.2⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped (mapShape_of_lookupShaped hside.2)
        (lookupShaped_deployedRefuseGates _))
      (lookupShaped_base_map _ _)⟩

-- ★ the 32 live tags (31 distinct deployed members — tags 2 and 14 share the revoke write
-- descriptor) + the total-function transfer fallback. Each receipt names its wrap chain.

/-- tag 0 — the v12 membership-teeth transfer (`transferV3Membership` = transfer ++ rc ++ 2 teeth
pins). -/
theorem side_transfer : KernelSideConditions (Rfix 0) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped (mapShape_of_lookupShaped (lookupShaped_graduateV1 _))
        (lookupShaped_base_map _ _))
      (lookupShaped_base_map _ _)⟩

/-- tag 1 — delegate on the INSERT-shaped cap-write keystone
(`grantCapWriteV3 ++ cap-open appendix ++ AFTER welds ++ selector`). -/
theorem side_delegate : KernelSideConditions (Rfix 1) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped (mapShape_of_lookupShaped grantCap_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterCapRootWelds _))
      (lookupShaped_base_single _)⟩

/-- tags 2 + 14 — revoke(Delegation) on the REMOVE-shaped cap-write keystone
(`revokeDelegationWriteV3 ++ cap-open appendix ++ BEFORE welds ++ selector`). -/
theorem side_revokeDelegationWrite : KernelSideConditions (Rfix 2) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped
          (mapShape_of_lookupShaped revokeDelegation_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_beforeCapRootWelds _))
      (lookupShaped_base_single _)⟩

/-- tag 3 — the dedicated-selector supply mint (`supplyMintV3`, the fan-out member verbatim). -/
theorem side_supplyMint : KernelSideConditions (Rfix 3) :=
  ⟨⟨rfl, rfl⟩, mapShape_of_lookupShaped supplyMint_sideConditions.2⟩

/-- tag 4 — burn, flag-day welded. -/
theorem side_burn : KernelSideConditions (Rfix 4) :=
  kernelSide_refused _ burn_sideConditions

/-- tag 5 — setField (the DEPLOYED static slot-0 tick face), flag-day welded. -/
theorem side_setField : KernelSideConditions (Rfix 5) :=
  kernelSide_refused _ (setFieldStatic_sideConditions 0)

/-- tag 6 — emitEvent, flag-day welded. -/
theorem side_emitEvent : KernelSideConditions (Rfix 6) :=
  kernelSide_refused _ emitEvent_sideConditions

/-- tag 7 — incrementNonce, flag-day welded. -/
theorem side_incrementNonce : KernelSideConditions (Rfix 7) :=
  kernelSide_refused _ incrementNonce_sideConditions

/-- tag 8 — setPermissions, flag-day welded. -/
theorem side_setPermissions : KernelSideConditions (Rfix 8) :=
  kernelSide_refused _ setPermissions_sideConditions

/-- tag 9 — setVK, flag-day welded. -/
theorem side_setVK : KernelSideConditions (Rfix 9) :=
  kernelSide_refused _ setVK_sideConditions

/-- tag 10 — introduce on the INSERT-shaped cap-write keystone. -/
theorem side_introduce : KernelSideConditions (Rfix 10) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped (mapShape_of_lookupShaped introduce_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterCapRootWelds _))
      (lookupShaped_base_single _)⟩

/-- tag 11 — delegateAtten on the INSERT-shaped cap-write keystone (the base keeps the
`granted ⊑ held` submask lookup — routed through the bus modeler). -/
theorem side_delegateAtten : KernelSideConditions (Rfix 11) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped (mapShape_of_lookupShaped delegateAtten_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterCapRootWelds _))
      (lookupShaped_base_single _)⟩

/-- tag 12 — the LIVE attenuate cap-open (`attenuateV3 ++ cap-open appendix ++ after-spine ++
selector`). -/
theorem side_attenuate : KernelSideConditions (Rfix 12) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped (mapShape_of_lookupShaped attenuate_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterSpineConstraints _))
      (lookupShaped_base_single _)⟩

/-- tag 13 — setProgram (the record-pin program-install member verbatim). -/
theorem side_setProgram : KernelSideConditions (Rfix 13) :=
  ⟨⟨rfl, rfl⟩, mapShape_of_lookupShaped setProgram_sideConditions.2⟩

/-- tag 16 — exercise-via-capability (the frozen exercise base + the authority appendix +
selector; an AUTHORITY-READ member, no write spine). -/
theorem side_exercise : KernelSideConditions (Rfix 16) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped (mapShape_of_lookupShaped exercise_sideConditions.2)
        (lookupShaped_capOpenConstraintsEff _ _))
      (lookupShaped_base_single _)⟩

/-- tag 17 — createCell on the §J′ cells-accumulator INSERT host
(`createCellV3 ++ heap-open read ++ insert appendix`); the grow-gate map-ops ride the core. -/
theorem side_createCell : KernelSideConditions (Rfix 17) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped createCellV3_shape (lookupShaped_heapOpenConstraints _))
      (lookupShaped_accumInsertConstraints _ _ _ _ _)⟩

/-- tag 18 — createCellFromFactory (the STEP-3 carriers member: `factoryV3` + the two after-octet
pin cohorts), flag-day welded; the accounts grow-gate map-ops ride the core. -/
theorem side_factory : KernelSideConditions (Rfix 18) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped
          (mapShape_append_lookupShaped factoryV3_shape (lookupShaped_base_map _ _))
          (lookupShaped_base_map _ _))
        (lookupShaped_deployedRefuseGates _))
      (lookupShaped_base_map _ _)⟩

/-- tag 19 — spawn on the INSERT-shaped cap-write keystone over the cap-write rotation
(`spawnWriteV3` keeps the cells grow-gate map-op pair). -/
theorem side_spawn : KernelSideConditions (Rfix 19) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped spawnWriteV3_shape
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterCapRootWelds _))
      (lookupShaped_base_single _)⟩

/-- tag 20 — bridgeMint (the felt mint-hash member `mintV3BridgeHash`), flag-day welded. -/
theorem side_bridgeMint : KernelSideConditions (Rfix 20) :=
  kernelSide_refused _ bridgeMint_sideConditions

/-- tag 24 — revokeCapability-via-cap (the rotated base + the authority appendix + selector). -/
theorem side_revokeCapability : KernelSideConditions (Rfix 24) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped (mapShape_of_lookupShaped (lookupShaped_graduateV1 _))
        (lookupShaped_capOpenConstraintsEff _ _))
      (lookupShaped_base_single _)⟩

/-- tag 27 — noteSpend on the §J′ nullifier-accumulator INSERT host (the freshness `.absent` +
set-insert `.insert` ride the core). -/
theorem side_noteSpend : KernelSideConditions (Rfix 27) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped noteSpendV3_shape (lookupShaped_heapOpenConstraints _))
      (lookupShaped_accumInsertConstraints _ _ _ _ _)⟩

/-- tag 28 — noteCreate on the §J′ commitments-accumulator INSERT host. -/
theorem side_noteCreate : KernelSideConditions (Rfix 28) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped noteCreateV3_shape (lookupShaped_heapOpenConstraints _))
      (lookupShaped_accumInsertConstraints _ _ _ _ _)⟩

/-- tag 38 — the v12 DEPLOYED sovereign (`makeSovereignV3 ++ rc ++ 4 teeth pins ++ the KEY_COMMIT
chip-compress appendix`). -/
theorem side_makeSovereign : KernelSideConditions (Rfix 38) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped (mapShape_of_lookupShaped makeSovereign_sideConditions.2)
          (lookupShaped_base_map _ _))
        (lookupShaped_base_map _ _))
      (lookupShaped_keyCommitConstraints _ _ _ _)⟩

/-- tag 39 — refusal on the OPTION-I fields-write host
(`refusalFieldsWriteV3 ++ fields-open read ++ fields after-spine`); the audit-slot `.write`
map-op rides the core. -/
theorem side_refusal : KernelSideConditions (Rfix 39) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped refusalFieldsWriteV3_shape
        (lookupShaped_fieldsOpenConstraints _))
      (lookupShaped_afterSpineConstraintsF _)⟩

/-- tag 40 — receiptArchive, flag-day welded. -/
theorem side_receiptArchive : KernelSideConditions (Rfix 40) :=
  kernelSide_refused _ receiptArchive_sideConditions

/-- tag 47 — pipelinedSend, flag-day welded. -/
theorem side_pipelinedSend : KernelSideConditions (Rfix 47) :=
  kernelSide_refused _ pipelinedSend_sideConditions

/-- tag 52 — cellSeal, flag-day welded. -/
theorem side_cellSeal : KernelSideConditions (Rfix 52) :=
  kernelSide_refused _ cellSeal_sideConditions

/-- tag 53 — cellUnseal, flag-day welded. -/
theorem side_cellUnseal : KernelSideConditions (Rfix 53) :=
  kernelSide_refused _ cellUnseal_sideConditions

/-- tag 54 — cellDestroy, flag-day welded. -/
theorem side_cellDestroy : KernelSideConditions (Rfix 54) :=
  kernelSide_refused _ cellDestroy_sideConditions

/-- tag 55 — refreshDelegation on the cap-write after-spine keystone
(`refreshDelegationWriteV3 ++ cap-open appendix ++ after-spine ++ selector`). -/
theorem side_refreshDelegation : KernelSideConditions (Rfix 55) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped
        (mapShape_append_lookupShaped
          (mapShape_of_lookupShaped refreshDelegation_sideConditions.2)
          (lookupShaped_capOpenConstraintsEff _ _))
        (lookupShaped_afterSpineConstraints _))
      (lookupShaped_base_single _)⟩

/-- tag 56 — heapWrite on the OPTION-I heap-write host
(`heapWriteV3 ++ heap-open read ++ heap after-spine`); the splice `.write` rides the core. -/
theorem side_heapWrite : KernelSideConditions (Rfix 56) :=
  ⟨⟨rfl, rfl⟩,
    mapShape_append_lookupShaped
      (mapShape_append_lookupShaped heapWriteV3_shape (lookupShaped_heapOpenConstraints _))
      (lookupShaped_afterSpineConstraintsH _)⟩

/-- The unrouted-tag fallback (`Rfix` is total: every tag without its own deployed member
resolves to the bare transfer descriptor). -/
theorem side_fallback : KernelSideConditions transferDescr :=
  ⟨⟨rfl, rfl⟩,
    mapShape_of_lookupShaped Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup⟩

/-! ## §4 — ★ THE EFFECT-TAG CASE SPLIT: `KernelSideConditions (Rfix e)` for EVERY tag.

One arm per live `actionTag` (32 routed tags), the transfer fallback for every unrouted literal
below the match horizon, and the `e + 57` tail for the off-range fallback (all three fallback
classes reduce to `transferDescr` definitionally). This IS the per-effect dispatch of the
capstone: each arm lands on ITS deployed descriptor's receipt. -/

theorem rfix_sideConditions : ∀ e : EffectIdx, KernelSideConditions (Rfix e)
  | 0 => side_transfer
  | 1 => side_delegate
  | 2 => side_revokeDelegationWrite
  | 3 => side_supplyMint
  | 4 => side_burn
  | 5 => side_setField
  | 6 => side_emitEvent
  | 7 => side_incrementNonce
  | 8 => side_setPermissions
  | 9 => side_setVK
  | 10 => side_introduce
  | 11 => side_delegateAtten
  | 12 => side_attenuate
  | 13 => side_setProgram
  | 14 => side_revokeDelegationWrite
  | 15 => side_fallback
  | 16 => side_exercise
  | 17 => side_createCell
  | 18 => side_factory
  | 19 => side_spawn
  | 20 => side_bridgeMint
  | 21 | 22 | 23 => side_fallback
  | 24 => side_revokeCapability
  | 25 | 26 => side_fallback
  | 27 => side_noteSpend
  | 28 => side_noteCreate
  | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 => side_fallback
  | 38 => side_makeSovereign
  | 39 => side_refusal
  | 40 => side_receiptArchive
  | 41 | 42 | 43 | 44 | 45 | 46 => side_fallback
  | 47 => side_pipelinedSend
  | 48 | 49 | 50 | 51 => side_fallback
  | 52 => side_cellSeal
  | 53 => side_cellUnseal
  | 54 => side_cellDestroy
  | 55 => side_refreshDelegation
  | 56 => side_heapWrite
  | _ + 57 => side_fallback

/-! ## §5 — ★★ THE CAPSTONE: `AlgoStarkSound hash Rfix` — the kernel is STARK-sound modulo the
named floor. -/

/-- **`algoStarkSound_kernel` — kernel STARK-soundness over the REAL registry.** From EXACTLY the
named floor — {`Poseidon2SpongeCR` ×2} + per tag {`FriLdtExtract (Rfix e)`, `BusModelFamily
(Rfix e)`, `MapReconcileFamily (Rfix e)`, `MapTableAssembly (Rfix e)`} — the FULL
`AlgoStarkSound hash Rfix …`: every `verifyAlgo`-accepted batch at ANY published effect tag yields
a genuine `Satisfied2 hash (Rfix pi.effect) …` witness whose published commitments are
`pi.toPublished`. Assembled POINTWISE from the general per-effect assembler at each tag's DEPLOYED
descriptor (`rfix_sideConditions` supplies the per-member shape; the modelers derive
`MainAirAcceptF`/`hood`/`hbus` per accepting batch). The per-tag extractor is `tr e` (each
effect's FRI extraction bundle names ITS extracted trace). NO `sorry`, NO carrier, NO re-assumed
`StarkSound`/`AlgoStarkSound`, NO `verifyBatch`. -/
theorem algoStarkSound_kernel {F : Type*} [Field F] [DecidableEq F]
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : EffectIdx → BatchPublicInputs → BatchProof → VmTrace)
    (hfri : ∀ e : EffectIdx, FriLdtExtract sponge perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    (hbusF : ∀ e : EffectIdx, BusModelFamily fp embed perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    (hrec : ∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    (hasm : ∀ e : EffectIdx, MapTableAssembly perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e)) :
    AlgoStarkSound hash Rfix perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_pointwise hash Rfix perm RATE toNat params vk
    (fullChecks core A toNat params.powBits) initState logN view
    (fun e =>
      algoStarkSound_of_mapShape (Rfix e) sponge hCR hash hCRh fp embed perm RATE toNat
        params vk core A initState logN view (tr e)
        (rfix_sideConditions e).2
        (rfix_sideConditions e).1.1 (rfix_sideConditions e).1.2
        (hfri e) (hbusF e) (hrec e) (hasm e))

/-! ## §6 — TEETH: the classification and the load-bearing premises are genuine.

  * The FRI-side extraction conjunct FIRES on honest data and BITES on a tampered gate —
    `AlgoStarkSoundInstance.mainAirAccept_respecting` / `mainAirAccept_biting` (committed with
    the shared assembler; the field migration did not vacuate the premise).
  * The bus residual is genuinely consumed — `AlgoStarkSoundFanoutMemFree.attenuateV3_has_lookup`
    exhibits a REAL non-arith lookup (the `granted ⊑ held` non-amplification tooth) inside the
    deployed attenuate base this capstone dispatches to at tag 12.
  * The shape classification is FALSIFIABLE (below): the `.memOp`-carrying `setFieldDynV3` fails
    `MapShape` — so `rfix_sideConditions` is a genuine per-member proof, not a tautology, and the
    honest reason the kernel needs no SetFieldDyn slot is that `Rfix`'s tag image EXCLUDES the
    memOp/proofBind members (bare-cohort positions 18/19 are unrouted; deployed setField rides
    the static tick face). -/

/-- **The falsifier** — `MapShape` is FALSE for the `.memOp`-carrying `setFieldDynV3` (its Blum
write op is non-arith and neither a lookup nor a mapOp). A memory-disciplined (`.memOp`) or
proof-binding descriptor CANNOT be pushed through this file's route — the SetFieldDyn family is
excluded by PROOF, not by omission. -/
theorem setFieldDynV3_not_mapShape : ¬ MapShape setFieldDynV3.constraints := by
  intro h
  have hmem : VmConstraint2.memOp fieldWriteOp ∈ setFieldDynV3.constraints :=
    List.mem_append_right _ (List.Mem.head _)
  rcases h _ hmem (fun hA => hA) with ⟨l, hl⟩ | ⟨m, hm⟩
  · exact nomatch hl
  · exact nomatch hm

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms algoStarkSound_of_pointwise
#assert_axioms rfix_sideConditions
#assert_axioms algoStarkSound_kernel
#assert_axioms setFieldDynV3_not_mapShape

end Dregg2.Circuit.AlgoStarkSoundKernel
