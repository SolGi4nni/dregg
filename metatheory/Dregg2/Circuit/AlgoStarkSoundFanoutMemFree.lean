/-
# `Dregg2.Circuit.AlgoStarkSoundFanoutMemFree` — THE MEM-FREE KERNEL FAN-OUT:
`algoStarkSound_<effect>` for every pure-graduated (memory/map-op-free) registry effect, each ONE
invocation of the general assembler `AlgoStarkSoundGeneral.algoStarkSound_of_memoryFree`.

## What this file is (the one-line honest claim)

Per mem-free effect `E` with deployed descriptor `dE`, `algoStarkSound_<E>` proves the full
`AlgoStarkSound hash (fun _ => dE) …` from EXACTLY the named floor

  { `Poseidon2SpongeCR sponge`, `FriLdtExtract … dE`, `BusModelFamily … dE` } + `MemMapFree`

(the same residual as the lever's `algoStarkSound_transferV3_ofBusModels` — the two
aux-table-emptiness assembly facts `FriLdtExtractV3` carries verbatim ride as `MemMapFree`).
NO `hood`, NO `hbus`, NO `MainAirAcceptF`, NO per-descriptor column layout is assumed anywhere:
those are DERIVED by the ∀-d modelers inside the general assembler.

## The per-effect obligation IS mechanical (this file is the receipt)

What remains per effect is the `MemFreeSideConditions` triple of
`transferV3_sideConditions_mechanical` — `hashSites = []` ∧ `ranges = []` (both `rfl`) plus the
all-lookup non-arith shape — and the shape discharges STRUCTURALLY, never by evaluating a
descriptor's constraint list:

  * every deployed mem-free member is `graduateV1 <rotated face>` possibly wrapped by additive
    combinators (`withSelectorGate` / `withDfaRcPins`-family pins / `withRecordPin8Headroom2` /
    `withPermsVK8Weld` / `withMintHashPin` / `v3OfWith* extras`), and every wrap only APPENDS
    `.base` constraints or explicit `.lookup`s;
  * `lookupShaped_graduateV1` (the ∀-face generalization of `AirLegsDischarged.hbus_is_lookup`,
    via the committed `constraints_graduateV1_shapes`) handles the graduated core, and the four
    append bricks (`lookupShaped_append`/`_nil`/`_base_*`/`_lookup_single`) handle every wrap.

Descriptor choice matches the template's convention: the PER-EFFECT deployed face (`mintV3`,
`attenuateV3`, `setPermsV3`, … — the `v3RegistryBare`/`v3RegistryHeap`-tail bases), exactly as the
lever instantiates `transferV3` (the bare transfer face, not the rc/teeth-pinned `Rfix 0` wrap —
the additive registry wraps are other lanes' peels).

## COVERED (26 effect instances + transferV3 already in the lever)

mint · bridgeMint (`mintV3BridgeHash`) · supplyMint · burn · incrementNonce · emitEvent ·
exercise · pipelinedSend · delegate · delegateAtten · attenuate · grantCap · introduce (write
face) · revokeCapability · revokeDelegation (write face) · refreshDelegation (write face) ·
makeSovereign · setPermissions · setVK · setProgram · cellSeal · cellUnseal · cellDestroy ·
receiptArchive · transferFee · setField-static (∀ slot : Fin 8 — 8 registry members in one
parametric instance).

## REPORTED — NOT mem-free (no instance faked; the falsifier tooth proves the honesty)

  * `setFieldDynV3` / `setFieldDynForcedV3` — carry 2 `.memOp`s (the Blum write→read transport);
    `setFieldDynV3_not_lookupShaped` PROVES the shape fact is FALSE for it.
  * `spawnWriteV3` — keeps its 2 cells-grow-gate `.mapOp`s.
  * `noteSpendV3` / `noteCreateV3` / `createCellV3` / `factoryV3` / `heapWriteV3` and the
    deployed insert/write hosts (`effAccumInsertV3`/`effHeapWriteV3`/`effFieldsWriteV3`, hence
    the deployed refusal) — the memory-touching family; they take the MEMORY-LEGS route
    (`algoStarkSound_of_memoryLegs`), not this file's.
  * `customV3` — carries a `.proofBind` (non-arith, non-lookup): mem-free in the table sense but
    NOT lookup-shaped; its non-arith arm needs the proof-binding leg, so it is NOT in this fan-out.
  * noop — has no own registry descriptor (pads ride `sel[NOOP]` inside other members); nothing
    to instantiate.

## Non-vacuity

The `AlgoStarkSound` content itself is the lever's (same derivation; `mainAirAccept_respecting` /
`mainAirAccept_biting` exhibit the load-bearing premise firing and biting). Here additionally:
`attenuateV3_has_lookup` / `delegateAttenV3_has_lookup` exhibit a GENUINE non-arith `.lookup`
routed through the bus modeler (the shape fact is not vacuously true), and
`setFieldDynV3_not_lookupShaped` exhibits it FALSE on a memory-ful descriptor (not a tautology).

## Discipline

Sorry-free; no carrier; no `decide`/`Fintype`/`Finset.univ` over field-sized objects — every shape
proof is structural (constructor-shape recursion over the emission combinators; no constraint list
is ever evaluated). BabyBear arithmetic never computed. NEW file; imports read-only; builds
targeted (`lake build Dregg2.Circuit.AlgoStarkSoundFanoutMemFree`).
-/
import Dregg2.Circuit.AlgoStarkSoundGeneral

namespace Dregg2.Circuit.AlgoStarkSoundFanoutMemFree

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2 Lookup)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (FriLdtExtract BusModelFamily MemMapFree algoStarkSound_of_memoryFree)
open Dregg2.Circuit.Emit.EffectVmEmit (EffectVmDescriptor VmConstraint)
open Dregg2.Circuit.Emit.EffectVmEmitV2
  (graduateV1 constraints_graduateV1_shapes submaskLookup fieldWriteOp)
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3
  (v3Of v3OfFrozen withSelectorGate setFieldTickFace mintV3 supplyMintV3 mintV3BridgeHash
   attenuateV3 revokeCapabilityV3 delegateV3 delegateAttenV3 grantCapWriteV3 introduceWriteV3
   revokeDelegationWriteV3 refreshDelegationWriteV3 setFieldDynV3 makeSovereignV3 setPermsV3
   setVKV3 setProgramV3 cellSealV3 cellUnsealV3 cellDestroyV3 receiptArchiveV3 transferFeeV3)

set_option autoImplicit false

/-! ## §0 — the mem-free effects with no OWN named `*V3` def: name their registry expressions.

Each abbrev is DEFINITIONALLY the `v3RegistryBare` member (sans the uniform additive rc wrap —
the template's convention; see header). -/

/-- The rotated burn member (`burnVmDescriptor2R24`; = `RotatedKernelRefinementMintBurn.burnV3`). -/
abbrev burnV3 : EffectVmDescriptor2 :=
  v3OfFrozen Dregg2.Circuit.Emit.EffectVmEmitBurn.burnVmDescriptor

/-- The rotated incrementNonce member (`incrementNonceVmDescriptor2R24`;
= `RotatedKernelRefinementIncNonce.incNonceV3`). -/
abbrev incrementNonceV3 : EffectVmDescriptor2 :=
  v3OfFrozen Dregg2.Circuit.Emit.EffectVmEmitIncrementNonce.incrementNonceVmDescriptor

/-- The rotated emitEvent member (`emitEventVmDescriptor2R24`). -/
abbrev emitEventV3 : EffectVmDescriptor2 :=
  v3OfFrozen Dregg2.Circuit.Emit.EffectVmEmitEmitEvent.emitEventVmDescriptor

/-- The rotated exercise member (`exerciseVmDescriptor2R24` — the frozen exercise base the
cap-open crown wraps). -/
abbrev exerciseV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitExercise.exerciseVmDescriptor

/-- The rotated pipelinedSend member (`pipelinedSendVmDescriptor2R24`). -/
abbrev pipelinedSendV3 : EffectVmDescriptor2 :=
  v3Of Dregg2.Circuit.Emit.EffectVmEmitPipelinedSend.pipelinedSendVmDescriptor

/-- The STATIC per-slot setField member (`setFieldVmDescriptor2-<slot>R24` — the eight
selector-gated tick faces; the DYNAMIC `setFieldDynV3` is memory-ful and NOT here). -/
abbrev setFieldStaticV3 (slot : Fin 8) : EffectVmDescriptor2 :=
  withSelectorGate Dregg2.Circuit.Emit.EffectVmEmitSetField.SEL_SET_FIELD
    (v3OfFrozen (setFieldTickFace slot))

/-! ## §1 — the SHAPE BRICKS: `LookupShaped` is structural over the emission combinators.

No constraint list is ever evaluated: `lookupShaped_graduateV1` is parametric in the face
(via the committed `constraints_graduateV1_shapes`), and every deployed wrap only APPENDS
`.base`s or explicit `.lookup`s — closed under the four append bricks. -/

/-- The all-lookup non-arith shape — EXACTLY the `hshape` slot of
`algoStarkSound_of_memoryFree` (and the second component of
`transferV3_sideConditions_mechanical`). -/
abbrev LookupShaped (cs : List VmConstraint2) : Prop :=
  ∀ c ∈ cs, ¬ isArith c → ∃ l : Lookup, c = VmConstraint2.lookup l

/-- **The graduated core is lookup-shaped, ∀ face** — the ∀-d generalization of
`AirLegsDischarged.hbus_is_lookup` (same proof, parametric). -/
theorem lookupShaped_graduateV1 (d0 : EffectVmDescriptor) :
    LookupShaped (graduateV1 d0).constraints := by
  intro c hc hA
  rcases constraints_graduateV1_shapes d0 c hc with ⟨c₀, rfl⟩ | ⟨l, rfl⟩
  · exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA
  · exact ⟨l, rfl⟩

/-- Shape is closed under append. -/
theorem lookupShaped_append {cs₁ cs₂ : List VmConstraint2}
    (h₁ : LookupShaped cs₁) (h₂ : LookupShaped cs₂) : LookupShaped (cs₁ ++ cs₂) := by
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

/-- The empty extras list (the `v3OfWithCapWrite … []` members). -/
theorem lookupShaped_nil : LookupShaped [] := fun _ hc => nomatch hc

/-- A single appended `.base` (selector gates, epoch-bump gates, single pins) is arith. -/
theorem lookupShaped_base_single (c₀ : VmConstraint) :
    LookupShaped [VmConstraint2.base c₀] := by
  intro c hc hA
  simp only [List.mem_singleton] at hc
  subst hc
  exact absurd (show isArith (VmConstraint2.base c₀) from trivial) hA

/-- A `.base`-mapped pin block (`withRecordPin8Headroom2` / `withPermsVK8Weld` / rc-pin family)
is all-arith. -/
theorem lookupShaped_base_map {α : Type*} (f : α → VmConstraint) (xs : List α) :
    LookupShaped (xs.map fun a => VmConstraint2.base (f a)) := by
  intro c hc hA
  simp only [List.mem_map] at hc
  obtain ⟨a, -, rfl⟩ := hc
  exact absurd (show isArith (VmConstraint2.base (f a)) from trivial) hA

/-- A single appended `.lookup` (the attenuate/delegateAtten submask tooth). -/
theorem lookupShaped_lookup_single (l : Lookup) :
    LookupShaped [VmConstraint2.lookup l] := by
  intro c hc _
  simp only [List.mem_singleton] at hc
  exact ⟨l, hc⟩

/-! ## §2 — the per-effect SIDE-CONDITION packages (the `transferV3_sideConditions_mechanical`
shape, per effect): `rfl` + the structural shape bricks. NO new proof content per effect. -/

/-- The whole per-effect obligation of `algoStarkSound_of_memoryFree` at `d` (the fan-out
receipt shape of the lever's §6). -/
abbrev MemFreeSideConditions (d : EffectVmDescriptor2) : Prop :=
  (d.hashSites = [] ∧ d.ranges = []) ∧ LookupShaped d.constraints

-- Pure `graduateV1` members (v3Of / v3OfFrozen and the graduateV1-headed gate/pin rotations):
theorem mint_sideConditions : MemFreeSideConditions mintV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem burn_sideConditions : MemFreeSideConditions burnV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem incrementNonce_sideConditions : MemFreeSideConditions incrementNonceV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem emitEvent_sideConditions : MemFreeSideConditions emitEventV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem exercise_sideConditions : MemFreeSideConditions exerciseV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem pipelinedSend_sideConditions : MemFreeSideConditions pipelinedSendV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem setProgram_sideConditions : MemFreeSideConditions setProgramV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem cellSeal_sideConditions : MemFreeSideConditions cellSealV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem cellUnseal_sideConditions : MemFreeSideConditions cellUnsealV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem cellDestroy_sideConditions : MemFreeSideConditions cellDestroyV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem receiptArchive_sideConditions : MemFreeSideConditions receiptArchiveV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩
theorem transferFee_sideConditions : MemFreeSideConditions transferFeeV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_graduateV1 _⟩

-- `graduateV1 … ++ []` (the cap-family write faces with extras dropped):
theorem delegate_sideConditions : MemFreeSideConditions delegateV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) lookupShaped_nil⟩
theorem grantCap_sideConditions : MemFreeSideConditions grantCapWriteV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) lookupShaped_nil⟩
theorem introduce_sideConditions : MemFreeSideConditions introduceWriteV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) lookupShaped_nil⟩
theorem revokeCapability_sideConditions : MemFreeSideConditions revokeCapabilityV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) lookupShaped_nil⟩
theorem refreshDelegation_sideConditions : MemFreeSideConditions refreshDelegationWriteV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) lookupShaped_nil⟩

-- `graduateV1 … ++ [.lookup submaskLookup]` (the non-amplification tooth):
theorem attenuate_sideConditions : MemFreeSideConditions attenuateV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_lookup_single _)⟩
theorem delegateAtten_sideConditions : MemFreeSideConditions delegateAttenV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_lookup_single _)⟩

-- `graduateV1 … ++ [.base …]` (single gate/pin wraps):
theorem revokeDelegation_sideConditions : MemFreeSideConditions revokeDelegationWriteV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_single _)⟩
theorem supplyMint_sideConditions : MemFreeSideConditions supplyMintV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_single _)⟩
theorem setFieldStatic_sideConditions (slot : Fin 8) :
    MemFreeSideConditions (setFieldStaticV3 slot) :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_single _)⟩

-- `graduateV1 … ++ (map .base pins)` (the H1 headroom-pin wrap):
theorem makeSovereign_sideConditions : MemFreeSideConditions makeSovereignV3 :=
  ⟨⟨rfl, rfl⟩, lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_map _ _)⟩

-- `(graduateV1 … ++ pins) ++ welds` (the perms/VK 8-felt completion wraps):
theorem setPermissions_sideConditions : MemFreeSideConditions setPermsV3 :=
  ⟨⟨rfl, rfl⟩,
    lookupShaped_append
      (lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_map _ _))
      (lookupShaped_base_map _ _)⟩
theorem setVK_sideConditions : MemFreeSideConditions setVKV3 :=
  ⟨⟨rfl, rfl⟩,
    lookupShaped_append
      (lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_map _ _))
      (lookupShaped_base_map _ _)⟩

-- `(graduateV1 … ++ [.base sel]) ++ [.base pin]` (the bridge-mint felt mint-hash member):
theorem bridgeMint_sideConditions : MemFreeSideConditions mintV3BridgeHash :=
  ⟨⟨rfl, rfl⟩,
    lookupShaped_append
      (lookupShaped_append (lookupShaped_graduateV1 _) (lookupShaped_base_single _))
      (lookupShaped_base_single _)⟩

/-! ## §3 — the DRY assembler: ONE application shape shared by every instance. -/

/-- **`algoStarkSound_memFree_apply`** — the general assembler consumed through the per-effect
side-condition package: for any `d` with `MemFreeSideConditions d`, the full `AlgoStarkSound` at
the registry slice `fun _ => d` from EXACTLY {`Poseidon2SpongeCR`, `FriLdtExtract … d`,
`BusModelFamily … d`} + `MemMapFree`. Nothing per-effect remains but the package. -/
theorem algoStarkSound_memFree_apply {F : Type*} [Field F] [DecidableEq F]
    (d : EffectVmDescriptor2) (hside : MemFreeSideConditions d)
    (sponge : List ℤ → ℤ) (hCR : Poseidon2SpongeCR sponge)
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr d)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => d) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_memoryFree d sponge hCR hash fp embed perm RATE toNat params vk core A
    initState logN view tr hside.2 hside.1.1 hside.1.2 hfri hbusF hmemfree

/-! ## §4 — ★ THE FAN-OUT: `algoStarkSound_<effect>` per mem-free effect.

Each is ONE `algoStarkSound_memFree_apply` at its descriptor; the residual of EVERY instance is
EXACTLY {`Poseidon2SpongeCR sponge`, `FriLdtExtract … d`, `BusModelFamily … d`, `MemMapFree`} —
the named floor, identical to `algoStarkSound_transferV3_ofBusModels`. -/

section FanOut

variable {F : Type*} [Field F] [DecidableEq F]
  (sponge : List ℤ → ℤ) (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
  (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
  (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
  (initState : List ℤ) (logN : Nat) (view : ProofView)
  (tr : BatchPublicInputs → BatchProof → VmTrace)

theorem algoStarkSound_mint
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr mintV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        mintV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => mintV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply mintV3 mint_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_bridgeMint
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        mintV3BridgeHash)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        mintV3BridgeHash)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => mintV3BridgeHash) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply mintV3BridgeHash bridgeMint_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_supplyMint
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        supplyMintV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        supplyMintV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => supplyMintV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply supplyMintV3 supplyMint_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_burn
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr burnV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        burnV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => burnV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply burnV3 burn_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_incrementNonce
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        incrementNonceV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        incrementNonceV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => incrementNonceV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply incrementNonceV3 incrementNonce_sideConditions sponge hCR hash
    fp embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_emitEvent
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        emitEventV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        emitEventV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => emitEventV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply emitEventV3 emitEvent_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_exercise
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        exerciseV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        exerciseV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => exerciseV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply exerciseV3 exercise_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_pipelinedSend
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        pipelinedSendV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        pipelinedSendV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => pipelinedSendV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply pipelinedSendV3 pipelinedSend_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_delegate
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        delegateV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        delegateV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => delegateV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply delegateV3 delegate_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_delegateAtten
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        delegateAttenV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        delegateAttenV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => delegateAttenV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply delegateAttenV3 delegateAtten_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_attenuate
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        attenuateV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        attenuateV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => attenuateV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply attenuateV3 attenuate_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_grantCap
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        grantCapWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        grantCapWriteV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => grantCapWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply grantCapWriteV3 grantCap_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_introduce
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        introduceWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        introduceWriteV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => introduceWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply introduceWriteV3 introduce_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_revokeCapability
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        revokeCapabilityV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        revokeCapabilityV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => revokeCapabilityV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply revokeCapabilityV3 revokeCapability_sideConditions sponge hCR
    hash fp embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_revokeDelegation
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        revokeDelegationWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        revokeDelegationWriteV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => revokeDelegationWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply revokeDelegationWriteV3 revokeDelegation_sideConditions sponge
    hCR hash fp embed perm RATE toNat params vk core A initState logN view tr hfri hbusF
    hmemfree

theorem algoStarkSound_refreshDelegation
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        refreshDelegationWriteV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        refreshDelegationWriteV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => refreshDelegationWriteV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply refreshDelegationWriteV3 refreshDelegation_sideConditions sponge
    hCR hash fp embed perm RATE toNat params vk core A initState logN view tr hfri hbusF
    hmemfree

theorem algoStarkSound_makeSovereign
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        makeSovereignV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        makeSovereignV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => makeSovereignV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply makeSovereignV3 makeSovereign_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_setPermissions
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        setPermsV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        setPermsV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => setPermsV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply setPermsV3 setPermissions_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_setVK
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        setVKV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        setVKV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => setVKV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply setVKV3 setVK_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_setProgram
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        setProgramV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        setProgramV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => setProgramV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply setProgramV3 setProgram_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_cellSeal
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        cellSealV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        cellSealV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => cellSealV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply cellSealV3 cellSeal_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_cellUnseal
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        cellUnsealV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        cellUnsealV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => cellUnsealV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply cellUnsealV3 cellUnseal_sideConditions sponge hCR hash fp embed
    perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_cellDestroy
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        cellDestroyV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        cellDestroyV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => cellDestroyV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply cellDestroyV3 cellDestroy_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_receiptArchive
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        receiptArchiveV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        receiptArchiveV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => receiptArchiveV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply receiptArchiveV3 receiptArchive_sideConditions sponge hCR hash
    fp embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

theorem algoStarkSound_transferFee
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        transferFeeV3)
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        transferFeeV3)
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => transferFeeV3) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply transferFeeV3 transferFee_sideConditions sponge hCR hash fp
    embed perm RATE toNat params vk core A initState logN view tr hfri hbusF hmemfree

/-- The eight STATIC per-slot setField members in one parametric instance (`slot : Fin 8`). -/
theorem algoStarkSound_setFieldStatic (slot : Fin 8)
    (hCR : Poseidon2SpongeCR sponge)
    (hfri : FriLdtExtract sponge perm RATE toNat params vk core A initState logN view tr
        (setFieldStaticV3 slot))
    (hbusF : BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr
        (setFieldStaticV3 slot))
    (hmemfree : MemMapFree perm RATE toNat params vk core A initState logN view tr) :
    AlgoStarkSound hash (fun _ => setFieldStaticV3 slot) perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_memFree_apply (setFieldStaticV3 slot) (setFieldStatic_sideConditions slot)
    sponge hCR hash fp embed perm RATE toNat params vk core A initState logN view tr
    hfri hbusF hmemfree

end FanOut

/-! ## §5 — NON-VACUITY + the HONESTY falsifier.

The shape facts are not vacuously true (there ARE non-arith lookups routed through the bus
modeler), and `LookupShaped` is FALSE on a memory-ful descriptor (the exclusion list is real —
no mem-free fact was faked). The `AlgoStarkSound` premise teeth (`mainAirAccept_respecting` /
`mainAirAccept_biting`) live with the shared assembler in `AlgoStarkSoundInstance`. -/

/-- The attenuate shape fact carries a GENUINE non-arith `.lookup` — the `granted ⊑ held`
submask tooth — so the `BusModelFamily` residual is genuinely consumed, not vacuous. -/
theorem attenuateV3_has_lookup :
    ∃ c ∈ attenuateV3.constraints,
      ¬ isArith c ∧ ∃ l : Lookup, c = VmConstraint2.lookup l :=
  ⟨VmConstraint2.lookup submaskLookup,
    List.mem_append_right _ (List.Mem.head _),
    fun h => h, submaskLookup, rfl⟩

/-- Same for delegateAtten (the reused non-amplification tooth). -/
theorem delegateAttenV3_has_lookup :
    ∃ c ∈ delegateAttenV3.constraints,
      ¬ isArith c ∧ ∃ l : Lookup, c = VmConstraint2.lookup l :=
  ⟨VmConstraint2.lookup submaskLookup,
    List.mem_append_right _ (List.Mem.head _),
    fun h => h, submaskLookup, rfl⟩

/-- **The falsifier** — `LookupShaped` is FALSE for the memory-ful `setFieldDynV3` (its Blum
write op is non-arith and not a lookup). The mem-free classification has teeth: a memory-touching
descriptor CANNOT be pushed through this file's route, which is why the 8-member memory family is
REPORTED to the memory-legs assembler instead. -/
theorem setFieldDynV3_not_lookupShaped : ¬ LookupShaped setFieldDynV3.constraints := by
  intro h
  have hmem : VmConstraint2.memOp fieldWriteOp ∈ setFieldDynV3.constraints :=
    List.mem_append_right _ (List.Mem.head _)
  obtain ⟨l, hl⟩ := h _ hmem (fun hA => hA)
  exact nomatch hl

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms lookupShaped_graduateV1
#assert_axioms lookupShaped_append
#assert_axioms algoStarkSound_memFree_apply
#assert_axioms algoStarkSound_mint
#assert_axioms algoStarkSound_bridgeMint
#assert_axioms algoStarkSound_supplyMint
#assert_axioms algoStarkSound_burn
#assert_axioms algoStarkSound_incrementNonce
#assert_axioms algoStarkSound_emitEvent
#assert_axioms algoStarkSound_exercise
#assert_axioms algoStarkSound_pipelinedSend
#assert_axioms algoStarkSound_delegate
#assert_axioms algoStarkSound_delegateAtten
#assert_axioms algoStarkSound_attenuate
#assert_axioms algoStarkSound_grantCap
#assert_axioms algoStarkSound_introduce
#assert_axioms algoStarkSound_revokeCapability
#assert_axioms algoStarkSound_revokeDelegation
#assert_axioms algoStarkSound_refreshDelegation
#assert_axioms algoStarkSound_makeSovereign
#assert_axioms algoStarkSound_setPermissions
#assert_axioms algoStarkSound_setVK
#assert_axioms algoStarkSound_setProgram
#assert_axioms algoStarkSound_cellSeal
#assert_axioms algoStarkSound_cellUnseal
#assert_axioms algoStarkSound_cellDestroy
#assert_axioms algoStarkSound_receiptArchive
#assert_axioms algoStarkSound_transferFee
#assert_axioms algoStarkSound_setFieldStatic
#assert_axioms attenuateV3_has_lookup
#assert_axioms delegateAttenV3_has_lookup
#assert_axioms setFieldDynV3_not_lookupShaped

end Dregg2.Circuit.AlgoStarkSoundFanoutMemFree
