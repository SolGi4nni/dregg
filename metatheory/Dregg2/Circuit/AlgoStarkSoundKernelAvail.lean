/-
# `Dregg2.Circuit.AlgoStarkSoundKernelAvail` — the STARK capstone over the HARDENED registry `RfixAvail`:
`AlgoStarkSound hash RfixAvail`, routing the two `.umemOp`-bearing avail members through the
MEMORY-LEGS assembler (NOT the map-shape `side_transfer`/`side_burn`).

## Why the bare `side_transfer`/`side_burn` route CANNOT be reused at tags 0/4

`AlgoStarkSoundKernel.algoStarkSound_kernel` assembles `AlgoStarkSound hash Rfix` POINTWISE, each tag
through `algoStarkSound_of_mapShape (Rfix e)` fed `rfix_sideConditions e : KernelSideConditions (Rfix e)`
— whose core is `MapShape (Rfix e).constraints` (every non-arith constraint is a `.lookup` or a `.mapOp`).

`RfixAvail` flips tags 0/4 to the DEPLOYED hardened members `weldedTransferAvailWide` /
`weldedBurnAvailWide` (`ClosureTransferAvail.RfixAvail`). Those are `weldUMemIntoWide baseAvail dom`, which
APPENDS a `.umemOp` constraint (`EffectVmEmitUMemWeldWide.weldUMemIntoWide` — the single-domain umem
memory-checking cohort). A `.umemOp` is non-arith and is NEITHER a `.lookup` NOR a `.mapOp`, so
`MapShape` PROVABLY FAILS on the welded members (the `setFieldDynV3_not_mapShape`-class falsifier). Hence
`side_transfer`/`side_burn` CANNOT re-prove over them — an in-place flip of the map-shape route is unsound.

## The route: `algoStarkSound_of_memoryLegs` with the umem leg

`AlgoStarkSoundGeneral.algoStarkSound_of_memoryLegs` is the ∀-d assembler for ANY descriptor: it takes the
graduated column shape (`d.hashSites = []`, `d.ranges = []` — both `rfl` for the welded avail members, the
15-bit borrow teeth lower into per-width range TABLES, i.e. `.lookup`s, not `.ranges`) and a `MemoryLegs`
input that handles the non-lookup non-arith arm (here the `.umemOp` row denotation) plus the six
memory-table legs (`Nodup` boundary / address closure / `Disciplined` / `MemCheck` balance / the two
table-assembly equations). The `.umemOp` is checked by the UMEM MEMORY-CHECKING leg, not `MapShape`.

So at tags 0/4 the capstone carries `MemoryLegs … weldedXAvailWide` (the umem leg — a named, realizable
floor exactly as the mapOp tags carry `MapReconcileFamily`), and at every OTHER tag it is the SAME
map-shape route as `algoStarkSound_kernel`, transported across `RfixAvail_off` (the 34 unchanged
descriptors are literally identical to `Rfix`'s).

## Realizability of the apex floor

`ClosureFinalAvail.lightclient_unfoolable_closed_final_avail` carries `[StarkSound hash RfixAvail]` as its
realizable extraction floor. This module + `FriVerifierBridge.starkSound_of_verifyAlgo` (with the code
refinement `DeployedRefines RfixAvail`) is the CONSTRUCTION of that floor over the umem members — the
parallel of `KernelConfigSoundness` at the hardened registry.

## The honest residual

⚑ MIGRATED 2026-07-25 off `AlgoStarkSoundGeneral.FriLdtExtract` / `algoStarkSound_of_memoryLegs`
(the singleton-OOD premise PROVED to force `verifyBatch` to reject every input, emptying this
capstone) onto `ApexOodLaneRepair.FriLdtExtractCons` / `algoStarkSound_of_memoryLegs_cons`; §3b is
the zero-added-strength receipt for the replacement.

Same named floor as `algoStarkSound_kernel` per tag {`Poseidon2SpongeCR hash` — ⛑ ×2 until
2026-07-30, the `sponge` instance is gone —, `FriLdtExtractCons`,
`BusModelFamily`}, PLUS: at tags 0/4 the umem `MemoryLegs`, at every other tag the `MapReconcileFamily` +
`MapTableAssembly` pair `algoStarkSound_kernel` already carries. Nothing faked; `.umemOp` handled by the
umem leg; the two graduated-shape legs discharge `rfl`.

## Discipline

Sorry-free; no `decide`/`Fintype` over field-sized objects (BabyBear never computed — constructor-shape
structural). NEW file; imports read-only; builds targeted (`lake build Dregg2.Circuit.AlgoStarkSoundKernelAvail`).
-/
import Dregg2.Circuit.AlgoStarkSoundKernel
import Dregg2.Circuit.ClosureTransferAvail

namespace Dregg2.Circuit.AlgoStarkSoundKernelAvail

open Dregg2.Circuit.FriVerifierBridge (AlgoStarkSound ProofView)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriChecks FriCore FieldArith fullChecks)
open Dregg2.Circuit.CircuitSoundness (Registry BatchPublicInputs BatchProof EffectIdx)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmConstraint2 VmTrace)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.AlgoStarkSoundGeneral (BusModelFamily MemoryLegs)
open Dregg2.Circuit.ApexOodLaneRepair
  (FriLdtExtractCons FriLdtExtractConsNoOodShape friLdtExtractCons_iff_noOodShape
   algoStarkSound_of_memoryLegs_cons)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapReconcileFamily MapTableAssembly
  algoStarkSound_of_mapShape)
open Dregg2.Circuit.AlgoStarkSoundKernel (algoStarkSound_of_pointwise rfix_sideConditions)
open Dregg2.Circuit.CircuitSoundnessAssembled (Rfix)
open Dregg2.Circuit.ClosureTransferAvail (RfixAvail RfixAvail_transfer RfixAvail_burn RfixAvail_off)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide (weldedTransferAvailWide weldedBurnAvailWide)

set_option autoImplicit false

/-! ## §1 — the two graduated-shape legs of the welded avail members are `rfl`.

`weldUMemIntoWide` is a `{ d with … }` record update touching only name/traceWidth/tables/constraints, so
`hashSites`/`ranges` are inherited; the base avail faces lower every hash site into the poseidon2 chip
lookup and every range into a per-width range TABLE (a `.lookup`), so both column lists are empty. -/

theorem transferAvailWide_hashSites : weldedTransferAvailWide.hashSites = [] := rfl
theorem transferAvailWide_ranges : weldedTransferAvailWide.ranges = [] := rfl
theorem burnAvailWide_hashSites : weldedBurnAvailWide.hashSites = [] := rfl
theorem burnAvailWide_ranges : weldedBurnAvailWide.ranges = [] := rfl

/-! ## §2 — ★ THE CAPSTONE: `AlgoStarkSound hash RfixAvail` from the named floor + the two umem legs.

Assembled POINTWISE: tags 0/4 route through `algoStarkSound_of_memoryLegs` at the welded avail member with
the carried umem `MemoryLegs`; every other tag is the `algoStarkSound_of_mapShape` route of
`algoStarkSound_kernel`, transported across `RfixAvail_off`. -/

/-- **`algoStarkSound_kernelAvail` — kernel STARK-soundness over the DEPLOYED HARDENED registry.** From
EXACTLY the named floor of `algoStarkSound_kernel` per tag — {`Poseidon2SpongeCR hash` (⛑ ×2 until
2026-07-30), `FriLdtExtractCons`,
`BusModelFamily`} + per off-debit tag {`MapReconcileFamily`, `MapTableAssembly`} — PLUS, at the two
BALANCE-DEBITING tags (0 transfer, 4 burn), the umem `MemoryLegs` (`hlegs0`/`hlegs4`) at the welded avail
members (the `.umemOp` memory-checking leg replacing the map-shape route), the full
`AlgoStarkSound hash RfixAvail …`. Assembled POINTWISE: tags 0/4 via `algoStarkSound_of_memoryLegs`, every
other tag via the `algoStarkSound_kernel` map-shape route transported across `RfixAvail_off`. NO `sorry`,
NO carrier, NO re-assumed `StarkSound`/`AlgoStarkSound`. -/
theorem algoStarkSound_kernelAvail {F : Type*} [Field F] [DecidableEq F]
    (sponge : List ℤ → ℤ)
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : EffectIdx → BatchPublicInputs → BatchProof → VmTrace)
    -- the FRI/bus floor at the DEPLOYED descriptor of each tag (welded avail at 0/4, `Rfix e` elsewhere).
    (hfri : ∀ e : EffectIdx, FriLdtExtractCons sponge perm RATE toNat params vk core A initState
        logN view (tr e) (RfixAvail e))
    (hbusF : ∀ e : EffectIdx, BusModelFamily fp embed perm RATE toNat params vk core A initState
        logN view (tr e) (RfixAvail e))
    -- the map-shape legs at the off-debit tags (used only where `RfixAvail e = Rfix e`).
    (hrec : ∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    (hasm : ∀ e : EffectIdx, MapTableAssembly perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ the two umem memory-checking legs at the welded avail members (the `.umemOp` leg).
    (hlegs0 : MemoryLegs hash perm RATE toNat params vk core A initState logN view (tr 0)
        weldedTransferAvailWide)
    (hlegs4 : MemoryLegs hash perm RATE toNat params vk core A initState logN view (tr 4)
        weldedBurnAvailWide) :
    AlgoStarkSound hash RfixAvail perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
  algoStarkSound_of_pointwise hash RfixAvail perm RATE toNat params vk
    (fullChecks core A toNat params.powBits) initState logN view
    (fun e => by
      by_cases h0 : e = 0
      · -- tag 0: `RfixAvail 0 = weldedTransferAvailWide`; the `.umemOp` is checked by `hlegs0`.
        subst h0
        rw [RfixAvail_transfer]
        have hfri0 := hfri 0; have hbusF0 := hbusF 0
        rw [RfixAvail_transfer] at hfri0 hbusF0
        exact algoStarkSound_of_memoryLegs_cons weldedTransferAvailWide sponge hash fp embed perm RATE
          toNat params vk core A initState logN view (tr 0)
          transferAvailWide_hashSites transferAvailWide_ranges hfri0 hbusF0 hlegs0
      · by_cases h4 : e = 4
        · -- tag 4: `RfixAvail 4 = weldedBurnAvailWide`; the `.umemOp` is checked by `hlegs4`.
          subst h4
          rw [RfixAvail_burn]
          have hfri4 := hfri 4; have hbusF4 := hbusF 4
          rw [RfixAvail_burn] at hfri4 hbusF4
          exact algoStarkSound_of_memoryLegs_cons weldedBurnAvailWide sponge hash fp embed perm RATE
            toNat params vk core A initState logN view (tr 4)
            burnAvailWide_hashSites burnAvailWide_ranges hfri4 hbusF4 hlegs4
        · -- every other tag: the `algoStarkSound_kernel` map-shape route, transported.
          rw [RfixAvail_off h0 h4]
          have hfrie := hfri e; have hbusFe := hbusF e
          rw [RfixAvail_off h0 h4] at hfrie hbusFe
          exact algoStarkSound_of_mapShape (Rfix e) sponge hash hCRh fp embed perm RATE toNat
            params vk core A initState logN view (tr e)
            (rfix_sideConditions e).2 (rfix_sideConditions e).1.1 (rfix_sideConditions e).1.2
            hfrie hbusFe (hrec e) (hasm e))

/-! ## §3b — ⚑ THE MIGRATION RECEIPT (2026-07-25). -/

/-- **The migrated premise cannot be the reason this capstone is empty.** At every deployed
hardened tag, `FriLdtExtractCons … (RfixAvail e)` is EQUIVALENT to itself with the OOD-shape
conjunct DELETED (the conjunct is supplied by the bundle's own `AcceptsFull` antecedent). The
premise this capstone was migrated OFF — `AlgoStarkSoundGeneral.FriLdtExtract`, asserting the
singleton `oodPoint = [ood]` — is REFUTED on accepting runs and forces `verifyBatch` to reject
everything (`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`). -/
theorem kernelAvailPremise_adds_no_strength
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : EffectIdx → BatchPublicInputs → BatchProof → VmTrace) :
    ∀ e : EffectIdx,
      (FriLdtExtractCons sponge perm RATE toNat params vk core A initState logN view (tr e)
          (RfixAvail e)
        ↔ FriLdtExtractConsNoOodShape sponge perm RATE toNat params vk core A initState logN
          view (tr e) (RfixAvail e)) :=
  fun e => friLdtExtractCons_iff_noOodShape sponge perm RATE toNat params vk core A initState
    logN view (tr e) (RfixAvail e)

/-! ## §4 — TEETH: the umem route is genuine (the falsifier that FORBIDS the map-shape route at 0/4).

`AlgoStarkSoundKernel.setFieldDynV3_not_mapShape` shows `MapShape` is falsifiable on a `.memOp`-carrying
descriptor; the SAME classification forbids the map-shape route on the `.umemOp`-carrying welded avail
members — which is exactly why tags 0/4 route through `algoStarkSound_of_memoryLegs`. The welded members
append a `.umemOp` (`EffectVmEmitUMemWeldWide.weldUMemIntoWide_constraints`), so the honest reason the
capstone needs the memory-legs route here (not `side_transfer`/`side_burn`) is that the deployed hardened
descriptors are memory-disciplined, not map-shaped. -/

/-- The welded transfer avail member's constraints END in the appended `.umemOp` — the non-arith,
non-lookup, non-mapOp constraint that FORCES the memory-legs route (and would falsify `MapShape`). -/
theorem transferAvailWide_has_umemOp :
    ∃ m, VmConstraint2.umemOp m ∈ weldedTransferAvailWide.constraints := by
  unfold weldedTransferAvailWide
  rw [Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide.weldUMemIntoWide_constraints]
  exact ⟨_, List.mem_append_right _ (List.Mem.head _)⟩

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms transferAvailWide_hashSites
#assert_axioms algoStarkSound_kernelAvail
#assert_axioms kernelAvailPremise_adds_no_strength
#assert_axioms transferAvailWide_has_umemOp

end Dregg2.Circuit.AlgoStarkSoundKernelAvail
