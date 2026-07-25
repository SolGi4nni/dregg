/-
# `Dregg2.Circuit.KernelConfigSoundnessAvail` — THE DEPLOYED HARDENED CONFIG CAPSTONE over `RfixAvail`.

`KernelConfigSoundness.kernelConfigSound` is the config-evolution capstone over `CircuitSoundnessAssembled.Rfix`:
`verifyBatch (vkOfRegistry Rfix)`-accept ⟹ a real kernel-config transition, with the STARK carrier the
ENUMERATED `algoStarkSound_kernel` (not opaque `[StarkSound]`). But over `Rfix` the transfer/burn slots
CARRY availability (`availOf`).

This module is the SAME capstone REPOINTED to the DEPLOYED hardened registry `RfixAvail` (= `Rfix` with the
two balance-debiting tags flipped to `weldedTransferAvailWide` / `weldedBurnAvailWide`): `verifyBatch
(vkOfRegistry RfixAvail)`-accept ⟹ a real kernel-config transition with `availOf` DISCHARGED at the
debiting tags (the deployed borrow chain FORCES `amt ≤ bal`). Both layers are re-keyed to `RfixAvail`:

  * **STARK layer** — the ENUMERATED hardened object: `AlgoStarkSoundKernelAvail.algoStarkSound_kernelAvail`
    builds `AlgoStarkSound hash RfixAvail` routing the two `.umemOp`-bearing avail members through
    `algoStarkSound_of_memoryLegs` (the umem memory-checking leg), NOT the map-shape `side_transfer`/
    `side_burn` (which PROVABLY fail `MapShape` on the appended `.umemOp`);
    `FriVerifierBridge.starkSound_of_verifyAlgo` lifts it (with `DeployedRefines RfixAvail`) to the apex
    carrier `StarkSound hash RfixAvail`.
  * **CONFIG layer** — the ASSEMBLED hardened bridge: `ClosureFinalAvail.closedWitnessAvail_of_readouts`
    routes the transfer/burn slots through the `ClosureTransferAvail` `_availFix` slots (availability
    DISCHARGED) and every other tag through the genuine `Rfix` readout bundle; the apex
    `ClosureFinalAvail.lightclient_unfoolable_closed_final_avail` reaches `kstepAll pi.effect pre post`.
  * **UNFOLD** — `kstepAll = dispatchArm` exposes the REAL `∃ fa, actionTag fa = pi.effect ∧
    fullActionStep pre fa post` config transition.

## Why this is the ADDITIVE repoint (not an in-place `Rfix` flip)

`CircuitSoundnessAssembled.Rfix 0 = transferV3Membership` is a load-bearing `rfl` the bare STARK-side
`algoStarkSound_kernel` enumerates; an in-place flip is unsound (the welded members' `.umemOp` fails
`MapShape`). `RfixAvail` is the parallel registry, and THIS capstone is the deployed VK a light client
verifies against (`vkOfRegistry RfixAvail`). The bare `Rfix` capstone (`kernelConfigSound`) is untouched —
nothing downstream reddens.

## The honest residual

⚑ MIGRATED 2026-07-25: `hfri` was `AlgoStarkSoundGeneral.FriLdtExtract`, the singleton-OOD bundle
PROVED to force `verifyBatch` to reject every input (so this theorem was vacuously true); it is now
`ApexOodLaneRepair.FriLdtExtractCons`, with the zero-added-strength receipt at
`AlgoStarkSoundKernelAvail.kernelAvailPremise_adds_no_strength`.

Same as `kernelConfigSound` (Poseidon2 CR ×2, `FriLdtExtractCons`, `BusModelFamily`, `MapReconcileFamily`,
`MapTableAssembly`, `DeployedRefines`, the per-effect readouts, `WitnessDecodes`, `mkLog`), PLUS the two
umem `MemoryLegs` at the welded avail members, and the two `ClosureTransferAvail` `_availFix` readout
bundles (the hardened transfer column+ledger+authority readouts / the hardened burn readout). Nothing
faked: the STARK carrier is enumerated (`algoStarkSound_kernelAvail`), availability is a THEOREM, and every
carried fact is a named `Prop`/`Type` hypothesis.

## Discipline

Sorry-free; no `decide`/`Fintype` over field-sized objects; no axiom beyond Lean's own. NEW file; imports
read-only; builds targeted (`lake build Dregg2.Circuit.KernelConfigSoundnessAvail`).
-/
import Dregg2.Circuit.AlgoStarkSoundKernelAvail
import Dregg2.Circuit.ClosureFinalAvail
import Dregg2.Circuit.FriVerifierBridge

namespace Dregg2.Circuit.KernelConfigSoundnessAvail

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Circuit.FriVerifierBridge
  (AlgoStarkSound ProofView DeployedRefines starkSound_of_verifyAlgo)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.AlgoStarkSoundGeneral (BusModelFamily MemoryLegs)
open Dregg2.Circuit.ApexOodLaneRepair
  (FriLdtExtractCons FriLdtExtractConsNoOodShape friLdtExtractCons_iff_noOodShape)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapReconcileFamily MapTableAssembly)
open Dregg2.Circuit.AlgoStarkSoundKernelAvail (algoStarkSound_kernelAvail)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts)
open Dregg2.Circuit.ClosureTransferAvail (RfixAvail TransferTraceReadoutAvail BurnTraceReadoutAvail
  closedLogExtract_transfer_closed_availFix closedLogExtract_burn_closed_availFix)
open Dregg2.Circuit.ClosureTransfer (TransferAuthorityWitness)
open Dregg2.Circuit.TransferDecodeBridge (LedgerSurfaceReadout)
open Dregg2.Circuit.ClosureFinalAvail (ClosedWitnessAvail closedWitnessAvail_of_readouts)
open Dregg2.Circuit.Emit.EffectVmEmitUMemWeldWide (weldedTransferAvailWide weldedBurnAvailWide)
open Dregg2.Circuit.ActionDispatch (actionTag fullActionStep)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA)

set_option autoImplicit false

section
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}

local notation "Slive" =>
  S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-- **`kernelConfigSoundAvail` — verifyBatch-accept over `RfixAvail` ⟹ a REAL kernel-config transition with
availability DISCHARGED.**

From the HARDENED STARK-side floor (Poseidon2 CR ×2, `FriLdtExtractCons`/`BusModelFamily` at each `RfixAvail`
descriptor, `MapReconcileFamily`/`MapTableAssembly` at the off-debit tags, the two umem `MemoryLegs` at the
welded avail members, `DeployedRefines RfixAvail`) composed through `algoStarkSound_kernelAvail` +
`starkSound_of_verifyAlgo`, and the config-side genuine readout bundle + the two `_availFix` readout
bundles composed through `closedWitnessAvail_of_readouts`, a `verifyBatch`-accepted batch against
`vkOfRegistry RfixAvail` at ANY published effect tag yields decoded endpoints and a GENUINE action `fa`
with `actionTag fa = pi.effect` performing `fullActionStep pre fa post`, whose endpoints commit to
`(pi.pre, pi.post)`. At `pi.effect ∈ {0,4}` the transition's availability leg is FORCED by the deployed
borrow chain — the light client verifies the descriptor over which `amt ≤ bal` is a THEOREM. -/
theorem kernelConfigSoundAvail
    {F : Type*} [Field F] [DecidableEq F]
    {State : Type} {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (LH : List Turn → ℤ)
    (hash : List ℤ → ℤ) (hCRh : Poseidon2SpongeCR hash)
    (sponge : List ℤ → ℤ) (hCRs : Poseidon2SpongeCR sponge)
    (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : EffectIdx → BatchPublicInputs → BatchProof → VmTrace)
    -- ★ HARDENED STARK floor at the DEPLOYED descriptors.
    (hfri : ∀ e : EffectIdx, FriLdtExtractCons sponge perm RATE toNat params vk core A initState
        logN view (tr e) (RfixAvail e))
    (hbusF : ∀ e : EffectIdx, BusModelFamily fp embed perm RATE toNat params vk core A initState
        logN view (tr e) (RfixAvail e))
    (hrec : ∀ e : EffectIdx, MapReconcileFamily hash perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    (hasm : ∀ e : EffectIdx, MapTableAssembly perm RATE toNat params vk core A initState
        logN view (tr e) (Rfix e))
    -- ★ the two umem memory-checking legs at the welded avail members (the `.umemOp` leg).
    (hlegs0 : MemoryLegs hash perm RATE toNat params vk core A initState logN view (tr 0)
        weldedTransferAvailWide)
    (hlegs4 : MemoryLegs hash perm RATE toNat params vk core A initState logN view (tr 4)
        weldedBurnAvailWide)
    (href : DeployedRefines RfixAvail perm RATE toNat params vk
        (fullChecks core A toNat params.powBits) initState logN view)
    -- ★ config-side: the genuine per-effect readouts (off-debit tags) + the two `_availFix` bundles.
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    -- ★ the HARDENED transfer readout bundle (feeds `closedLogExtract_transfer_closed_availFix`).
    (readoutT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Σ' (trn : Turn) (a : AssetId), TransferTraceReadoutAvail hash minit mfin maddrs t pre post trn a)
    (hpubT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      pubLogPost = LH ((readoutT minit mfin maddrs t pre post hsat).1 :: pre.log))
    (ledgerT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      LedgerSurfaceReadout Slive
        pre post (readoutT minit mfin maddrs t pre post hsat).1
        (readoutT minit mfin maddrs t pre post hsat).2.1
        (readoutT minit mfin maddrs t pre post hsat).2.2.srcPre.balLo
        (readoutT minit mfin maddrs t pre post hsat).2.2.srcPost.balLo
        (readoutT minit mfin maddrs t pre post hsat).2.2.dstPre.balLo
        (readoutT minit mfin maddrs t pre post hsat).2.2.dstPost.balLo)
    (fcapsT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState), Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t →
      Dregg2.Exec.FacetAuthority.FacetCaps)
    (authWitnessT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      TransferAuthorityWitness hash (fcapsT minit mfin maddrs t pre post hsat) pre
        (readoutT minit mfin maddrs t pre post hsat).1)
    (toyAuthOfT : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState)
      (hsat : Satisfied2 hash weldedTransferAvailWide minit mfin maddrs t),
      Dregg2.Exec.authorizedB pre.kernel.caps (readoutT minit mfin maddrs t pre post hsat).1 = true)
    -- ★ the HARDENED burn readout (feeds `closedLogExtract_burn_closed_availFix`).
    (readoutB : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      BurnTraceReadoutAvail hash LH minit mfin maddrs t pubLogPost pre post)
    (mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode Slive pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash RfixAvail Slive pi)
    (hacc : verifyBatch (vkOfRegistry RfixAvail) pi π = Verdict.accept) :
    ∃ (pre post : RecChainedState) (fa : FullActionA),
      StateDecode Slive pi.toPublished pre post ∧
      actionTag fa = pi.effect ∧
      fullActionStep pre fa post ∧
      pi.pre = (Slive).commit pre.kernel pi.turn ∧
      pi.post = (Slive).commit post.kernel pi.turn := by
  -- STARK layer: the ENUMERATED hardened kernel object → AlgoStarkSound → StarkSound (opaque gone).
  haveI hAlgo : AlgoStarkSound hash RfixAvail perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view :=
    algoStarkSound_kernelAvail sponge hCRs hash hCRh fp embed perm RATE toNat params vk core A
      initState logN view tr hfri hbusF hrec hasm hlegs0 hlegs4
  haveI hSS : StarkSound hash RfixAvail :=
    starkSound_of_verifyAlgo hash RfixAvail perm RATE toNat params vk
      (fullChecks core A toNat params.powBits) initState logN view href
  -- CONFIG layer: the two `_availFix` slots (availability DISCHARGED) + the genuine bundle → kstepAll.
  have availTransfer : Dregg2.Circuit.ClosureAll.ClosedLogExtract Slive LH hash RfixAvail 0 :=
    closedLogExtract_transfer_closed_availFix (LH := LH) hash readoutT hpubT ledgerT fcapsT
      authWitnessT toyAuthOfT
  have availBurn : Dregg2.Circuit.ClosureAll.ClosedLogExtract Slive LH hash RfixAvail 4 :=
    closedLogExtract_burn_closed_availFix (LH := LH) hash readoutB
  obtain ⟨pre, post, hdec, hstep, hc1, hc2⟩ :=
    Dregg2.Circuit.ClosureFinalAvail.lightclient_unfoolable_closed_final_avail hash LH hCRh pi π
      (closedWitnessAvail_of_readouts rds availTransfer availBurn mkLog pi hwitdec) hacc
  -- UNFOLD kstepAll = dispatchArm to expose the REAL config transition fullActionStep.
  obtain ⟨fa, htag, hfull⟩ := hstep
  exact ⟨pre, post, fa, hdec, htag, hfull, hc1, hc2⟩

end

/-! ## §M — ⚑ THE MIGRATION RECEIPT (2026-07-25): the corrected premise adds ZERO strength. -/

/-- **The migrated FRI premise cannot be the reason `kernelConfigSoundAvail` is empty.** At every
DEPLOYED HARDENED tag, `FriLdtExtractCons … (RfixAvail e)` is EQUIVALENT to itself with the OOD-shape
conjunct DELETED: that conjunct is supplied by the bundle's OWN `AcceptsFull` antecedent
(`ApexOodLaneRepair.acceptsFull_gives_cons_shape` — `FriVerifier.batchTablesCheck` returns `false`
on an empty `oodPoint`), so it cannot shrink the set of accepting runs the premise ranges over.

Contrast the premise this capstone was migrated OFF — `AlgoStarkSoundGeneral.FriLdtExtract`,
asserting the singleton `oodPoint = [ood]`: that conjunct is CONTRADICTED on accepting runs and
forces `CircuitSoundness.verifyBatch` to reject EVERY input at the deployed `cfg*` arguments
(`ApexOodLaneRepair.friLdtExtract_makes_verifyBatch_reject_everything`). Since this capstone is the
VK a light client actually verifies against (`vkOfRegistry RfixAvail`), that is precisely the
statement that had nothing behind it.

⚠ NOT CLAIMED: satisfiability of the corrected bundle at the deployed arguments — its remaining
conjuncts ARE the undischarged FRI-LDT / Merkle / Fiat–Shamir floor and `cfg*` are `opaque`. The
retained conjunct `topen ∈ (view pi π).1.tableOpenings` is refutable at the toy accepting pole
(whose `tableOpenings` is `[]`); that residual is inherited unchanged from the corrected bundle,
not introduced by this migration. -/
theorem kernelConfigAvailPremise_adds_no_strength
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

/-! ## Kernel-clean keystone (0 sorries; axiom floor is Lean's own). -/

#assert_axioms kernelConfigSoundAvail
#assert_axioms kernelConfigAvailPremise_adds_no_strength

end Dregg2.Circuit.KernelConfigSoundnessAvail
