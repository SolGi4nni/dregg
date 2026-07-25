/-
# Dregg2.Circuit.ClosureFinalAvail — the CLOSED circuit-soundness apex on the HARDENED (DEPLOYED)
registry `RfixAvail`: `availOf` DISCHARGED at the apex, not carried.

## What this module is

`ClosureFinal.lightclient_unfoolable_circuit_sound` is the headline apex over `CircuitSoundnessAssembled.Rfix`
— the Lean-side registry whose transfer/burn tags (0/4) still route to the BARE faces
(`transferV3Membership` / the bare burn). Over `Rfix` the transfer/burn slots must CARRY availability as a
per-witness residual (`ClosureTransfer.closedLogExtract_transfer_closed`'s `availOf`, and the burn slot's
in-decode `guardAvail`), because the bare mod-`p` balance gate does NOT force `amt ≤ bal` (the
underflow-wrap mint-from-nothing / well-supply-inflation forgeries).

`ClosureTransferAvail` closed that gap over the PARALLEL registry `RfixAvail` (= `Rfix` with tags 0/4
flipped to the DEPLOYED hardened members `weldedTransferAvailWide` / `weldedBurnAvailWide`, whose borrow
chain FORCES `amt ≤ bal`): its `closedLogExtract_transfer_closed_availFix` / `_burn_closed_availFix` slots
discharge the transfer/burn `ClosedLogExtract` over `RfixAvail` with availability a THEOREM, not a
hypothesis. But those two slots were a PROVEN-BUT-UNTHREADED island. This module THREADS them up to the
apex.

  * **`closedLogExtract_transport`** — the registry-congruence: `ClosedLogExtract` depends on `R` only
    through `R e`, so it transports across `R' e = R e`. This lifts the 34 UNCHANGED tags of
    `ClosureFanoutGenuine.closedLogExtract_all_genuine` (stated at `Rfix e`) to `RfixAvail e` via
    `ClosureTransferAvail.RfixAvail_off` — no re-proof, the descriptors are literally identical.
  * **`closedLogExtract_all_genuine_avail`** — the `∀ e, ClosedLogExtract … RfixAvail e` family: tags 0/4
    from the `_availFix` slots (availability DISCHARGED), every other tag transported from the genuine
    `Rfix` bundle. So the two debiting slots are the deployed hardened members; the rest are verbatim.
  * **`ClosedWitnessAvail`** — the single parametric witness floor over `RfixAvail` (the `ClosedWitness`
    mirror): `WitnessDecodes hash RfixAvail`, the single `ClosedLogExtract … RfixAvail pi.effect`, and the
    log enrichment. At `pi.effect ∈ {0,4}` its `ext` is an `_availFix` slot — availability discharged AT
    the descriptor the light client verifies.
  * **`lightclient_unfoolable_closed_final_avail`** — THE APEX: from a batch verifying against
    `vkOfRegistry RfixAvail` + `[StarkSound hash RfixAvail]` + the crypto floors + `ClosedWitnessAvail`,
    the light client concludes a genuine full kernel+log transition `kstepAll pi.effect pre post` whose
    endpoints commit to `pi`. At the two debiting tags the transition's availability leg is FORCED by the
    deployed borrow chain — not carried as an `availOf` residual anywhere.

## The STARK floor `[StarkSound hash RfixAvail]` (realizability)

Same altitude as the bare apex's `[StarkSound hash Rfix]`: a carried, realizable extraction floor. Its
CONSTRUCTION over `RfixAvail` is the parallel STARK lane `AlgoStarkSoundKernelAvail.algoStarkSound_kernelAvail`
(→ `starkSound_of_verifyAlgo`), which routes the two `.umemOp`-bearing avail members
(`weldedTransferAvailWide` / `weldedBurnAvailWide`) through `algoStarkSound_of_memoryLegs` (the
umem-memory-checking leg) rather than the map-shape `side_transfer`/`side_burn` — those bare-face side
conditions PROVABLY fail `MapShape` on the appended `.umemOp` (`setFieldDynV3_not_mapShape`-class). The
apex carries the class; the parallel lane exhibits it realizable.

## Why `Rfix`/`vkOfRegistry` are NOT mutated (additive, not an in-place flip)

`CircuitSoundnessAssembled.Rfix 0 = transferV3Membership` is a deliberate load-bearing `rfl` (the bare face
the STARK-side `algoStarkSound_kernel` enumerates); an in-place flip is UNSOUND (the welded members append a
`.umemOp` that fails `MapShape`, so `side_transfer` cannot re-prove over them). `RfixAvail` is the parallel
registry; this apex is the ADDITIVE deployed-path capstone over it. Nothing bare-side reddens.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureFinal
import Dregg2.Circuit.ClosureTransferAvail

namespace Dregg2.Circuit.ClosureFinalAvail

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureFinal (lightclient_unfoolable_one)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts closedLogExtract_all_genuine)
open Dregg2.Circuit.ClosureTransferAvail (RfixAvail RfixAvail_off RfixAvail_transfer RfixAvail_burn
  closedLogExtract_transfer_closed_availFix closedLogExtract_burn_closed_availFix BurnTraceReadoutAvail
  TransferTraceReadoutAvail)
open Dregg2.Circuit.ClosureTransfer (TransferAuthorityWitness)
open Dregg2.Circuit.TransferDecodeBridge (LedgerSurfaceReadout)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Exec

set_option autoImplicit false

/-! ## §1 — `closedLogExtract_transport`: `ClosedLogExtract` transports across a registry that agrees at
the tag. `ClosedLogExtract S LH hash R e` mentions `R` ONLY as `R e` (inside `Satisfied2 hash (R e) …`),
so it is invariant under any registry that agrees at `e`. This lifts the 34 UNCHANGED tags. -/

/-- **`closedLogExtract_transport`** — from `R' e = R e`, the closed extract at `R` transports to `R'`.
Pure congruence (the descriptor at `e` is literally the same object). -/
theorem closedLogExtract_transport
    {S : CommitSurface} {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {R R' : Registry} {e : EffectIdx}
    (heq : R' e = R e) (hext : ClosedLogExtract S LH hash R e) :
    ClosedLogExtract S LH hash R' e := by
  intro minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  rw [heq] at hsat
  exact hext minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog

/-! ## §2 — the `∀ e, ClosedLogExtract … RfixAvail e` family: hardened debiting slots + transported rest. -/

section PerEffect
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}
variable {LH : List Turn → ℤ} {hash : List ℤ → ℤ}

local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-- **`closedLogExtract_all_genuine_avail`** — `∀ e, ClosedLogExtract … RfixAvail e`. The two BALANCE-
DEBITING tags (transfer 0, burn 4) ride the `ClosureTransferAvail` `_availFix` slots (availability
DISCHARGED by the deployed borrow chain); every OTHER tag is the genuine `Rfix` slot
(`closedLogExtract_all_genuine`) transported across `RfixAvail_off` (the descriptor is verbatim). The
proven per-effect `<e>_closedLog` rungs stay load-bearing (via `closedLogExtract_all_genuine`); the transfer/
burn availability discharge is now threaded to the registry the light client verifies. -/
theorem closedLogExtract_all_genuine_avail {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (availTransfer : ClosedLogExtract Slive LH hash RfixAvail 0)
    (availBurn : ClosedLogExtract Slive LH hash RfixAvail 4) :
    ∀ e, ClosedLogExtract Slive LH hash RfixAvail e := by
  intro e
  by_cases h0 : e = 0
  · subst h0; exact availTransfer
  · by_cases h4 : e = 4
    · subst h4; exact availBurn
    · exact closedLogExtract_transport (RfixAvail_off h0 h4) (closedLogExtract_all_genuine rds e)

/-! ## §3 — `ClosedWitnessAvail`: the single parametric witness floor over `RfixAvail`. -/

/-- **`ClosedWitnessAvail hash S LH pi` — the single prover-witness floor over the HARDENED registry.**
The `ClosureFinal.ClosedWitness` mirror at `RfixAvail`: the `WitnessDecodes` existence rung, the single
`ClosedLogExtract … RfixAvail pi.effect` closed-with-log extraction, and the realizable log enrichment. At
`pi.effect ∈ {0,4}` the `ext` slot is a `ClosureTransferAvail` `_availFix` slot — availability DISCHARGED
at the descriptor the light client verifies. NOT a free assertion: `closedWitnessAvail_of_readouts` builds
it from the genuine readouts + the two `_availFix` slots. -/
structure ClosedWitnessAvail
    (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    (pi : BatchPublicInputs) : Prop where
  /-- the witness→kernel-state existence rung over `RfixAvail`. -/
  wit : WitnessDecodes hash RfixAvail S pi
  /-- the single per-effect closed-with-log extraction AT the published effect, over `RfixAvail`. -/
  ext : ClosedLogExtract S LH hash RfixAvail pi.effect
  /-- the realizable `logHashInjective` log enrichment at `pi.effect`. -/
  mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
    StateDecode S pc pre post →
    ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post

/-! ## §4 — THE APEX: `lightclient_unfoolable_closed_final_avail` over `RfixAvail`. -/

/-- **`lightclient_unfoolable_closed_final_avail` — THE HARDENED CLOSED CIRCUIT-SOUNDNESS APEX.**

From a verifying batch against `vkOfRegistry RfixAvail` and EXACTLY the standard crypto foundations —
  * `StarkSound hash RfixAvail` (the audited p3 batch-STARK extraction at the deployed hardened registry;
    realizable via `AlgoStarkSoundKernelAvail.algoStarkSound_kernelAvail`, the umem memory-legs route),
  * `Poseidon2SpongeCR hash` + the `S_live` `CommitSurface` CR fields,
  * `logHashInjective LH` (carried inside `ClosedWitnessAvail.mkLog`),
  * `ClosedWitnessAvail hash S_live LH pi` (the ONE prover-witness floor, parametric in `pi.effect`) —
there EXIST decoded endpoints and a genuine FULL kernel+log transition `kstepAll pi.effect pre post` whose
endpoints commit to `(pi.pre, pi.post)`. At `pi.effect ∈ {0,4}` (transfer/burn) the transition's
availability leg (`amt ≤ bal`) is FORCED by the deployed borrow chain — the `_availFix` `ext` slot carries
NO `availOf`: `availOf` is DISCHARGED at the apex. -/
theorem lightclient_unfoolable_closed_final_avail
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash RfixAvail]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcw : ClosedWitnessAvail hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH pi)
    (hacc : verifyBatch (vkOfRegistry RfixAvail) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn := by
  -- the single published-effect refinement rung, from the single `ext`/`mkLog` of the hardened floor.
  have hrefine :
      descriptorRefines (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        hash (RfixAvail pi.effect) (kstepAll pi.effect) :=
    effectDecodeBridge_of_closedLogExtract hcw.ext hcw.mkLog
  exact lightclient_unfoolable_one hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) RfixAvail hCR kstepAll pi
    hrefine π hcw.wit hacc

/-! ## §5 — non-vacuity: `ClosedWitnessAvail` is BUILT from the genuine readouts + the `_availFix` slots.

`closedWitnessAvail_of_readouts` constructs a `ClosedWitnessAvail` whose `ext` is
`closedLogExtract_all_genuine_avail … pi.effect` — at tags 0/4 the `ClosureTransferAvail` `_availFix`
slots (availability DISCHARGED), elsewhere the genuine `Rfix` bundle (every proven `<e>_closedLog` rung
load-bearing). So the hardened apex is non-vacuous AND the transfer/burn availability discharge is the
one the apex consumes. -/

/-- **`closedWitnessAvail_of_readouts`** — the hardened witness floor BUILT from the genuine per-effect
readouts (`ClosureReadouts`) + the two `ClosureTransferAvail` `_availFix` slots. Its `ext` routes through
`closedLogExtract_all_genuine_avail`, so at the debiting tags it CALLS the availability-discharged slot and
at every other tag the proven `<e>_closedLog` rung. Witnesses `ClosedWitnessAvail` NON-VACUOUS. -/
theorem closedWitnessAvail_of_readouts {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (availTransfer : ClosedLogExtract Slive LH hash RfixAvail 0)
    (availBurn : ClosedLogExtract Slive LH hash RfixAvail 4)
    (mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode Slive pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog Slive LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs)
    (hwitdec : WitnessDecodes hash RfixAvail Slive pi) :
    ClosedWitnessAvail hash Slive LH pi where
  wit := hwitdec
  ext := closedLogExtract_all_genuine_avail rds availTransfer availBurn pi.effect
  mkLog := mkLog

end PerEffect

/-! ## §6 — axiom hygiene. -/

#assert_axioms closedLogExtract_transport
#assert_axioms closedLogExtract_all_genuine_avail
#assert_axioms lightclient_unfoolable_closed_final_avail
#assert_axioms closedWitnessAvail_of_readouts

end Dregg2.Circuit.ClosureFinalAvail
