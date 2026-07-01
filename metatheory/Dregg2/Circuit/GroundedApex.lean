/-
# Dregg2.Circuit.GroundedApex — the apex re-rested on the FOUR proven carrier-reductions.

This module is the PAYOFF weld: it makes the four dregg-specific apex carriers — each independently
reduced to the crypto floor in its own `#assert_axioms`-clean module this session — LOAD-BEARING at
the apex, ADDITIVELY. It edits NOTHING upstream; it imports the four reduction homes + the apex
read-only and builds GROUNDED variants beside them, so the existing apex (and its every downstream
caller) is untouched. The main loop wires the import + migrates callers.

## What "grounded" means (the boundary shrink)

The two apex headlines — `RecursiveAggregation.light_client_verifies_whole_history` (whole-history) and
`CircuitSoundness.lightclient_unfoolable` (single-transition) — each rest on assumed legs that LOOK like
soundness boundaries but were SHRUNK this session:

  * `EngineSound.binding_sound` (the chain-ordering tooth) → DISCHARGED by
    `BindingAirSound.binding_air_discharges_binding_sound` (a satisfying represented `TurnChainBindingAir`
    trace FORCES `ChainBound` + the genesis/final pins — NO crypto at all).
  * `EngineSound.leaf_sound` (the per-leaf executor binding) → DERIVED by
    `WitnessRealizing.engineSound_of_refinements` from a `Forall₂ LeafRefinement` (the per-effect
    `descriptorRefines` family + the structural position fold).
  * `EngineSound.recursive_sound` (the FRI recursive-verifier soundness) → the SAME named FRI carrier
    `RecursiveVerifierSound`, whose per-NODE content `AggAirSound.segsound_node_discharged` opens to
    `{FriExtract floor ⊕ the PROVEN segment-combine gates}`. Carried here as the named hypothesis `hrec`
    (the whole-tree fold from per-node `FriExtract` to the root→all-leaves shape is the named residual —
    NOT axiomatized; see the report). It is the only assumed leg of the whole-history grounded apex, and
    it is exactly the standard FRI/recursion floor.
  * `CircuitSoundness.WitnessDecodes` (the witness→kernel-state existence rung) → REALIZED by
    `WitnessRealizing.lightclient_unfoolable_witness_realized` from the honest prover's genuine
    `recStateCommit`-bound kernels.
  * the registry-wide `∀ e, descriptorRefines (Rfix e) (kstepAll e)` → PROVEN WHOLE by
    `DescriptorRefinesComplete.descriptorRefines_complete` (all deployed effect tags, no catch-all).

The grounded apexes below consume those reductions, so a DEPLOYED light client trusts only
{FRI/recursion soundness, Poseidon2-sponge collision-resistance, the standard `CommitSurface` Poseidon CR
set} + the realizer DATA an honest prover supplies (the represented binding trace, the per-effect
`LeafRefinement`/`ClosureReadouts` family, the genuine committed kernels) — NO assumed `EngineSound`
legs, NO assumed `WitnessDecodes`, NO per-effect refinement parking lot.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); every carrier enters as a Prop/struct
hypothesis, NO fresh axiom, NO `sorry`. Standalone: `lake build Dregg2.Circuit.GroundedApex`.
-/
import Dregg2.Circuit.BindingAirSound
import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.WitnessRealizing
import Dregg2.Circuit.DescriptorRefinesComplete
import Dregg2.Circuit.RecursiveSoundFromNodes

namespace Dregg2.Circuit.GroundedApex

open Dregg2.Circuit.CircuitSoundness
  (CommitSurface StateDecode descriptorRefines WitnessDecodes BatchPublicInputs BatchProof
   PublishedCommit Verdict verifyBatch vkOfRegistry StarkSound Registry EffectIdx)
open Dregg2.Circuit.RecursiveAggregation
  (EngineSound Aggregate AggregateAttests light_client_verifies_whole_history
   acceptAll RealProof realAggregate realSteps zCH zRH zcmb zcompress zcompressN)
open Dregg2.Circuit.BindingAirSound
  (BindingRow BindingPublic Satisfies Represents binding_air_discharges_binding_sound
   foldedFinalRoot_eq_lastNew satisfies_one represents_one rowOf pubOf)
open Dregg2.Circuit.WitnessRealizing
  (LeafRefinement engineSound_of_refinements lightclient_unfoolable_witness_realized
   emptyState emptyKernel_wf genuinePi)
open Dregg2.Circuit.DescriptorRefinesComplete (DescriptorRefinesComplete descriptorRefines_complete)
open Dregg2.Circuit.RecursiveSoundFromNodes
  (PTree NodeCarrier rootP leavesP recursive_sound_from_nodes engineSound_recursive_derived
   honestTree honest_node_carrier)
open Dregg2.Circuit.CircuitSoundnessAssembled (Rfix kstepAll)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit
  (AccountsWF compressInjective compressNInjective cellLeafInjective RestHashIffFrame)
open Dregg2.Distributed.HistoryAggregation (ChainStep ChainBound stateRoot zeroTurn foldedFinalRoot)
open Dregg2.Exec (RecChainedState RecordKernelState CellId Value Turn recCexec)
open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)
open Dregg2.Distributed.HistoryAggregation (honestStep)

set_option autoImplicit false

/-! ## §1 — the binding-AIR extraction carrier (the realizer DATA the grounded binding leg consumes).

`EngineSound.binding_sound` is `verify bindingProof = true → ChainBound + pins`. The grounded leg discharges
it by `binding_air_discharges_binding_sound` once it has a SATISFYING REPRESENTED binding-AIR trace whose
public roots are the aggregate's. That extraction — a verifying binding leaf yields such a trace — is the
binding AIR's in-circuit soundness, the chain-binding analog of `StarkSound`/`AggAirSound.FriExtract`;
named here, not assumed inside `EngineSound`. -/

/-- **`BindingExtract`** — a verifying `TurnChainBindingAir` leaf yields a satisfying represented trace
(`Satisfies` + `Represents` over the chain `steps`) whose public inputs are the aggregate's published
genesis/final roots. The realizer DATA the grounded binding leg takes; the keystone
`binding_air_discharges_binding_sound` then FORCES the `binding_sound` conclusion from it. -/
def BindingExtract (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (steps : List ChainStep) : Prop :=
  verify agg.bindingProof = true →
    ∃ (rows : List BindingRow) (pub : BindingPublic),
      Satisfies hash rows pub
        ∧ Represents CH RH cmb compress compressN rows steps
        ∧ agg.genesisRoot = pub.genesis
        ∧ agg.finalRoot = pub.final

/-! ## §2 — `engineSound_grounded`: `EngineSound` with `binding_sound` + `leaf_sound` DERIVED. -/

/-- **`engineSound_grounded`** — the recursion-engine soundness bundle with TWO of its three legs DERIVED
from realizer data, not assumed:

  * `leaf_sound` — from the `Forall₂ LeafRefinement` family (`hleaves`), via
    `engineSound_of_refinements` (the per-effect `descriptorRefines` rung + the structural position fold).
  * `binding_sound` — from the binding-AIR extraction `hbindExtract`, via the keystone
    `binding_air_discharges_binding_sound` (which FORCES `ChainBound` + the genesis/final pins; the pins
    re-export through the aggregate's published roots `hgen`/`hfin`).

The third leg `recursive_sound` is supplied as `hrec` — the named FRI recursive-verifier carrier
(`RecursiveVerifierSound`), whose per-node content `AggAirSound.segsound_node_discharged` opens to
`{FriExtract ⊕ proven combine}`; it is the only assumed leg, and it is the standard recursion floor. -/
theorem engineSound_grounded
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract Proof verify hash CH RH cmb compress compressN agg steps)
    (hrec : verify agg.root = true →
      (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true) :
    EngineSound Proof verify CH RH cmb compress compressN agg g steps :=
  engineSound_of_refinements Proof verify hash S hCR CH RH cmb compress compressN agg g steps
    hleaves hrec
    (fun hv => by
      obtain ⟨rows, pub, hsat, hrep, hgen, hfin⟩ := hbindExtract hv
      obtain ⟨hbound, hg, hf⟩ :=
        binding_air_discharges_binding_sound CH RH cmb compress compressN hash rows pub steps g hsat hrep
      exact ⟨hbound, hgen.trans hg, hfin.trans hf⟩)

/-! ## §2b — `engineSound_grounded_v2`: ALL THREE legs derived — `recursive_sound` off the per-node fold.

`engineSound_grounded` (§2) still carries the FRI-composition leg `hrec` (`= recursive_sound`). This v2
DROPS `hrec` and instead consumes the proof-carrying aggregation tree `t` + the per-node `NodeCarrier`
(the localized `AggAirSound.FriExtract` floor) + the wrapping facts; `RecursiveSoundFromNodes.recursive_sound_from_nodes`
runs the WHOLE-TREE fold (`all_leaves_verify`) over them to PRODUCE the exact `hrec` shape, which it then
hands to `engineSound_grounded`. So the engine is assembled with NO carried `EngineSound` leg: `leaf_sound`
is derived from the refinement family, `binding_sound` from the binding-AIR extraction, and `recursive_sound`
from the per-node carrier fold. The remaining floor is the PER-NODE carrier `hc` (the standard in-circuit
recursion-verifier soundness, localized to one node + its two children — strictly smaller than the carried
whole-tree `hrec`) + the realizer data, NO whole-tree FRI-composition hypothesis. -/
theorem engineSound_grounded_v2
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (H : ℤ → ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract Proof verify hash CH RH cmb compress compressN agg steps)
    (t : PTree Proof)
    (hc : NodeCarrier verify H t)
    (htroot : rootP t = agg.root)
    (hwrap : ∀ p ∈ agg.leafProofs, p ∈ leavesP t)
    (hbind : agg.bindingProof ∈ leavesP t) :
    EngineSound Proof verify CH RH cmb compress compressN agg g steps :=
  engineSound_grounded Proof verify hash S hCR CH RH cmb compress compressN agg g steps
    hleaves hbindExtract
    (recursive_sound_from_nodes verify H agg t hc htroot hwrap hbind)

/-! ## §3 — `light_client_verifies_whole_history_grounded`: the whole-history apex on the grounded engine. -/

/-- **`light_client_verifies_whole_history_grounded` (THE GROUNDED WHOLE-HISTORY APEX).** Same conclusion
as `RecursiveAggregation.light_client_verifies_whole_history` — a light client checking ONLY
`verify agg.root = true` obtains `AggregateAttests` (every turn executed, the chain is ordered, the final
root is the genuine fold) — but resting on NO assumed `EngineSound` legs: only the named FRI carrier
`hrec`, the Poseidon CR floor `hCR`, and the realizer DATA (`hleaves` = the per-effect refinement family,
`hbindExtract` = the represented binding trace). The whole-history attestation now trusts only the crypto
floor + the honest prover's witnesses. -/
theorem light_client_verifies_whole_history_grounded
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract Proof verify hash CH RH cmb compress compressN agg steps)
    (hrec : verify agg.root = true →
      (∀ p ∈ agg.leafProofs, verify p = true) ∧ verify agg.bindingProof = true)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps :=
  light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps
    (engineSound_grounded Proof verify hash S hCR CH RH cmb compress compressN agg g steps
      hleaves hbindExtract hrec)
    hroot

/-- **`light_client_verifies_whole_history_grounded_v2` (THE GROUNDED WHOLE-HISTORY APEX — NO CARRIED FRI).**
Same conclusion as `light_client_verifies_whole_history_grounded`, but the whole-tree FRI hypothesis `hrec`
is GONE: in its place the per-node `NodeCarrier hc` over the proof-carrying tree `t` (+ the wrapping facts),
from which `engineSound_grounded_v2` DERIVES `recursive_sound` by the whole-tree fold. The deployed light
client now rests on `{the per-node FriExtract floor `hc`, Poseidon CR `hCR`}` + realizer data (`hleaves`,
`hbindExtract`) — every `EngineSound` leg DERIVED, no carried whole-tree recursion hypothesis. -/
theorem light_client_verifies_whole_history_grounded_v2
    (Proof : Type) (verify : Proof → Bool) (hash : List ℤ → ℤ) (S : CommitSurface)
    (hCR : Poseidon2SpongeCR hash)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (H : ℤ → ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement Proof verify hash S p s))
      agg.leafProofs steps)
    (hbindExtract : BindingExtract Proof verify hash CH RH cmb compress compressN agg steps)
    (t : PTree Proof)
    (hc : NodeCarrier verify H t)
    (htroot : rootP t = agg.root)
    (hwrap : ∀ p ∈ agg.leafProofs, p ∈ leavesP t)
    (hbind : agg.bindingProof ∈ leavesP t)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps :=
  light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps
    (engineSound_grounded_v2 Proof verify hash S hCR CH RH cmb compress compressN H agg g steps
      hleaves hbindExtract t hc htroot hwrap hbind)
    hroot

/-! ## §4 — `lightclient_unfoolable_grounded`: the single-transition apex with `WitnessDecodes` REALIZED. -/

/-- **`lightclient_unfoolable_grounded` (THE GROUNDED SINGLE-TRANSITION APEX).** Every accepted batch
decodes to a GENUINE kernel step committing to `pi.pre`/`pi.post` — with `WitnessDecodes` GONE from the
hypothesis list, replaced by the honest prover's genuine `recStateCommit`-bound kernels `pre₀`/`post₀`
(the realizer `WitnessRealizing.lightclient_unfoolable_witness_realized` discharges the existence rung
internally). The remaining floor is exactly {audited `StarkSound`, the per-effect `descriptorRefines`
family `hrefines`, `Poseidon2SpongeCR`} — no assumed witness→state surjectivity. -/
theorem lightclient_unfoolable_grounded
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (pi : BatchPublicInputs) (π : BatchProof)
    (pre₀ post₀ : RecChainedState)
    (hpreWF : AccountsWF pre₀.kernel) (hpostWF : AccountsWF post₀.kernel)
    (hpre : pi.pre = S.commit pre₀.kernel pi.turn)
    (hpost : pi.post = S.commit post₀.kernel pi.turn)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn :=
  lightclient_unfoolable_witness_realized hash S R hCR kstep hrefines pi π
    pre₀ post₀ hpreWF hpostWF hpre hpost hacc

/-- **`lightclient_unfoolable_grounded_live` (THE GROUNDED SINGLE-TRANSITION APEX ON THE LIVE SURFACE).**
The grounded apex over the DEPLOYED surface `S_live` and registry `Rfix`, with the per-effect refinement
family no longer an assumed hypothesis but PROVEN WHOLE by `DescriptorRefinesComplete.descriptorRefines_complete`
(every deployed effect tag routes to its own genuine `<e>_closedLog` rung — no catch-all). What remains is
{audited `StarkSound`, `Poseidon2SpongeCR`, the standard `CommitSurface` CR set, the named `ClosureReadouts`
limb-decode carriers `rds` + the log-floor `mkLog`} + the genuine committed kernels. The whole per-effect
soundness column is now PROVEN, not carried. -/
theorem lightclient_unfoolable_grounded_live
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (pi : BatchPublicInputs) (π : BatchProof)
    (pre₀ post₀ : RecChainedState)
    (hpreWF : AccountsWF pre₀.kernel) (hpostWF : AccountsWF post₀.kernel)
    (hpre : pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
      pre₀.kernel pi.turn)
    (hpost : pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
      post₀.kernel pi.turn)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn :=
  lightclient_unfoolable_grounded hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) Rfix hCR kstepAll
    (descriptorRefines_complete hash LH rds mkLog) pi π
    pre₀ post₀ hpreWF hpostWF hpre hpost hacc

/-! ## §5 — NON-VACUITY: the grounded apexes FIRE on a real honest chain (audited floors named).

The grounded headlines would be hollow if no realizer data inhabited them. We exercise each on the honest
teeth-genesis chain (reusing the reduction files' honest instances), leaving exactly the named audited
floor (a `Satisfied2` witness under an accepting verifier / an accepting `verifyBatch`) — never a hole. -/

section Vacuity

/-- **`engineSound_grounded_constructs` (the engine constructor FIRES).** On the honest 1-step chain
(`teethGenesis ⟶ honestStep.post`), `engineSound_grounded` PRODUCES a genuine `EngineSound` over a
rejecting verifier — the leaf realizer is the concrete `WitnessRealizing.rejectLeaf`, the binding/recursion
legs are vacuous under rejection. So the grounded constructor is inhabited on a real executor run; it is
not an empty over-ask. (The accepting-verifier firing — which DOES exercise the binding keystone — is
`grounded_light_client_fires` below.) -/
theorem engineSound_grounded_constructs
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (d : Dregg2.Circuit.DescriptorIR2.EffectVmDescriptor2) :
    EngineSound Unit WitnessRealizing.rejectAll zCH zRH zcmb zcompress zcompressN
      { root := (), leafProofs := [()], bindingProof := ()
      , genesisRoot := 0, finalRoot := 0, chainDigest := 0, numTurns := 1 }
      teethGenesis [honestStep] :=
  engineSound_grounded Unit WitnessRealizing.rejectAll hash S hCR
    zCH zRH zcmb zcompress zcompressN _ teethGenesis [honestStep]
    (List.Forall₂.cons ⟨WitnessRealizing.rejectLeaf hash S d honestStep⟩ List.Forall₂.nil)
    (fun h => by simp [WitnessRealizing.rejectAll] at h)
    (fun h => by simp [WitnessRealizing.rejectAll] at h)

/-- **`grounded_light_client_fires` (THE GROUNDED WHOLE-HISTORY APEX FIRES).** On the honest chain, with
an ACCEPTING verifier, `light_client_verifies_whole_history_grounded` fires and concludes a TRUE executor
fact — `recCexec teethGenesis honestTurn = some honestStep.post`. The binding-AIR extraction is discharged
CONCRETELY (`satisfies_one`/`represents_one` over the honest step — so the keystone
`binding_air_discharges_binding_sound` is genuinely load-bearing), and the only non-concrete input is the
per-leaf `Forall₂ LeafRefinement` under the accepting verifier — the SAME audited `Satisfied2`/STARK floor
every module here carries (named `hleaves`, not a hole). -/
theorem grounded_light_client_fires
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement RealProof acceptAll hash S p s))
      (realAggregate.leafProofs) realSteps) :
    recCexec teethGenesis honestTurn = some honestStep.post := by
  have hbe : BindingExtract RealProof acceptAll hash zCH zRH zcmb zcompress zcompressN
      realAggregate realSteps := by
    intro _
    refine ⟨[rowOf zCH zRH zcmb zcompress zcompressN honestStep],
            pubOf zCH zRH zcmb zcompress zcompressN hash honestStep,
            satisfies_one zCH zRH zcmb zcompress zcompressN hash honestStep,
            represents_one zCH zRH zcmb zcompress zcompressN honestStep, rfl, ?_⟩
    show realAggregate.finalRoot = (pubOf zCH zRH zcmb zcompress zcompressN hash honestStep).final
    simp only [realAggregate, pubOf, realSteps]
    exact foldedFinalRoot_eq_lastNew zCH zRH zcmb zcompress zcompressN teethGenesis [honestStep]
      honestStep (by simp)
  have hrec : acceptAll realAggregate.root = true →
      (∀ p ∈ realAggregate.leafProofs, acceptAll p = true)
        ∧ acceptAll realAggregate.bindingProof = true :=
    fun _ => ⟨fun _ _ => rfl, rfl⟩
  have hatt := light_client_verifies_whole_history_grounded RealProof acceptAll hash S hCR
    zCH zRH zcmb zcompress zcompressN realAggregate teethGenesis realSteps
    hleaves hbe hrec rfl
  have h := hatt.every_turn honestStep (by simp [realSteps])
  simpa [honestStep] using h

/-- **`grounded_light_client_fires_v2` (THE NO-CARRIED-FRI WHOLE-HISTORY APEX FIRES).** As
`grounded_light_client_fires`, but through `light_client_verifies_whole_history_grounded_v2`: the carried
`hrec` is replaced by the concrete honest proof-carrying tree `honestTree` and its per-node carrier
`honest_node_carrier` (the `[1→2] ⋆ [2→3]` honest combine of `RecursiveSoundFromNodes`). So the whole-tree
recursion fold is genuinely LOAD-BEARING in the firing — `recursive_sound` is DERIVED, not supplied — and
the apex still concludes the TRUE executor fact `recCexec teethGenesis honestTurn = some honestStep.post`.
The only non-concrete input remains the per-leaf `Forall₂ LeafRefinement` (the audited STARK floor). -/
theorem grounded_light_client_fires_v2
    (hash : List ℤ → ℤ) (S : CommitSurface) (hCR : Poseidon2SpongeCR hash)
    (hleaves : List.Forall₂ (fun p s => Nonempty (LeafRefinement RealProof acceptAll hash S p s))
      (realAggregate.leafProofs) realSteps) :
    recCexec teethGenesis honestTurn = some honestStep.post := by
  have hbe : BindingExtract RealProof acceptAll hash zCH zRH zcmb zcompress zcompressN
      realAggregate realSteps := by
    intro _
    refine ⟨[rowOf zCH zRH zcmb zcompress zcompressN honestStep],
            pubOf zCH zRH zcmb zcompress zcompressN hash honestStep,
            satisfies_one zCH zRH zcmb zcompress zcompressN hash honestStep,
            represents_one zCH zRH zcmb zcompress zcompressN honestStep, rfl, ?_⟩
    show realAggregate.finalRoot = (pubOf zCH zRH zcmb zcompress zcompressN hash honestStep).final
    simp only [realAggregate, pubOf, realSteps]
    exact foldedFinalRoot_eq_lastNew zCH zRH zcmb zcompress zcompressN teethGenesis [honestStep]
      honestStep (by simp)
  -- the carried `hrec` is GONE: the recursion leg comes from the concrete honest tree + per-node carrier.
  have hatt := light_client_verifies_whole_history_grounded_v2 RealProof acceptAll hash S hCR
    zCH zRH zcmb zcompress zcompressN RecursiveSoundFromNodes.zH
    realAggregate teethGenesis realSteps hleaves hbe
    honestTree honest_node_carrier rfl
    (by intro p _; cases p; simp [leavesP, honestTree])
    (by simp [leavesP, honestTree, realAggregate])
    rfl
  have h := hatt.every_turn honestStep (by simp [realSteps])
  simpa [honestStep] using h

/-- **`lightclient_unfoolable_grounded_fires` (THE GROUNDED SINGLE-TRANSITION APEX FIRES).** On the
genuine empty-cell boundary (`emptyState ⟶ emptyState`, whose `recStateCommit`-bound roots are CONCRETE —
`emptyKernel_wf`), `lightclient_unfoolable_grounded` fires: the witness→state realizer is discharged with
NO assumption, leaving only the audited `StarkSound` + the accepting batch `hacc` as the named floor. So
the grounded single-transition apex is non-vacuously inhabited on a real `recStateCommit`-bound state. -/
theorem lightclient_unfoolable_grounded_fires
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (hrefines : ∀ e, descriptorRefines S hash (R e) (kstep e))
    (π : BatchProof) (t : Turn)
    (hacc : verifyBatch (vkOfRegistry R) (genuinePi S t) π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S (genuinePi S t).toPublished pre post ∧
      kstep (genuinePi S t).effect pre post ∧
      (genuinePi S t).pre = S.commit pre.kernel (genuinePi S t).turn ∧
      (genuinePi S t).post = S.commit post.kernel (genuinePi S t).turn :=
  lightclient_unfoolable_grounded hash S R hCR kstep hrefines (genuinePi S t) π
    emptyState emptyState emptyKernel_wf emptyKernel_wf rfl rfl hacc

end Vacuity

/-! ## §6 — Axiom hygiene (every grounded apex `#assert_axioms`-clean: no fresh axiom). -/

#assert_axioms engineSound_grounded
#assert_axioms engineSound_grounded_v2
#assert_axioms light_client_verifies_whole_history_grounded
#assert_axioms light_client_verifies_whole_history_grounded_v2
#assert_axioms lightclient_unfoolable_grounded
#assert_axioms lightclient_unfoolable_grounded_live
-- non-vacuity (the grounded apexes fire on a real honest chain):
#assert_axioms engineSound_grounded_constructs
#assert_axioms grounded_light_client_fires
#assert_axioms grounded_light_client_fires_v2
#assert_axioms lightclient_unfoolable_grounded_fires

end Dregg2.Circuit.GroundedApex
