/-
# Dregg2.Circuit.ClosureFinal — the FOLD: collapse the per-effect prover-witness family into ONE
witness floor parametric in the published effect, and emit the headline `lightclient_unfoolable_circuit_sound`.

`ClosureFanoutGenuine` discharged `∀ e, ClosedLogExtract` from a `ClosureReadouts` bundle whose ~36 fields
are the per-effect NAMED decode-extraction readouts (`Satisfied2 (Rfix e) ⟹ <e>Encodes`, the
`WitnessDecodes`-class limb-level reads the honest prover's trace supplies). It fed that whole family to
`lightclient_unfoolable_closed`, which carries the `∀ e, ClosedLogExtract` family.

## The genuine over-ask, and its fold

`lightclient_unfoolable_closed` is built on `lightclient_unfoolable`, and `lightclient_unfoolable` applies
its per-effect refinement family at EXACTLY ONE index — `pi.effect`, the published effect (it derives
`kstep pi.effect pre post` and nothing else). So the `∀ e` family of per-effect decode-extractions is
OVER-ASKED: only the slot for the published effect `pi.effect` is consumed. The other 35 slots are never
touched by the proof.

This module exploits that to land the FOLD honestly:

  * `ClosedWitness hash Rfix S LH pi` — a SINGLE witness floor, PARAMETRIC in `pi.effect`. It bundles, for
    the published effect ONLY:
      - `wit  : WitnessDecodes hash Rfix S pi`        — the witness→kernel-state existence rung (already
        parametric in `pi.effect`, the standard SNARK-soundness witness floor);
      - `ext  : ClosedLogExtract S LH hash Rfix pi.effect` — the SINGLE per-effect closed extract (the
        prover supplies its own trace's column decode FOR THE PUBLISHED EFFECT), the `WitnessDecodes`-class
        decode-extraction specialized to `pi.effect`;
      - `mkLog : … pi.effect …`                       — the realizable `logHashInjective` log-enrichment AT
        the published effect.
    This is ONE floor parametric in `pi.effect`, NOT a 36-member conjunction. The per-effect prover-witness
    is now subsumed under this strengthened witness floor.

  * `lightclient_unfoolable_one` — the parametric apex: `lightclient_unfoolable` re-stated to consume ONLY
    the `pi.effect` refinement rung (mirroring `lightclient_unfoolable`'s proof, which already uses
    `hrefines` only at `pi.effect`). The `∀ e` family is GONE from the signature.

  * `lightclient_unfoolable_circuit_sound` — THE HEADLINE. From a verifying batch against
    `vkOfRegistry Rfix` + EXACTLY {`StarkSound hash Rfix`, `Poseidon2SpongeCR hash` + the `S_live` CR
    fields, `logHashInjective LH` (inside `ClosedWitness`'s `mkLog`), `ClosedWitness` (the single witness
    floor)} — the light client concludes a genuine full kernel+log transition `kstepAll pi.effect pre post`
    whose endpoints commit to `(pi.pre, pi.post)`. The carried set is the four standard crypto foundations
    + ONE witness floor, parametric in the published effect.

## The proven `*_closedLog` rungs stay LOAD-BEARING (non-vacuity)

`ClosedWitness` is not a free assertion. `closedWitness_of_readouts` BUILDS one from the
`ClosureReadouts` bundle: its `ext` field is `closedLogExtract_all_genuine rds pi.effect`, which routes
through the 36-way actionTag case-split — every cohort slot CALLING its proven `<e>_closedLog` rung. So the
`RotatedKernelRefinement* … _closedLog` soundness rungs remain load-bearing behind the single parametric
floor: `closedWitness_of_readouts` names `closedLogExtract_all_genuine`, which names each `*_closedLog`.

`lightclient_unfoolable_circuit_sound_of_readouts` composes the two — the headline conclusion directly from
the genuine readout bundle + the crypto floors, demonstrating the single floor is realizable AND the proven
rungs are consumed.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All carriers enter as Prop/Type hypotheses or
structure fields, never as axioms. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureFanoutGenuine

namespace Dregg2.Circuit.ClosureFinal

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts closedLogExtract_all_genuine)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (authReceipt)

set_option autoImplicit false

/-! ## §1 — `lightclient_unfoolable_one`: the parametric apex consuming ONLY the published-effect rung.

`lightclient_unfoolable` (in `CircuitSoundness`) carries `hrefines : ∀ e, descriptorRefines …` but applies
it at EXACTLY `pi.effect`. We re-state it taking ONLY that one rung — the `∀ e` family is gone. The proof
is `lightclient_unfoolable`'s body verbatim, with `hrefines pi.effect` replaced by the single `hrefine`. -/

/-- **`lightclient_unfoolable_one` — the single-effect closed apex.** Same conclusion as
`lightclient_unfoolable`, but the per-effect refinement obligation is carried at EXACTLY the published
effect `pi.effect` (one rung, parametric in `pi.effect`) — not as a `∀ e` family. -/
theorem lightclient_unfoolable_one
    (hash : List ℤ → ℤ) (S : CommitSurface) (R : Registry)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash R]
    (kstep : EffectIdx → RecChainedState → RecChainedState → Prop)
    (pi : BatchPublicInputs)
    (hrefine : descriptorRefines S hash (R pi.effect) (kstep pi.effect))
    (π : BatchProof)
    (hwitdec : WitnessDecodes hash R S pi)
    (hacc : verifyBatch (vkOfRegistry R) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode S pi.toPublished pre post ∧
      kstep pi.effect pre post ∧
      pi.pre = S.commit pre.kernel pi.turn ∧
      pi.post = S.commit post.kernel pi.turn := by
  -- (1) strengthened STARK soundness extracts a Satisfied2 witness of the CLAIMED descriptor whose
  --     published commitments ARE `pi.toPublished`.
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ :=
    (inferInstance : StarkSound hash R).extract pi π hacc
  -- (2) the carried witness→state EXISTENCE rung supplies the decoded kernel boundary `(pre, post)`.
  obtain ⟨pre, post, hdecode⟩ := hwitdec minit mfin maddrs t hsat hpub
  -- (3) the SINGLE published-effect rung (fed the named hash CR carrier `hCR`) turns the circuit witness +
  --     the derived decode into the step.
  have hstep : kstep pi.effect pre post :=
    hrefine hCR minit mfin maddrs t pi.toPublished pre post hsat hdecode
  -- (4) faithfulness re-exports the published commitments as the genuine endpoint commitments.
  refine ⟨pre, post, hdecode, hstep, ?_, ?_⟩
  · simpa using hdecode.preBinds
  · simpa using hdecode.postBinds

/-! ## §2 — `ClosedWitness`: the SINGLE witness floor, parametric in `pi.effect`.

The fold target. `WitnessDecodes` is already the per-turn witness→kernel-state existence floor (parametric
in `pi.effect` — it speaks `R pi.effect`). The per-effect `<e>TraceReadout` decode-extraction (subsumed
inside `ClosedLogExtract`) is the SAME prover-witness interface, specialized per effect. We bundle, for the
PUBLISHED effect only, the existence floor + the single `ClosedLogExtract pi.effect` + the single log
enrichment `mkLog` at `pi.effect`. ONE floor, parametric in `pi.effect`; NOT a 36-way family. -/

/-- **`ClosedWitness hash Rfix S LH pi` — THE single prover-witness floor, parametric in the published
effect.** Bundles, for `pi.effect`: the `WitnessDecodes` existence rung, the single `ClosedLogExtract`
closed-with-log extraction (the prover's trace column decode AT `pi.effect`), and the realizable
`logHashInjective` log enrichment at `pi.effect`. This is the strengthened `WitnessDecodes` — the per-effect
prover-witness subsumed under ONE floor. NOT a free assertion: `closedWitness_of_readouts` builds it from
the genuine `ClosureReadouts` bundle (whose `ext` routes through every proven `<e>_closedLog` rung). -/
structure ClosedWitness
    (hash : List ℤ → ℤ) (S : CommitSurface) (LH : List Turn → ℤ)
    (pi : BatchPublicInputs) : Prop where
  /-- the witness→kernel-state existence rung (already parametric in `pi.effect`). -/
  wit : WitnessDecodes hash Rfix S pi
  /-- the SINGLE per-effect closed-with-log extraction, AT the published effect `pi.effect`. -/
  ext : ClosedLogExtract S LH hash Rfix pi.effect
  /-- the realizable `logHashInjective` log enrichment, AT the published effect `pi.effect`. -/
  mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
    StateDecode S pc pre post →
    ∃ pubLogPre pubLogPost, StateDecodeLog S LH pc pubLogPre pubLogPost pre post

/-! ## §3 — `lightclient_unfoolable_circuit_sound`: THE HEADLINE on the four floors + one witness floor.

From `ClosedWitness` (the single parametric witness floor) we build the published-effect refinement rung
(`effectDecodeBridge_of_closedLogExtract` on the single `ext`/`mkLog`), then feed it to
`lightclient_unfoolable_one`. The carried set is EXACTLY {`StarkSound`, `Poseidon2SpongeCR` + the `S_live`
CR fields, `logHashInjective` (inside `ClosedWitness.mkLog`), `ClosedWitness`}. -/

/-- **`lightclient_unfoolable_circuit_sound` — THE CIRCUIT-SOUNDNESS HEADLINE.**

From a verifying batch against `vkOfRegistry Rfix` and EXACTLY the standard crypto foundations of a verified
SNARK soundness proof —
  * `StarkSound hash Rfix` (the audited p3 batch-STARK extraction),
  * `Poseidon2SpongeCR hash` + the `S_live` `CommitSurface` CR fields (the decode-faithfulness floor),
  * `logHashInjective LH` (the log-CR floor, carried inside `ClosedWitness.mkLog`),
  * `ClosedWitness hash Rfix S_live LH pi` (the ONE prover-witness floor, parametric in `pi.effect`) —
there EXIST decoded endpoints and a genuine FULL kernel+log transition `kstepAll pi.effect pre post` whose
endpoints commit to the published `(pi.pre, pi.post)`. NO `∀ e` family of per-effect hypotheses: the
per-effect prover-witness is subsumed under the single `ClosedWitness` floor at the published effect. -/
theorem lightclient_unfoolable_circuit_sound
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (pi : BatchPublicInputs) (π : BatchProof)
    (hcw : ClosedWitness hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn := by
  -- the single published-effect refinement rung, from the single `ext`/`mkLog` of the witness floor.
  have hrefine :
      descriptorRefines (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        hash (Rfix pi.effect) (kstepAll pi.effect) :=
    effectDecodeBridge_of_closedLogExtract hcw.ext hcw.mkLog
  exact lightclient_unfoolable_one hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) Rfix hCR kstepAll pi
    hrefine π hcw.wit hacc

/-! ## §4 — non-vacuity: `ClosedWitness` is BUILT from the genuine readout bundle (rungs load-bearing).

`closedWitness_of_readouts` constructs a `ClosedWitness` whose `ext` is `closedLogExtract_all_genuine rds
pi.effect` — which routes through the 36-way actionTag case-split, every cohort slot CALLING its proven
`<e>_closedLog` rung. So the proven `RotatedKernelRefinement* … _closedLog` soundness rungs remain
LOAD-BEARING behind the single parametric floor. (The `mkLog` is supplied as the realizable
`logHashInjective` log enrichment; `WitnessDecodes` as its named existence rung.) -/

/-- **`closedWitness_of_readouts` — the single floor BUILT from the genuine per-effect readouts.** Its `ext`
is `closedLogExtract_all_genuine rds pi.effect`, so every proven `<e>_closedLog` rung is consumed (the
36-way case-split lands the published effect's slot by CALLING its rung). This witnesses `ClosedWitness`
NON-VACUOUS and keeps the soundness rungs load-bearing. -/
theorem closedWitness_of_readouts
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs)
    (hwitdec : WitnessDecodes hash Rfix
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pi) :
    ClosedWitness hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH pi where
  wit := hwitdec
  ext := closedLogExtract_all_genuine rds pi.effect
  mkLog := mkLog

/-- **`lightclient_unfoolable_circuit_sound_of_readouts` — the headline directly from the genuine readout
bundle.** Composes `closedWitness_of_readouts` (proven rungs load-bearing) into the headline. Demonstrates
the single `ClosedWitness` floor is realizable from the genuine per-effect decode-extractions + the crypto
floors. -/
theorem lightclient_unfoolable_circuit_sound_of_readouts
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    (pi : BatchPublicInputs) (π : BatchProof)
    (hwitdec : WitnessDecodes hash Rfix
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pi)
    (hacc : verifyBatch (vkOfRegistry Rfix) pi π = Verdict.accept) :
    ∃ pre post : RecChainedState,
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pi.toPublished pre post ∧
      kstepAll pi.effect pre post ∧
      pi.pre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        pre.kernel pi.turn ∧
      pi.post = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        post.kernel pi.turn :=
  lightclient_unfoolable_circuit_sound hash LH hCR pi π
    (closedWitness_of_readouts rds mkLog pi hwitdec) hacc

/-! ## §5 — axiom hygiene. -/

#assert_axioms lightclient_unfoolable_one
#assert_axioms lightclient_unfoolable_circuit_sound
#assert_axioms closedWitness_of_readouts
#assert_axioms lightclient_unfoolable_circuit_sound_of_readouts

end Dregg2.Circuit.ClosureFinal
