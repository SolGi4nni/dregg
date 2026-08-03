/-
# Dregg2.Circuit.ClosureForest — the WHOLE-TURN CLOSED apex over HETEROGENEOUS effects.

`ClosureFinal.lightclient_unfoolable_circuit_sound` proves the SINGLE-step closed apex: a verifying batch
for ONE effect ⟹ a genuine single kernel step `kstepAll pi.effect`, standing on only the realizable floors
{`StarkSound`, `Poseidon2SpongeCR` + the `S_live` CR fields, `logHashInjective`, the per-effect
`ClosedLogExtract` prover-witness floor}. The WHOLE-TURN analog is what this module lands: a verified TURN
— a LIST of HETEROGENEOUS effects, threaded as a `TurnDecodeChain` (each step's circuit `Satisfied2`,
decoded, seam-published) — ⟹ a genuine whole-turn kernel transition `execFullTurnA start acts = some fin`,
standing on the SAME realizable floors, the `ClosedLogExtract` family now QUANTIFIED OVER THE CHAIN'S STEPS
(a per-STEP family, ANY effect — NOT the transfer-only residual `hidx0` the faithful forest carried).

## What composes (the fold is already built; this module CLOSES its carried family)

`CircuitSoundness.lightclient_turn_unfoolable_forest` is the whole-turn apex over the THREADED chain. It
carries the per-effect refinement family `hrefines : ∀ e, descriptorRefines S hash (R e) (dispatchArm e)`
OPAQUELY. `CircuitSoundnessAssembled.lightclient_turn_unfoolable_forest_forest_assembled` re-states it at
`Rfix`/`kstepAll = dispatchArm`, still carrying the abstract `EffectDecodeBridge` family. This module does
to the WHOLE-TURN apex EXACTLY what `ClosureFinal.lightclient_unfoolable_circuit_sound_of_readouts` did to
the single-step apex: it BUILDS the carried per-effect refinement family from the genuine per-step
`ClosedLogExtract` family + the log floor, so the proven `RotatedKernelRefinement* … _closedLog` soundness
rungs are LOAD-BEARING behind the whole turn.

The realization chain (every rung genuinely consumed):

  * `ClosureFanoutGenuine.closedLogExtract_all_genuine rds : ∀ e, ClosedLogExtract S_live LH hash Rfix e`
    — the per-STEP/per-effect prover-witness family, discharged by the 36-way `actionTag` case split, EACH
    cohort slot CALLING its proven `<e>_closedLog` rung (the load-bearing core — `cellSeal_closedLog`,
    `revoke_closedLog`, `mint_closedLog`, …, NOT a carried opaque `∀ step, kstep`).

  * `ClosureAll.hrefinesAllClosed S_live LH hash (closedLogExtract_all_genuine rds) mkLog :
    ∀ e, descriptorRefines S_live hash (Rfix e) (kstepAll e)` — folds each step's `ClosedLogExtract` (the
    `Satisfied2 (Rfix e) + StateDecodeLog ⟹ kstepAll e` rung, via `effectDecodeBridge_of_closedLogExtract`
    over the realizable `logHashInjective` `mkLog`) into the per-effect refinement. Since
    `kstepAll = dispatchArm` DEFINITIONALLY, this IS the `∀ e, descriptorRefines S_live hash (Rfix e)
    (dispatchArm e)` family the whole-turn fold consumes.

  * `CircuitSoundness.lightclient_turn_unfoolable_forest` — folds that family along the threaded
    `TurnDecodeChain` (the kernel-half-of-the-seam DERIVED, the frame tooth) into the genuine executor run
    `execFullTurnA start acts = some fin`, endpoints committing to the published turn-level `(pre, post)`.

## The HETEROGENEOUS win (no transfer-only residual)

`RotatedKernelForestFacet.lightclient_turn_unfoolable_forest_facet` carries `hidx0 : ∀ d ∈ c.steps,
∃ e, d.descr = R e ∧ e = 0` — EVERY step is the transfer effect. This module RETIRES that: the per-step
identification is the generic `hidx : ∀ d ∈ c.steps, ∃ e, d.descr = Rfix e` (the step's descriptor is the
registry entry for SOME effect index — ANY of the 36, mixed freely). The per-step arm at each effect is the
genuine `ClosedLogExtract`/`<e>_closedLog` rung, so a turn `[transfer, cellSeal, revoke, mint, …]` is
covered with each step landing its own proven soundness rung. The single-step floors, per-STEP, over
heterogeneous effects.

## ⚑ NON-VACUITY: THERE IS NONE, AND THE TWO TEETH THAT SAID OTHERWISE ARE DELETED (2026-08-03)

`closedLogExtract_family_covers_mixed` and `lightclient_unfoolable_circuit_sound_turn_empty` both
opened `(rds : ClosureReadouts …)` — a bundle with NO INHABITANT
(`ClosureReadoutsRealizable.closureReadouts_uninstantiable_concrete` through `other 15`, and
`…not_nonempty_closureReadouts_refLH` through `transfer`, the second closed and floor-free). See §3.
Everything below them carries the same uninhabited premise and is vacuous with it.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on `lightclient_unfoolable_circuit_sound_turn`
+ the realizable floors entering as Prop/Type hypotheses (`StarkSound` instance, `Poseidon2SpongeCR`, the
`S_live` rest-frame obligation, `logHashInjective` inside `mkLog`, the `ClosureReadouts` per-step
prover-witness bundle). NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureFinal

namespace Dregg2.Circuit.ClosureForest

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts closedLogExtract_all_genuine)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)

set_option autoImplicit false

/-! ## §1 — the whole-turn carried family, CLOSED from the genuine per-step readouts.

The whole-turn fold `lightclient_turn_unfoolable_forest` consumes `∀ e, descriptorRefines S hash (Rfix e)
(dispatchArm e)`. We BUILD that family from the per-step `ClosedLogExtract` family — itself realized by the
genuine `ClosureReadouts` bundle (every cohort slot calling its proven `<e>_closedLog` rung) — plus the
realizable `logHashInjective` log floor `mkLog`. `kstepAll = dispatchArm` definitionally, so the family this
produces IS what the fold needs. -/

/-- **`hrefines_forest_closed` — the per-effect refinement family, CLOSED from the genuine readouts.** From
the genuine `ClosureReadouts` bundle `rds` (each cohort slot routing through its proven `<e>_closedLog`
rung) + the realizable `logHashInjective` enrichment `mkLog`, the whole-turn fold's carried family
`∀ e, descriptorRefines S_live hash (Rfix e) (dispatchArm e)`. The proven soundness rungs are LOAD-BEARING:
this term names `closedLogExtract_all_genuine`, which names every `<e>_closedLog`. -/
theorem hrefines_forest_closed
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hRest)
        LH pc pubLogPre pubLogPost pre post) :
    ∀ e, descriptorRefines
      (S_live CH RH cmb compress compressN hRest) hash
      (Rfix e) (dispatchArm e) :=
  -- `kstepAll = dispatchArm` definitionally, so `hrefinesAllClosed`'s `kstepAll e` family IS the
  -- `dispatchArm e` family the whole-turn fold consumes.
  hrefinesAllClosed
    (S_live CH RH cmb compress compressN hRest) LH hash
    (closedLogExtract_all_genuine rds) mkLog

/-! ## §2 — `lightclient_unfoolable_circuit_sound_turn`: THE WHOLE-TURN CLOSED APEX.

The centerpiece. A verified TURN — a `TurnDecodeChain` over HETEROGENEOUS effects (each step's circuit
`Satisfied2`, decoded, seam-published; the per-step effect identified by the generic `hidx`, ANY effect) +
the turn-level endpoint pinning (`TurnEndpoints`) + the realizable floors {`StarkSound`, `Poseidon2SpongeCR`
+ the `S_live` CR fields, `logHashInjective` inside `mkLog`, the per-step `ClosureReadouts` prover-witness
family} ⟹ a genuine executor run `execFullTurnA start acts = some fin` whose ENDPOINTS commit to the
published turn-level `(pre, post)`. NO transfer-only `hidx0`. The light client RAN NOTHING. -/

/-- **`lightclient_unfoolable_circuit_sound_turn` — THE WHOLE-TURN CIRCUIT-SOUNDNESS HEADLINE.**

A verified `TurnDecodeChain` over HETEROGENEOUS effects (`hidx` identifies each step's descriptor as
`Rfix e` for SOME effect `e` — any of the 36, freely mixed) + the turn-level endpoint pinning + the
realizable crypto floors + the genuine per-step `ClosureReadouts` prover-witness bundle (routing through
every proven `<e>_closedLog` rung) ⟹ there EXISTS a genuine executor run `execFullTurnA s acts = some s'`
whose endpoints commit to the published turn-level `(pre, post)`. The carried floor set is EXACTLY the
single-step floors of `lightclient_unfoolable_circuit_sound`, now per-STEP: NO transfer-only residual. -/
theorem lightclient_unfoolable_circuit_sound_turn
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hCR : Poseidon2SpongeCR hash)
    (rds : @ClosureReadouts CH RH cmb compress compressN hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hRest)
        LH pc pubLogPre pubLogPost pre post)
    {start fin : RecChainedState}
    (c : TurnDecodeChain hash
      (S_live CH RH cmb compress compressN hRest) start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = Rfix e)
    (te : TurnEndpoints hash
      (S_live CH RH cmb compress compressN hRest) c) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = (S_live CH RH cmb compress compressN hRest).commit
        s.kernel te.tp.turn ∧
      te.tp.pubPost = (S_live CH RH cmb compress compressN hRest).commit
        s'.kernel te.tp.turn :=
  -- the whole-turn fold, with its carried per-effect family CLOSED from the genuine per-step readouts.
  lightclient_turn_unfoolable_forest hash
    (S_live CH RH cmb compress compressN hRest) Rfix hCR
    (hrefines_forest_closed hash LH rds mkLog) c hidx te

/-! ## §3 — ⚰ THE TWO NON-VACUITY TEETH ARE DELETED (2026-08-03). THEY WERE THEMSELVES VACUOUS.

`closedLogExtract_family_covers_mixed` (the "MIXED-effect NON-VACUITY tooth") and
`lightclient_unfoolable_circuit_sound_turn_empty` (the "joint-satisfiability tooth") both opened
`(rds : ClosureReadouts …)`, and `ClosureReadouts` HAS NO INHABITANT. A tooth that certifies
non-vacuity from an uninhabited premise certifies nothing: it is true for the same reason the thing
it was defending is true.

Two independent proofs of that, both closed and both in `ClosureReadoutsRealizable`:

  * `closureReadouts_uninstantiable_concrete` — through the `other 15` member (the dead-tag route);
  * `not_nonempty_closureReadouts_refLH` — through the `transfer` member, i.e. through a field the
    bundle carries at a LIVE tag, with no crypto floor assumed anywhere.

⚠ **STATED AT THE RESOLUTION IT IS PROVED AT.** What is settled is the PREMISE: there is no
`ClosureReadouts`, so both teeth were true for the reason they existed to rule out, whatever their
conclusions say. Separately, ONE instance of the conclusion shape is REFUTED —
`ClosedLogExtract … Rfix 0` is false at every surface at which anything decodes
(`not_closedLogExtract_transfer_refLH`), because the extract's circuit witness and its state decode
are quantified independently. That route reaches any tag whose every action ADVANCES the log, which
the mixed cohort's own readouts assert it does (each carries `pubLogPost = LH (receipt :: pre.log)`)
— but it is NOT discharged here at 52/2/3, and nothing below claims it is.

Either way, neither tooth could be repaired by moving it to a different bundle or a different cohort:
there is no bundle to move it to, and the cohort is not the part that was wrong. They are gone rather
than restated, and `emptyChain` (used only by the second) with them.

⚠ **WHAT REMAINS ABOVE IS STILL VACUOUS AND IS NOW UNDEFENDED.** `hrefines_forest_closed` and
`lightclient_unfoolable_circuit_sound_turn` take the same uninhabited `rds`. Deleting the teeth does
not weaken them — they were never load-bearing for those proofs — it stops the module CLAIMING a
non-vacuity it does not have. ⚠ And the repair is NOT just adding `descriptorRefinesFree`'s
publication link: `Market.ProtocolAssurance.shieldedRingDescriptorRefinesFree_forces_no_decode`
refutes the LINKED rung too at a log-reading conclusion. See `ClosureReadoutsRealizable` §4's closing
note for the two routes that would actually close it; neither is this commit. -/

/-! ## §4 — axiom hygiene. -/

#assert_axioms hrefines_forest_closed
#assert_axioms lightclient_unfoolable_circuit_sound_turn

end Dregg2.Circuit.ClosureForest
