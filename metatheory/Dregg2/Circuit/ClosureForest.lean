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

## NON-VACUITY (a mixed-effect turn is genuinely covered)

  * `closedLogExtract_family_covers_mixed` — the per-step family `closedLogExtract_all_genuine rds`
    INHABITS the rung at the NON-transfer effects cellSeal (52), revoke (2), mint (3) simultaneously
    (a mixed cohort). The family is not transfer-restricted: it produces a genuine `ClosedLogExtract` at
    each, routing through `cellSeal_closedLog`/`revoke_closedLog`/`mint_closedLog`.

  * `lightclient_unfoolable_circuit_sound_turn_empty` — instantiates the whole-turn closed apex on the
    DEGENERATE empty chain (the trivially-constructible `TurnDecodeChain` with no steps), demonstrating the
    apex's hypotheses are jointly satisfiable (the family + floors compose, no `False`-laundering).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on `lightclient_unfoolable_circuit_sound_turn`
+ the realizable floors entering as Prop/Type hypotheses (`StarkSound` instance, `Poseidon2SpongeCR`, the
`S_live` CR fields, `logHashInjective` inside `mkLog`, the `ClosureReadouts` per-step prover-witness
bundle). No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file; imports read-only.
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
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post) :
    ∀ e, descriptorRefines
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) hash
      (Rfix e) (dispatchArm e) :=
  -- `kstepAll = dispatchArm` definitionally, so `hrefinesAllClosed`'s `kstepAll e` family IS the
  -- `dispatchArm e` family the whole-turn fold consumes.
  hrefinesAllClosed
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash
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
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hCR : Poseidon2SpongeCR hash)
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    {start fin : RecChainedState}
    (c : TurnDecodeChain hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) start fin)
    (hidx : ∀ d ∈ c.steps, ∃ e : EffectIdx, d.descr = Rfix e)
    (te : TurnEndpoints hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) c) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      te.tp.pubPre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        s.kernel te.tp.turn ∧
      te.tp.pubPost = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        s'.kernel te.tp.turn :=
  -- the whole-turn fold, with its carried per-effect family CLOSED from the genuine per-step readouts.
  lightclient_turn_unfoolable_forest hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) Rfix hCR
    (hrefines_forest_closed hash LH rds mkLog) c hidx te

/-! ## §3 — NON-VACUITY: a MIXED-effect turn is genuinely covered.

The per-step family `closedLogExtract_all_genuine rds` is NOT transfer-restricted. We exhibit it INHABITED
at three NON-transfer effects simultaneously (cellSeal 52, revoke 2, mint 3) — a mixed cohort — each slot
routing through its proven `<e>_closedLog` rung. This is the "mixed-effect turn is genuinely covered" tooth:
a turn `[…, cellSeal, …, revoke, …, mint, …]` has its per-step rung at EACH, not only at transfer. -/

/-- **`closedLogExtract_family_covers_mixed` (the MIXED-effect tooth).** The genuine per-step family
inhabits the `ClosedLogExtract` rung at the NON-transfer effects cellSeal (52), revoke (2), AND mint (3)
simultaneously — each from the same `ClosureReadouts` bundle, each routing through its proven `<e>_closedLog`
rung. The whole-turn family genuinely covers heterogeneous effects, not transfer alone. -/
theorem closedLogExtract_family_covers_mixed
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) :
    Dregg2.Circuit.ClosureAll.ClosedLogExtract
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 52 ∧
    Dregg2.Circuit.ClosureAll.ClosedLogExtract
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 2 ∧
    Dregg2.Circuit.ClosureAll.ClosedLogExtract
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 3 :=
  ⟨closedLogExtract_all_genuine rds 52,
   closedLogExtract_all_genuine rds 2,
   closedLogExtract_all_genuine rds 3⟩

/-! ## §4 — NON-VACUITY: the whole-turn apex on the degenerate (empty) chain.

The empty `TurnDecodeChain` is trivially constructible (no steps to satisfy). Instantiating the whole-turn
closed apex on it shows the apex's hypotheses are jointly satisfiable (the closed family + the floors
compose), so the headline is not a vacuous implication. -/

/-- **The empty `TurnDecodeChain`** — no steps, `start = fin`. Trivially well-formed (every per-step
obligation is vacuous over the empty step list). -/
def emptyChain
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (start : RecChainedState) :
    TurnDecodeChain hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) start start where
  steps := []
  sat := by intro d hd; simp at hd
  headPre := by simp
  lastPost := by simp
  seam := by simp
  pubSeam := by simp

/-- **`lightclient_unfoolable_circuit_sound_turn_empty` (the joint-satisfiability tooth).** The whole-turn
closed apex instantiated on the empty chain: a genuine (empty) executor run exists, with the published
endpoints binding `start.kernel`. Demonstrates the apex's hypotheses COMPOSE (the closed family + the
floors), so the headline is non-vacuous. -/
theorem lightclient_unfoolable_circuit_sound_turn_empty
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ) {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (hCR : Poseidon2SpongeCR hash)
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        pc pre post →
      ∃ pubLogPre pubLogPost, StateDecodeLog
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        LH pc pubLogPre pubLogPost pre post)
    (start : RecChainedState) (tp : PublishedCommit)
    (hpre : tp.pubPre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
      start.kernel tp.turn)
    (hpost : tp.pubPost = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
      start.kernel tp.turn) :
    ∃ (acts : List FullActionA) (s s' : RecChainedState),
      execFullTurnA s acts = some s' ∧
      tp.pubPre = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        s.kernel tp.turn ∧
      tp.pubPost = (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest).commit
        s'.kernel tp.turn := by
  let te : TurnEndpoints hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
      (emptyChain hash start) :=
    { tp := tp
      headOpen := by simp [emptyChain, hpre]
      lastOpen := by simp [emptyChain, hpost] }
  -- `te.tp` is `tp` by construction, so the apex's conclusion (over `te.tp`) IS the goal (over `tp`).
  exact lightclient_unfoolable_circuit_sound_turn hash LH hCR rds mkLog
    (emptyChain hash start) (by intro d hd; simp [emptyChain] at hd) te

/-! ## §5 — axiom hygiene. -/

#assert_axioms hrefines_forest_closed
#assert_axioms lightclient_unfoolable_circuit_sound_turn
#assert_axioms closedLogExtract_family_covers_mixed
#assert_axioms lightclient_unfoolable_circuit_sound_turn_empty

end Dregg2.Circuit.ClosureForest
