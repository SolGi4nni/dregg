/-
# `DescriptorRefinesComplete` — the per-effect `descriptorRefines` family, CENSUSED + ASSEMBLED whole.

`descriptorRefines S hash d kstep` (`CircuitSoundness`) is the per-effect circuit⟺executor refinement
rung: ANY `Satisfied2` witness of descriptor `d` whose published commitments decode (faithfully) to
`pre`/`post` FORCES `kstep pre post`. The whole-history apex (`lightclient_unfoolable`) carries the
registry-wide family `∀ e, descriptorRefines S hash (Rfix e) (kstepAll e)` as its ONE reducible carrier
(the rest of the apex's floor is the standard crypto carriers `StarkSound`/`Poseidon2SpongeCR` +
`EngineBinding`).

## What this module does (and does NOT re-prove)

The family is NOT a per-effect parking lot of catch-alls. Every one of the 31 deployed effect tags is
discharged by a GENUINE `<e>_closedLog` soundness rung inside
`ClosureFanoutGenuine.closedLogExtract_all_genuine` (the 36-way `actionTag` case split, each slot CALLING
its proven rung — `transfer`/`mint`/`burn`/`cellSeal`/`exercise`/`attenuate`/`revoke`/…), and
`ClosureForest.hrefines_forest_closed` lifts that whole family into
`∀ e, descriptorRefines S_live hash (Rfix e) (dispatchArm e)`. Because `kstepAll = dispatchArm`
DEFINITIONALLY (`CircuitSoundnessAssembled.kstepAll`), that IS the apex's carried family.

This module is the consolidated CENSUS + completeness face over the already-proven pieces:

  * `DescriptorRefinesComplete S hash` — the crisp statement `∀ e, descriptorRefines S hash (Rfix e)
    (kstepAll e)`.
  * `descriptorRefines_complete` — PROVES it for the live surface `S_live`, by routing through
    `hrefines_forest_closed` (which names `closedLogExtract_all_genuine`, which names every proven
    `<e>_closedLog`). The genuine soundness rungs are LOAD-BEARING in the proof term — not opaque.
  * `descriptorRefines_census` — the explicit enumeration: from the complete family, project the
    refinement rung at EACH of the 31 deployed effect tags. A compile-checked manifest that every named
    effect rides its OWN `Rfix e` descriptor (not a transfer fallback / catch-all).
  * ANTI-GHOST (non-vacuity): `kstepAll_discriminates` (the conclusion relation is tag-pinned — each `e`'s
    rung forces an action of tag `e`, so the family is not collapsed to one ghost relation) +
    `kstepAll_not_total` (the conclusion relation is NOT the always-true relation — there is an effect
    index `15` with NO action, so `kstepAll 15` is empty; hence `descriptorRefines` is not laundering
    `kstep := True`).

## The residual (what `descriptorRefines_complete` still consumes — named, not laundered)

`descriptorRefines_complete` consumes, as explicit hypotheses (NOT axioms):

  1. `Poseidon2SpongeCR hash` — INSIDE each `descriptorRefines` (the standard-crypto carrier tying the
     published PI to the decoded limbs). TERMINAL crypto floor.
  2. The `ClosureReadouts` bundle `rds` — the per-effect circuit-decode EXTRACTION carriers (the
     `<e>TraceReadout` family: a `Satisfied2 (Rfix e)` witness yields its named per-effect `…Encodes`
     predicate). This is the `WitnessDecodes`-class limb-level decode — the genuinely-hard residual, but
     REALIZABLE + named (one carrier per effect family), NOT an open soundness gap. See the per-arm notes
     at the bottom of this file.
  3. `mkLog` — the `logHashInjective` log-floor enrichment (`StateDecode ⟹ ∃ StateDecodeLog`). REALIZABLE
     log-commitment CR floor.

There is NO dregg-specific per-effect `descriptorRefines` arm left assumed/unproven: the family is whole.
-/
import Dregg2.Circuit.ClosureForest

namespace Dregg2.Circuit.DescriptorRefinesComplete

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.ClosureFanoutGenuine (ClosureReadouts)
open Dregg2.Circuit.ClosureForest (hrefines_forest_closed)
open Dregg2.Circuit.ActionDispatch (actionTag fullActionStep)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull (FullActionA execFullTurnA)

/-! ## §1 — the crisp statement. -/

/-- **`DescriptorRefinesComplete S hash`** — the apex's carried per-effect refinement family, named:
every effect index's deployed descriptor `Rfix e` refines its dispatcher arm `kstepAll e`. This is the
ONE reducible carrier of `lightclient_unfoolable` (above the standard crypto floors). -/
def DescriptorRefinesComplete (S : CommitSurface) (hash : List ℤ → ℤ) : Prop :=
  ∀ e : EffectIdx, descriptorRefines S hash (Rfix e) (kstepAll e)

/-! ## §2 — completeness: the family is PROVEN whole for the live surface.

`descriptorRefines_complete` is `hrefines_forest_closed` re-typed at `kstepAll` (= `dispatchArm`
definitionally). Its proof term NAMES `closedLogExtract_all_genuine`, which case-splits the 36 cohort tags
and CALLS the proven `<e>_closedLog` rung at each — so every arm is genuine, none is a catch-all. -/

/-- **`descriptorRefines_complete`** — `∀ e, descriptorRefines S_live hash (Rfix e) (kstepAll e)`, the
whole per-effect family, from the genuine per-step `ClosureReadouts` bundle `rds` (each cohort slot
routing through its proven `<e>_closedLog` rung) + the realizable log-floor `mkLog`. The `Poseidon2SpongeCR`
carrier sits inside each `descriptorRefines`; the proof consumes NO axiom beyond the named hypotheses. -/
theorem descriptorRefines_complete
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
        LH pc pubLogPre pubLogPost pre post) :
    DescriptorRefinesComplete
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) hash :=
  -- `kstepAll = dispatchArm` definitionally, so the `dispatchArm e` family `hrefines_forest_closed`
  -- yields IS the `kstepAll e` family `DescriptorRefinesComplete` names.
  hrefines_forest_closed hash LH rds mkLog

/-! ## §3 — the per-effect CENSUS: every deployed tag is a projection of the complete family.

Each conjunct is `H e` at a SPECIFIC deployed effect tag `e`, witnessing that the named effect rides its
OWN descriptor `Rfix e` (the 31 live tags from `actionTag`). This is the compile-checked manifest that the
family covers the whole effect vocabulary — value, the cap write-cap-open family, lifecycle, perms/vk/
program, birth, notes, and the misc/exercise tail — NOT transfer alone. -/

/-- **`descriptorRefines_census`** — from the complete family, the refinement rung at EACH of the 31
deployed effect tags, named. Pure projection (`H e`); the genuineness of each (it routes to that tag's
proven `<e>_closedLog`) is established upstream in `closedLogExtract_all_genuine`. -/
theorem descriptorRefines_census (S : CommitSurface) (hash : List ℤ → ℤ)
    (H : DescriptorRefinesComplete S hash) :
    -- value family
    descriptorRefines S hash (Rfix 0)  (kstepAll 0)  ∧  -- transfer (balanceA)
    descriptorRefines S hash (Rfix 3)  (kstepAll 3)  ∧  -- mint
    descriptorRefines S hash (Rfix 4)  (kstepAll 4)  ∧  -- burn
    descriptorRefines S hash (Rfix 20) (kstepAll 20) ∧  -- bridgeMint
    -- cell-field / perms / vk / program / nonce / heap
    descriptorRefines S hash (Rfix 5)  (kstepAll 5)  ∧  -- setField
    descriptorRefines S hash (Rfix 7)  (kstepAll 7)  ∧  -- incrementNonce
    descriptorRefines S hash (Rfix 8)  (kstepAll 8)  ∧  -- setPermissions
    descriptorRefines S hash (Rfix 9)  (kstepAll 9)  ∧  -- setVK
    descriptorRefines S hash (Rfix 13) (kstepAll 13) ∧  -- setProgram
    descriptorRefines S hash (Rfix 56) (kstepAll 56) ∧  -- heapWrite (GAP-2 tail)
    -- capability write-cap-open family (in-circuit cap-tree authority)
    descriptorRefines S hash (Rfix 1)  (kstepAll 1)  ∧  -- delegate (grantCap cap-open)
    descriptorRefines S hash (Rfix 2)  (kstepAll 2)  ∧  -- revoke
    descriptorRefines S hash (Rfix 10) (kstepAll 10) ∧  -- introduce
    descriptorRefines S hash (Rfix 11) (kstepAll 11) ∧  -- delegateAtten
    descriptorRefines S hash (Rfix 12) (kstepAll 12) ∧  -- attenuate (cap-reshape crown)
    descriptorRefines S hash (Rfix 14) (kstepAll 14) ∧  -- revokeDelegation
    descriptorRefines S hash (Rfix 55) (kstepAll 55) ∧  -- refreshDelegation
    -- cell lifecycle
    descriptorRefines S hash (Rfix 52) (kstepAll 52) ∧  -- cellSeal
    descriptorRefines S hash (Rfix 53) (kstepAll 53) ∧  -- cellUnseal
    descriptorRefines S hash (Rfix 54) (kstepAll 54) ∧  -- cellDestroy
    descriptorRefines S hash (Rfix 38) (kstepAll 38) ∧  -- makeSovereign
    descriptorRefines S hash (Rfix 39) (kstepAll 39) ∧  -- refusal
    descriptorRefines S hash (Rfix 40) (kstepAll 40) ∧  -- receiptArchive
    -- account growth / birth
    descriptorRefines S hash (Rfix 17) (kstepAll 17) ∧  -- createCell
    descriptorRefines S hash (Rfix 18) (kstepAll 18) ∧  -- createCellFromFactory
    descriptorRefines S hash (Rfix 19) (kstepAll 19) ∧  -- spawn
    -- notes
    descriptorRefines S hash (Rfix 27) (kstepAll 27) ∧  -- noteSpend
    descriptorRefines S hash (Rfix 28) (kstepAll 28) ∧  -- noteCreate
    -- misc / exercise / events / queue
    descriptorRefines S hash (Rfix 6)  (kstepAll 6)  ∧  -- emitEvent
    descriptorRefines S hash (Rfix 47) (kstepAll 47) ∧  -- pipelinedSend
    descriptorRefines S hash (Rfix 16) (kstepAll 16) := -- exercise (depth-16 hold-gate crown)
  ⟨H 0, H 3, H 4, H 20, H 5, H 7, H 8, H 9, H 13, H 56,
   H 1, H 2, H 10, H 11, H 12, H 14, H 55,
   H 52, H 53, H 54, H 38, H 39, H 40,
   H 17, H 18, H 19, H 27, H 28, H 6, H 47, H 16⟩

/-! ## §4 — ANTI-GHOST: the conclusion relation `kstepAll` has teeth (non-vacuity).

A `descriptorRefines S hash d kstep` rung is only meaningful if `kstep` is a genuine relation — if `kstep`
were `fun _ _ => True`, the rung would be trivially (vacuously) true. We certify the conclusion family
`kstepAll` is NOT laundered:

  * `kstepAll_discriminates` — each `e`'s relation is tag-PINNED: `kstepAll e pre post` forces SOME
    `FullActionA` of `actionTag = e`. So the 31 arms are genuinely distinct obligations, not one collapsed
    ghost.
  * `kstepAll_not_total` — `kstepAll` is NOT the always-true relation: the effect index `15` has no
    `FullActionA` (it is absent from `actionTag`), so `kstepAll 15` is the EMPTY relation. Hence at least
    one fiber of `descriptorRefines (Rfix _) (kstepAll _)` carries a non-trivial (here, unsatisfiable)
    conclusion — the family is not laundering `kstep := True`. -/

/-- **`kstepAll_discriminates`** — the conclusion relation is tag-pinned: a `kstepAll e` step forces an
action whose `actionTag` is exactly `e`. The per-effect rungs are genuinely distinct, not one ghost. -/
theorem kstepAll_discriminates {e : EffectIdx} {pre post : RecChainedState}
    (h : kstepAll e pre post) : ∃ fa : FullActionA, actionTag fa = e := by
  obtain ⟨fa, htag, -⟩ := h
  exact ⟨fa, htag⟩

/-- **`kstepAll_not_total`** — the conclusion relation is NOT the always-true relation: effect index `15`
has no `FullActionA` (it is not in the range of `actionTag`), so `kstepAll 15` is empty. Certifies
`descriptorRefines_complete` is not a laundered vacuity over `kstep := True`. -/
theorem kstepAll_not_total : ∀ (pre post : RecChainedState), ¬ kstepAll 15 pre post := by
  intro pre post h
  obtain ⟨fa, htag, -⟩ := h
  cases fa <;> simp_all [actionTag]

/-! ## §5 — axiom hygiene. -/

#assert_axioms descriptorRefines_complete
#assert_axioms descriptorRefines_census
#assert_axioms kstepAll_discriminates
#assert_axioms kstepAll_not_total

/-! ## §6 — the per-arm residual notes (the `ClosureReadouts` carrier each genuine arm consumes).

Each genuine `<e>_closedLog` arm (inside `closedLogExtract_all_genuine`) consumes exactly ONE named
circuit-decode EXTRACTION carrier from the `ClosureReadouts` bundle — the `Satisfied2 (Rfix e) ⟹
<e>Encodes` limb-level decode (the `WitnessDecodes`-class residual). These are REALIZABLE and named, NOT
open soundness gaps; they are the precise tail under `descriptorRefines_complete`:

  · value (transfer 0 / mint 3 / burn 4 / bridgeMint 20 / setField 5 / incNonce 7 / heapWrite 56):
      `…TraceReadout` + the `RotTableSide` deployed-chip-permutation faithfulness side-condition.
  · cap write-cap-open (delegate 1 / revoke 2 / introduce 10 / delegateAtten 11 / attenuate 12 /
      revokeDelegation 14 / refreshDelegation 55): the `…CapsTreeEncodes` cap-tree decode + the
      `…WriteAnchor` moving-face anchor; subset arms (11/12) also carry the `SUBMASK` subset-table side.
  · lifecycle (cellSeal 52 / cellUnseal 53 / cellDestroy 54 / makeSovereign 38 / refusal 39 /
      receiptArchive 40 / setPermissions 8 / setVK 9 / setProgram 13): `…TraceReadout` + `RotTableSide` +
      the published receipt-prepend `pubLogPost = LH (receipt :: pre.log)`.
  · birth (createCell 17 / createCellFromFactory 18 / spawn 19): `…TraceReadout` + the create receipt.
  · notes (noteSpend 27 / noteCreate 28): `…TraceReadout` + the nullifier/commitment receipt.
  · misc (emitEvent 6 / pipelinedSend 47): `…Encodes` (no extra side); exercise 16 rides
      `exerciseEncodesAuthV3` (the depth-16 cap-membership hold-gate crown, no outer receipt-prepend).

GENUINELY-HARD residual (needing real NEW circuit-decode work, not assembled here): NONE at the
`descriptorRefines` level — every arm's logical core (`<e>Encodes ⟹ <e>Spec ⟹ kstepAll e`) is landed.
What remains is the standard-crypto realization of the `…TraceReadout`/`…Encodes` carriers themselves
(`Satisfied2`-trace ⟹ named-encode), which bottoms at `Poseidon2SpongeCR` + the deployed-chip
permutation/table faithfulness — the SAME crypto floor the apex already names, not a per-effect open. -/

end Dregg2.Circuit.DescriptorRefinesComplete
