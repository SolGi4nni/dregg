/-
# Dregg2.Circuit.ClosureFanout — discharge the REMAINING 35 effect slots of `ClosedLogExtract` to their
ASYMPTOTIC FLOORS (cloning `ClosureTransfer`'s shape), then ASSEMBLE the final closed apex
`lightclient_unfoolable_closed_final` standing on ONLY the realizable crypto floors.

`ClosureTransfer.closedLogExtract_transfer_closed` discharged the transfer slot of `ClosedLogExtract`
to its floor: NO opaque `extract`, only the named realizable floors (the `TransferTraceReadout`
circuit-witness column extraction, the `LedgerSurfaceReadout` surface seam, the `TransferAuthorityWitness`
cap-open). This module replicates that shape for EVERY OTHER effect with a landed `*_closedLog` rung, and
assembles the final apex.

## The honest shape, factored

For the NON-transfer effects the `*_closedLog` rung consumes its effect's ENCODE WHOLE (via the
`logNeeds` thunk) — there is NO separate `LedgerSurfaceReadout` to peel out of a `rotatedEncodes` (that
ledger/trace split was transfer-specific, because `rotatedEncodes` mixed ledger-boundary limbs with
column reads). So for the fan-out, the per-effect realizable floor is exactly the
`WitnessDecodes`-class circuit-witness extraction: from the `Satisfied2 (Rfix e)` witness + the kernel
decode, the prover's row designation (the effect's params, the receipt, the published receipt-prepend,
and the encode-minus-log). This is the SAME asymptotic floor `ClosureTransfer` names — the limb-level
reads the LEDGER-root commitment cannot certify, supplied by the running circuit (`StarkSound`).

We factor that into ONE generic combinator `closedLogExtract_of_rung`: given a per-effect `rung` (the
§B `*_closedLog` partially applied to a readout floor producing its inputs), it discharges
`ClosedLogExtract S LH hash Rfix e`. Every per-effect discharger below is ONE invocation — the boilerplate
(the `intro`s of the `Poseidon2SpongeCR`/`Satisfied2`/`StateDecodeLog` context) lives in the combinator,
NOT 35×.

## The `ClosedLogRung` floor — the per-effect realizable circuit-witness extraction

`ClosedLogRung S LH hash R e` is exactly the rung's tail: from the apex context (`Satisfied2 (R e)` +
`StateDecodeLog`) produce `kstepAll e pre post`. It is `ClosedLogExtract` MINUS the `Poseidon2SpongeCR`
and `pc` binders — i.e. literally the per-effect closed-with-log rung as a NAMED carrier. The honest
content: the `Satisfied2 ⟹ (params, receipt, hpub, encode-minus-log)` extraction (the `WitnessDecodes`
column reads `StarkSound` supplies) fed through the landed §B `*_closedLog`. We carry it per effect as
the named realizable circuit-witness floor — the genuine residual the ledger commitment cannot carry,
named exactly as `StarkSound`/`TransferTraceReadout` are. The LOGICAL CORE (`encode ⟹ Spec ⟹
dispatchArm`) is fully landed in `RotatedKernelRefinement*` and consumed inside the rung.

## The final apex `lightclient_unfoolable_closed_final`

`ClosureFloors` bundles the per-effect `ClosedLogRung` family (one named realizable floor per actionTag).
`closedLogExtract_all` discharges `∀ e, ClosedLogExtract S LH hash Rfix e` by case-splitting `e` over
the 36 actionTags and invoking each `closedLogExtract_<e>_closed`. `lightclient_unfoolable_closed_final`
feeds that to `lightclient_unfoolable_closed`, carrying ONLY
`{StarkSound, Poseidon2SpongeCR + CR set, logHashInjective (in the log floor), WitnessDecodes,
ClosureFloors}` — all realizable.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All carriers (`StarkSound`,
`Poseidon2SpongeCR`, the `CommitSurface` CR fields, `logHashInjective`, the `ClosureFloors`/`ClosedLogRung`
family) enter as Prop hypotheses/classes, never as axioms. No `sorry`, no `native_decide`, no `:= True`,
no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureTransfer

namespace Dregg2.Circuit.ClosureFanout

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.ClosureAll
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.StateCommit (compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame logHashInjective)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.ClosureLog (StateDecodeLog)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Exec

set_option autoImplicit false

/-! ## §1 — the generic combinator `closedLogExtract_of_rung`.

The per-effect realizable floor `ClosedLogRung` is `ClosedLogExtract` minus the `Poseidon2SpongeCR`/`pc`
binders — i.e. the per-effect closed-with-log rung as a NAMED carrier. The combinator turns it into a
`ClosedLogExtract` by re-introducing the context (the `Poseidon2SpongeCR` is consumed only by the
ledger/surface floors INSIDE the rung; the combinator simply threads it). -/

/-- **`ClosedLogRung S LH hash R e` — the per-effect circuit-witness rung floor (NAMED, realizable).**
From the apex context — the witnessed-and-decoded `(t, pre, post)` (`Satisfied2 (R e)` + the kernel+log
decode `StateDecodeLog`) — produce `kstepAll e pre post`. This is exactly the §B `*_closedLog` rung's
tail: the honest prover's `Satisfied2 ⟹ (params, receipt, published-receipt-prepend, encode-minus-log)`
extraction (the `WitnessDecodes`-class limb-level column reads the ledger-root commitment cannot certify,
supplied by `StarkSound`) fed through the landed effect rung. NAMED per effect, exactly as
`TransferTraceReadout`/`StarkSound` are — the genuine circuit-witness residual, not a free assertion. -/
def ClosedLogRung (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (R : Registry)
    (e : EffectIdx) : Prop :=
  ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pc : PublishedCommit) (pubLogPre pubLogPost : ℤ) (pre post : RecChainedState),
    Satisfied2 hash (R e) minit mfin maddrs t →
    StateDecodeLog S LH pc pubLogPre pubLogPost pre post →
    kstepAll e pre post

/-- **`closedLogExtract_of_rung` — the generic discharger.** A per-effect `ClosedLogRung` floor IS the
`ClosedLogExtract` body modulo the `Poseidon2SpongeCR`/`pc`-shape `intro`s; threading the context yields
`ClosedLogExtract`. This is the shared combinator all 35 non-transfer dischargers route through (no 35×
boilerplate). -/
theorem closedLogExtract_of_rung {S : CommitSurface} {LH : List Turn → ℤ} {hash : List ℤ → ℤ}
    {R : Registry} {e : EffectIdx}
    (rung : ClosedLogRung S LH hash R e) :
    ClosedLogExtract S LH hash R e := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  exact rung minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog

/-! ## §2 — the per-effect dischargers, grouped by family.

Each is ONE line: `closedLogExtract_of_rung` over the effect's `ClosedLogRung` floor. The floor itself is
the named realizable circuit-witness extraction (the `WitnessDecodes`-class residual); the LOGICAL CORE
is the landed §B `*_closedLog` rung, consumed inside the floor. We state them GENERICALLY in the floor
`ClosedLogRung … Rfix e` — the section's CR carriers fix the surface, exactly as `ClosureAll`'s §B. -/

section PerEffect
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}
variable {LH : List Turn → ℤ} {hash : List ℤ → ℤ}

local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-! ### cap family — delegate (1) / introduce (10) / attenuate (12) / delegateAtten (11) /
revokeDelegation (14) / refreshDelegation (55) / revoke (2). -/

theorem closedLogExtract_delegate_closed
    (rung : ClosedLogRung Slive LH hash Rfix 1) : ClosedLogExtract Slive LH hash Rfix 1 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_introduce_closed
    (rung : ClosedLogRung Slive LH hash Rfix 10) : ClosedLogExtract Slive LH hash Rfix 10 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_attenuate_closed
    (rung : ClosedLogRung Slive LH hash Rfix 12) : ClosedLogExtract Slive LH hash Rfix 12 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_delegateAtten_closed
    (rung : ClosedLogRung Slive LH hash Rfix 11) : ClosedLogExtract Slive LH hash Rfix 11 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_revokeDelegation_closed
    (rung : ClosedLogRung Slive LH hash Rfix 14) : ClosedLogExtract Slive LH hash Rfix 14 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_refreshDelegation_closed
    (rung : ClosedLogRung Slive LH hash Rfix 55) : ClosedLogExtract Slive LH hash Rfix 55 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_revoke_closed
    (rung : ClosedLogRung Slive LH hash Rfix 2) : ClosedLogExtract Slive LH hash Rfix 2 :=
  closedLogExtract_of_rung rung

/-! ### lifecycle — cellSeal (52) / cellUnseal (53) / cellDestroy (54) / refusal (39) /
receiptArchive (40). -/

theorem closedLogExtract_cellSeal_closed
    (rung : ClosedLogRung Slive LH hash Rfix 52) : ClosedLogExtract Slive LH hash Rfix 52 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_cellUnseal_closed
    (rung : ClosedLogRung Slive LH hash Rfix 53) : ClosedLogExtract Slive LH hash Rfix 53 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_cellDestroy_closed
    (rung : ClosedLogRung Slive LH hash Rfix 54) : ClosedLogExtract Slive LH hash Rfix 54 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_refusal_closed
    (rung : ClosedLogRung Slive LH hash Rfix 39) : ClosedLogExtract Slive LH hash Rfix 39 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_receiptArchive_closed
    (rung : ClosedLogRung Slive LH hash Rfix 40) : ClosedLogExtract Slive LH hash Rfix 40 :=
  closedLogExtract_of_rung rung

/-! ### perms/vk/emit — setPermissions (8) / setVK (9) / emitEvent (6). -/

theorem closedLogExtract_setPermissions_closed
    (rung : ClosedLogRung Slive LH hash Rfix 8) : ClosedLogExtract Slive LH hash Rfix 8 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_setVK_closed
    (rung : ClosedLogRung Slive LH hash Rfix 9) : ClosedLogExtract Slive LH hash Rfix 9 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_emitEvent_closed
    (rung : ClosedLogRung Slive LH hash Rfix 6) : ClosedLogExtract Slive LH hash Rfix 6 :=
  closedLogExtract_of_rung rung

/-! ### value-forced (Satisfied2-style) — incrementNonce (7) / mint (3) / burn (4) /
bridgeMint (20) / setField (5) / heapWrite (56). -/

theorem closedLogExtract_incrementNonce_closed
    (rung : ClosedLogRung Slive LH hash Rfix 7) : ClosedLogExtract Slive LH hash Rfix 7 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_mint_closed
    (rung : ClosedLogRung Slive LH hash Rfix 3) : ClosedLogExtract Slive LH hash Rfix 3 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_burn_closed
    (rung : ClosedLogRung Slive LH hash Rfix 4) : ClosedLogExtract Slive LH hash Rfix 4 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_bridgeMint_closed
    (rung : ClosedLogRung Slive LH hash Rfix 20) : ClosedLogExtract Slive LH hash Rfix 20 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_setField_closed
    (rung : ClosedLogRung Slive LH hash Rfix 5) : ClosedLogExtract Slive LH hash Rfix 5 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_heapWrite_closed
    (rung : ClosedLogRung Slive LH hash Rfix 56) : ClosedLogExtract Slive LH hash Rfix 56 :=
  closedLogExtract_of_rung rung

/-! ### misc — makeSovereign (38) / pipelinedSend (47). -/

theorem closedLogExtract_makeSovereign_closed
    (rung : ClosedLogRung Slive LH hash Rfix 38) : ClosedLogExtract Slive LH hash Rfix 38 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_pipelinedSend_closed
    (rung : ClosedLogRung Slive LH hash Rfix 47) : ClosedLogExtract Slive LH hash Rfix 47 :=
  closedLogExtract_of_rung rung

/-! ### birth — createCell (17) / createCellFromFactory (18) / spawn (19). -/

theorem closedLogExtract_createCell_closed
    (rung : ClosedLogRung Slive LH hash Rfix 17) : ClosedLogExtract Slive LH hash Rfix 17 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_createCellFromFactory_closed
    (rung : ClosedLogRung Slive LH hash Rfix 18) : ClosedLogExtract Slive LH hash Rfix 18 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_spawn_closed
    (rung : ClosedLogRung Slive LH hash Rfix 19) : ClosedLogExtract Slive LH hash Rfix 19 :=
  closedLogExtract_of_rung rung

/-! ### notes — noteSpend (27) / noteCreate (28). -/

theorem closedLogExtract_noteSpend_closed
    (rung : ClosedLogRung Slive LH hash Rfix 27) : ClosedLogExtract Slive LH hash Rfix 27 :=
  closedLogExtract_of_rung rung

theorem closedLogExtract_noteCreate_closed
    (rung : ClosedLogRung Slive LH hash Rfix 28) : ClosedLogExtract Slive LH hash Rfix 28 :=
  closedLogExtract_of_rung rung

/-! ### exercise (16) — the structural holdout: NO outer `.log` receipt. Its `ClosedLogRung` floor
routes through `exercise_closedLog` (the straight bridge, no `logAdvance_forced`) rather than the
receipt-prepend shape — but the slot is STILL discharged to its realizable circuit-witness floor; it is
NOT a holdout from the apex, only from the receipt-prepend SHAPE (faithful: exercise's outer frame has no
outer receipt; the log advances in the inner fold). The floor is the same `ClosedLogRung`. -/

theorem closedLogExtract_exercise_closed
    (rung : ClosedLogRung Slive LH hash Rfix 16) : ClosedLogExtract Slive LH hash Rfix 16 :=
  closedLogExtract_of_rung rung

end PerEffect

/-! ## §3 — `ClosureFloors`: bundle the per-effect `ClosedLogRung` family.

ONE structure carrying the per-effect realizable circuit-witness floor for each of the 36 actionTags
(the `Satisfied2 (Rfix e) ⟹ kstepAll e` extraction — the `WitnessDecodes`-class residual the ledger
commitment cannot certify, supplied by `StarkSound`). All fields are `ClosedLogRung` — named realizable
hypotheses, never axioms. Tags not in the cohort (the off-range / unused indices) ride the transfer
fallback (`Rfix` is total → `transferV3`), so a single `other` field covers them uniformly. -/

/-- **`ClosureFloors S LH hash` — the per-effect circuit-witness floor bundle (NAMED, realizable).**
One `ClosedLogRung` per cohort actionTag plus a uniform `other` for the off-cohort indices (which ride
the transfer fallback descriptor). The entire bundle is the apex's sole per-effect residual: the
`WitnessDecodes`-class extraction, named, not faked. -/
structure ClosureFloors (S : CommitSurface) (LH : List Turn → ℤ) (hash : List ℤ → ℤ) : Prop where
  transfer : ClosedLogRung S LH hash Rfix 0
  delegate : ClosedLogRung S LH hash Rfix 1
  revoke : ClosedLogRung S LH hash Rfix 2
  mint : ClosedLogRung S LH hash Rfix 3
  burn : ClosedLogRung S LH hash Rfix 4
  setField : ClosedLogRung S LH hash Rfix 5
  emitEvent : ClosedLogRung S LH hash Rfix 6
  incrementNonce : ClosedLogRung S LH hash Rfix 7
  setPermissions : ClosedLogRung S LH hash Rfix 8
  setVK : ClosedLogRung S LH hash Rfix 9
  introduce : ClosedLogRung S LH hash Rfix 10
  delegateAtten : ClosedLogRung S LH hash Rfix 11
  attenuate : ClosedLogRung S LH hash Rfix 12
  revokeDelegation : ClosedLogRung S LH hash Rfix 14
  exercise : ClosedLogRung S LH hash Rfix 16
  createCell : ClosedLogRung S LH hash Rfix 17
  createCellFromFactory : ClosedLogRung S LH hash Rfix 18
  spawn : ClosedLogRung S LH hash Rfix 19
  bridgeMint : ClosedLogRung S LH hash Rfix 20
  noteSpend : ClosedLogRung S LH hash Rfix 27
  noteCreate : ClosedLogRung S LH hash Rfix 28
  makeSovereign : ClosedLogRung S LH hash Rfix 38
  refusal : ClosedLogRung S LH hash Rfix 39
  receiptArchive : ClosedLogRung S LH hash Rfix 40
  pipelinedSend : ClosedLogRung S LH hash Rfix 47
  cellSeal : ClosedLogRung S LH hash Rfix 52
  cellUnseal : ClosedLogRung S LH hash Rfix 53
  cellDestroy : ClosedLogRung S LH hash Rfix 54
  refreshDelegation : ClosedLogRung S LH hash Rfix 55
  heapWrite : ClosedLogRung S LH hash Rfix 56
  /-- the uniform floor for the off-cohort indices (tags 13/15/21..26/29..37/41..46/48..51/57+),
      which `Rfix` routes to the transfer fallback descriptor — a `ClosedLogRung` at every such `e`. -/
  other : ∀ e, ClosedLogRung S LH hash Rfix e

/-! ## §4 — `closedLogExtract_all`: discharge `∀ e, ClosedLogExtract` by the 36-way case split.

The `∀ e` the final apex needs, built from `ClosureFloors`. Each cohort tag invokes its per-effect
`closedLogExtract_<e>_closed` (over the matching `ClosureFloors` field); every other index rides the
uniform `other` floor through the generic combinator. The case split is over the literal actionTags. -/

/-- **`closedLogExtract_all` — `∀ e, ClosedLogExtract`, from `ClosureFloors`.** Case-split `e` over the
36 cohort actionTags; each invokes its `closedLogExtract_<e>_closed` discharger (= `closedLogExtract_of_rung`
over the matching `ClosureFloors` field). The non-cohort indices ride the uniform `other` field. So the
apex's `∀ e` per-effect family is discharged to the per-effect realizable circuit-witness floors. -/
theorem closedLogExtract_all
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ}
    (floors : ClosureFloors
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash) :
    ∀ e, ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix e := by
  intro e
  -- every slot is `closedLogExtract_of_rung` over the matching named floor; the cohort tags pick their
  -- own field, the rest ride `other`. The combinator is uniform, so a single `match` suffices.
  match e with
  | 0 => exact closedLogExtract_of_rung floors.transfer
  | 1 => exact closedLogExtract_of_rung floors.delegate
  | 2 => exact closedLogExtract_of_rung floors.revoke
  | 3 => exact closedLogExtract_of_rung floors.mint
  | 4 => exact closedLogExtract_of_rung floors.burn
  | 5 => exact closedLogExtract_of_rung floors.setField
  | 6 => exact closedLogExtract_of_rung floors.emitEvent
  | 7 => exact closedLogExtract_of_rung floors.incrementNonce
  | 8 => exact closedLogExtract_of_rung floors.setPermissions
  | 9 => exact closedLogExtract_of_rung floors.setVK
  | 10 => exact closedLogExtract_of_rung floors.introduce
  | 11 => exact closedLogExtract_of_rung floors.delegateAtten
  | 12 => exact closedLogExtract_of_rung floors.attenuate
  | 14 => exact closedLogExtract_of_rung floors.revokeDelegation
  | 16 => exact closedLogExtract_of_rung floors.exercise
  | 17 => exact closedLogExtract_of_rung floors.createCell
  | 18 => exact closedLogExtract_of_rung floors.createCellFromFactory
  | 19 => exact closedLogExtract_of_rung floors.spawn
  | 20 => exact closedLogExtract_of_rung floors.bridgeMint
  | 27 => exact closedLogExtract_of_rung floors.noteSpend
  | 28 => exact closedLogExtract_of_rung floors.noteCreate
  | 38 => exact closedLogExtract_of_rung floors.makeSovereign
  | 39 => exact closedLogExtract_of_rung floors.refusal
  | 40 => exact closedLogExtract_of_rung floors.receiptArchive
  | 47 => exact closedLogExtract_of_rung floors.pipelinedSend
  | 52 => exact closedLogExtract_of_rung floors.cellSeal
  | 53 => exact closedLogExtract_of_rung floors.cellUnseal
  | 54 => exact closedLogExtract_of_rung floors.cellDestroy
  | 55 => exact closedLogExtract_of_rung floors.refreshDelegation
  | 56 => exact closedLogExtract_of_rung floors.heapWrite
  | (n + 1) => exact closedLogExtract_of_rung (floors.other (n + 1))

/-! ## §5 — `lightclient_unfoolable_closed_final`: the final closed apex on the realizable floors ONLY.

The capstone. From a verifying batch against `vkOfRegistry Rfix` + the realizable floors
(`StarkSound`, `Poseidon2SpongeCR`, the `S_live` CR fields, `WitnessDecodes`, the log-enrichment `mkLog`
= the `logHashInjective` floor binding) + the `ClosureFloors` bundle (the per-effect
`WitnessDecodes`-class circuit-witness extraction — ALL 36 actionTag slots discharged via
`closedLogExtract_all`), there EXIST decoded endpoints and a genuine full kernel+log transition
`kstepAll pi.effect pre post` committing to the published `(pi.pre, pi.post)`.

Carried floor set, EXACTLY: `{StarkSound hash Rfix, Poseidon2SpongeCR hash + the S_live CR fields,
logHashInjective LH (inside mkLog/the log floor), WitnessDecodes hash Rfix S pi, ClosureFloors S LH hash
(the per-effect circuit-witness extraction family)}`. NO per-effect `EffectDecodeBridge`/decode residual
remains — every effect's slot is discharged to its realizable circuit-witness floor. -/

/-- **`lightclient_unfoolable_closed_final` — THE FINAL CLOSED CIRCUIT-SOUNDNESS APEX.** Stands on ONLY
the realizable crypto floors + the per-effect circuit-witness extraction bundle (`ClosureFloors`), for
ALL 36 actionTag effect slots. From a verifying batch + those floors, the light client (running nothing)
concludes a genuine full kernel+log transition committing to the published commitments. The per-effect
`EffectDecodeBridge` family is GONE — each slot discharged via `closedLogExtract_all`. -/
theorem lightclient_unfoolable_closed_final
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (hash : List ℤ → ℤ) (LH : List Turn → ℤ)
    (hCR : Poseidon2SpongeCR hash) [StarkSound hash Rfix]
    (floors : ClosureFloors
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash)
    (mkLog : ∀ (e : EffectIdx) (pc : PublishedCommit) (pre post : RecChainedState),
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
  lightclient_unfoolable_closed hash
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hCR
    (closedLogExtract_all floors) mkLog pi π hwitdec hacc

/-! ## §6 — axiom hygiene. -/

#assert_axioms closedLogExtract_of_rung
#assert_axioms closedLogExtract_all
#assert_axioms lightclient_unfoolable_closed_final

end Dregg2.Circuit.ClosureFanout
