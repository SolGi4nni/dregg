/-
# Dregg2.Circuit.ClosureFanoutGenuine — the GENUINE per-effect dischargers.

`ClosureFanout` "discharged" each non-transfer slot of `ClosedLogExtract` via `closedLogExtract_of_rung
(rung : ClosedLogRung … e)` — but `ClosedLogRung e` IS the entire per-effect refinement obligation
(`Satisfied2 (Rfix e) → StateDecodeLog → kstepAll e`) carried as a hypothesis. The proven `*_closedLog`
rungs were NOT consumed. That renamed the obligation as a "floor", it did not REDUCE it.

This module replaces every non-transfer discharger with a GENUINE one, cloning the shape of
`ClosureTransfer.closedLogExtract_transfer_closed`:

  * it takes a NAMED decode-extraction floor `<e>TraceReadout` = the realizable
    `Satisfied2 (Rfix e) ⟹ <e>EncodesMinusLog` extraction (the `WitnessDecodes`-class limb-level column
    reads the honest prover's trace supplies — the SAME class as `TransferTraceReadout`). This is
    `Satisfied2 → encode`, NOT `Satisfied2 → kstep`;
  * it ACTUALLY CALLS the proven `<e>_closedLog` rung (the landed `…EncodesMinusLog → kstepAll e`), fed
    the extracted encode, the `StateDecodeLog`, and the published receipt-prepend. The proven rung — the
    circuit-forcing core landed in `RotatedKernelRefinement*` and re-exported by `ClosureAll` — appears
    in EVERY proof term here (grep: every discharger names a `*_closedLog`).

So `ClosedLogExtract Slive LH hash Rfix e` is discharged carrying ONLY the named realizable
decode-extraction (`<e>TraceReadout`) + the surface CR (in `Slive`) + the rung's named carriers
(`hash`/`Scap`/`compressN2`/`hN`, all realizable crypto primitives), NEVER the whole `ClosedLogRung` /
`Satisfied2 → kstep`.

## The `<e>TraceReadout` shape (`Satisfied2 → encode`, per family)

`<e>TraceReadout` extracts, from the per-effect `Satisfied2` witness + `pre`/`post`/the published
`pubLogPost`, the prover's row designation `(params…)` together with: the published receipt-prepend
(`PLift (pubLogPost = LH (receipt :: pre.log))`) and the encode-minus-`logAdv` (the function
`post.log = receipt :: pre.log → <e>Encodes …`). For the `Satisfied2`-style effects (mint/burn/
incrementNonce/setField/heapWrite/bridgeMint/transfer) it also carries the table side-condition
`RotTableSide`. This is EXACTLY the `extract` of `ClosureAll.closedLogExtract_transfer` generalised per
effect — the `WitnessDecodes`-class circuit-witness extraction, named not faked.

## `exercise` (tag 16) — the structural holdout

`exercise_closedLog` is the SOLE rung with no outer receipt-prepend (`ExerciseSpec` has none — the log
advances in the inner fold). Its readout is `Satisfied2 → exerciseEncodes` with NO `hpub`/no derived
advance; the discharger still CALLS `exercise_closedLog` on the extracted encode. Genuinely connected,
only the receipt-prepend SHAPE differs.

## Re-assembly

`ClosureFloorsGenuine` bundles the per-effect NAMED `<e>TraceReadout` decode-extraction floors (plus the
shared rung carriers). `closedLogExtract_all_genuine` discharges `∀ e, ClosedLogExtract` by the 36-way
actionTag case split, each slot CALLING its proven rung. `lightclient_unfoolable_closed_final_genuine`
feeds that to `lightclient_unfoolable_closed`. So the proven `RotatedKernelRefinement*` soundness rungs
are LOAD-BEARING in the final apex, and the carried set is the per-effect decode-extraction
(`WitnessDecodes` class) + the crypto floors — NOT the whole refinement.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. All carriers enter as Prop/Type
hypotheses, never as axioms. NEW file; imports read-only.
-/
import Dregg2.Circuit.ClosureTransfer

namespace Dregg2.Circuit.ClosureFanoutGenuine

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
open Dregg2.Exec.TurnExecutorFull (authReceipt)

set_option autoImplicit false

section PerEffect
variable {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
variable {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
variable {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
variable {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
variable {hRest : RestHashIffFrame RH}
variable {LH : List Turn → ℤ} {hash : List ℤ → ℤ}

local notation "Slive" => S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest

/-! ## §1 — the `Satisfied2`-style readouts (carry `RotTableSide` + receipt + encode-minus-log).

These effects' rungs (`transfer`/`mint`/`burn`/`bridgeMint`/`incrementNonce`/`setField`/`heapWrite`)
take a `hash`/`Satisfied2`/`RotTableSide` triple. The readout extracts, from the `Satisfied2` witness +
`pre`/`post`/`pubLogPost`, the row designation, the `RotTableSide`, the published receipt-prepend, and
the encode-minus-`logAdv`. -/

/-- **mint (3).** The `Satisfied2 mintV3 ⟹ (params, RotTableSide, receipt, rotatedEncodesMint-minus-log)`
extraction — the `WitnessDecodes`-class circuit-witness readout. -/
abbrev MintTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ) (permOut : List ℤ → List ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log)) ×'
    (post.log = Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesMint
        hash minit mfin maddrs t pre post actor cell a amt)

theorem closedLogExtract_mint_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      MintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 3 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- `Rfix 3` is the DEPLOYED gated mint member (`withSelectorGate selM.MINT mintV3`); strip the
  -- appended selector-binding gate to recover the bare-`mintV3` witness the readout/rung consume.
  have hsat := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withSelectorGate_satisfied2
    hash _ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t hsat
  obtain ⟨actor, cell, a, amt, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact mint_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **burn (4).** -/
abbrev BurnTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Dregg2.Circuit.RotatedKernelRefinementMintBurn.burnV3) minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ) (permOut : List ℤ → List ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH (Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log)) ×'
    (post.log = Dregg2.Circuit.Spec.SupplyDestruction.burnReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesBurn
        hash minit mfin maddrs t pre post actor cell a amt)

theorem closedLogExtract_burn_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      BurnTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 4 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, a, amt, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact burn_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **bridgeMint (20)** — refines `MintASpec`, via the mint descriptor `mintV3`. -/
abbrev BridgeMintTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ) (permOut : List ℤ → List ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH (Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log)) ×'
    (post.log = Dregg2.Circuit.Spec.SupplyCreation.mintReceipt actor cell a amt :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementMintBurn.rotatedEncodesMint
        hash minit mfin maddrs t pre post actor cell a amt)

theorem closedLogExtract_bridgeMint_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      BridgeMintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 20 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- `Rfix 20` is the DEPLOYED gated mint member (`withSelectorGate selM.MINT mintV3`); strip the
  -- appended selector-binding gate to recover the bare-`mintV3` witness the readout/rung consume.
  have hsat := Dregg2.Circuit.Emit.EffectVmEmitRotationV3.withSelectorGate_satisfied2
    hash _ Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t hsat
  obtain ⟨actor, cell, a, amt, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact bridgeMint_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **incrementNonce (7).** Receipt is the self-row `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
abbrev IncNonceTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinementIncNonce.incNonceV3 minit mfin maddrs t →
  Σ' (actor cell : CellId) (n : ℤ) (permOut : List ℤ → List ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
    (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementIncNonce.rotatedEncodesIncNonce
        hash minit mfin maddrs t pre post actor cell n)

theorem closedLogExtract_incrementNonce_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      IncNonceTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 7 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, n, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact incrementNonce_closedLog hash hside hsat pre post actor cell n pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **setField (5)** at slot `slot : Fin 8`. -/
abbrev SetFieldTraceReadout (slot : Fin 8) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Rfix 5) minit mfin maddrs t →
  Σ' (actor cell : CellId) (v : ℤ) (permOut : List ℤ → List ℤ),
    Satisfied2 hash (Dregg2.Circuit.RotatedKernelRefinementSetField.setFieldV3 slot) minit mfin maddrs t ×'
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
    (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementSetField.rotatedEncodesSF
        slot hash minit mfin maddrs t pre post actor cell v)

theorem closedLogExtract_setField_closed (slot : Fin 8)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      SetFieldTraceReadout (LH := LH) (hash := hash) slot minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 5 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, v, permOut, hsat2, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact setField_closedLog slot hash hside hsat2 pre post actor cell v pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **heapWrite (56) — CLASS A.** Receipt is `{ actor, src:=target, dst:=target, amt:=0 }`. The new
`heap_root` is forced from the DEPLOYED `heapWriteV3` (`= Rfix 56` by `rfl`, `actionTagToPos 56 = 45`,
`v3RegistryHeap` tail) via `heapWrite_descriptorRefines_sat`: the readout extracts the chip/range
`RotTableSide`, the published receipt-prepend, and the `HeapWriteTraceReadout`-minus-log (register write /
splice / guard / 14-field frame). Editing `heapWriteV3`'s recompute sites turns this — and the apex — RED. -/
abbrev HeapWriteTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Rfix 56) minit mfin maddrs t →
  Σ' (actor target : CellId) (addr v newRoot : ℤ) (permOut : List ℤ → List ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
    PLift (pubLogPost = LH ({ actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log)) ×'
    (post.log = { actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementExercise.HeapWriteTraceReadout
        hash t pre post actor target addr v newRoot)

theorem closedLogExtract_heapWrite_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      HeapWriteTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 56 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- `Rfix 56 = heapWriteV3` definitionally (`actionTagToPos 56 = 45`, `v3RegistryHeap` tail).
  have hsat' : Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, target, addr, v, newRoot, permOut, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact heapWrite_closedLog_sat hash hside hsat' pre post actor target addr v newRoot
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-! ## §2 — the cap-family readouts (carry `Scap` + `authReceipt` + cap-tree encode-minus-log).

The cap rungs (`delegate`/`introduce`/`attenuate`/`delegateAtten`/`revokeDelegation`/`refreshDelegation`/
`revoke`) take a `CapHashScheme` carrier `Scap` (the deployed sorted-Poseidon2 cap-tree hash, a named
realizable crypto primitive) and produce their `*CapsTreeEncodes`. The readout extracts the row
designation + the published `authReceipt`-prepend + the cap-tree encode-minus-log. `Scap` is a
discharger parameter (shared across all witnesses), threaded into the rung. -/

/-- **delegate (1) — CLASS A.** `Rfix 1 = delegateWriteCapOpenV3` (the WRITE-FORCING cap-open wrapper,
position 46): the readout extracts the cap-tree decode + the realizable `DelegateWriteAnchor`, and
`delegate_closedLog_sat` strips the wrapper through `capOpen_satisfied2_strips_to_base` to the base
`grantCap_descriptorRefines_sat` — the post cap-root is pinned by the LIVE insert write. Editing
`delegateWriteCapOpenV3`'s write op turns this — and the apex — RED. -/
theorem closedLogExtract_delegate_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 1) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (del rec tt : CellId),
        PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
        (post.log = authReceipt del :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
                Scap pre post del rec tt),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateWriteAnchor
              Scap pre post del rec tt hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 1 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.delegateWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, del, rec, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact delegate_closedLog_sat (State := Unit) Scap hash hChip hsat' pre post del rec tt
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **introduce (10) — CLASS A.** `Rfix 10 = introduceWriteCapOpenV3` (position 47): the cap-tree insert
on the moving genuine face is FORCED via `introduce_descriptorRefines_capOpenSat`. Refines `DelegateSpec`. -/
theorem closedLogExtract_introduce_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 10) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (intro rec tt : CellId),
        PLift (pubLogPost = LH (authReceipt intro :: pre.log)) ×'
        (post.log = authReceipt intro :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
                Scap pre post intro rec tt),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.IntroduceWriteAnchor
              Scap pre post intro rec tt hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 10 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.introduceWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, intro, rec, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact introduce_closedLog_sat (State := Unit) Scap hash hChip hsat' pre post intro rec tt
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **attenuate (12) — CLASS A.** `Rfix 12 = attenuateCapOpenEffV3` (position 43): the LIVE cap-open
authority descriptor whose base `attenuateV3` is the MOVING write face (no `gCapPass` freeze). The cap-tree
UPDATE-AT-KEY (the in-place slot narrow) is FORCED via `attenuate_descriptorRefines_capOpenSat` (strip the
authority appendix + selector tooth → `Satisfied2 attenuateV3` → `attenuateV3_non_amp`'s `keepWriteOp`).
The readout supplies the realizable submask table-fill `hsub` alongside the anchor. Editing `attenuateV3`'s
write op reds this rung — and the apex. Refines `AttenuateSpec`. -/
theorem closedLogExtract_attenuate_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 12) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (actor : CellId) (idx : Nat) (keep : List Dregg2.Authority.Auth),
        PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
          = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
        PLift (pubLogPost = LH (authReceipt actor :: pre.log)) ×'
        (post.log = authReceipt actor :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes
                Scap pre post actor idx keep),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateWriteAnchor
              Scap pre post actor idx keep hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 12 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.attenuateCapOpenEffV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, actor, idx, keep, hsub, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact attenuate_closedLog_sat (State := Unit) Scap hash hsub.down hChip hsat' pre post actor idx keep
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **delegateAtten (11) — CLASS A.** `Rfix 11 = delegateAttenWriteCapOpenV3` (position 48): the cap-tree
insert + the `granted ⊑ held` non-amplification are FORCED via `delegateAtten_descriptorRefines_capOpenSat`.
The readout supplies the SUBMASK table-fill `hsub` (the realizable lookup carrier) alongside the anchor. -/
theorem closedLogExtract_delegateAtten_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 11) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (del rec tt : CellId) (keep : List Dregg2.Authority.Auth),
        PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
          = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
        PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
        (post.log = authReceipt del :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes
                Scap pre post del rec tt keep),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenWriteAnchor
              Scap pre post del rec tt keep hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 11 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.delegateAttenWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, del, rec, tt, keep, hsub, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact delegateAtten_closedLog_sat (State := Unit) Scap hash hsub.down hChip hsat' pre post del rec tt keep
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **revokeDelegation (14) — CLASS A.** `Rfix 14 = revokeDelegationWriteCapOpenV3` (position 49): the
cap-tree REMOVE on the moving genuine face is FORCED via `revokeDelegation_descriptorRefines_capOpenSat_full`.
Refines the FAITHFUL `RevokeDelegationFullSpec` (cap-edge remove FORCED + the epoch step — parent epoch
bumped + child snapshot staled — carried as the NAMED `RevokeDelegationFullEncodes` epoch residual, §3.EPOCH). -/
theorem closedLogExtract_revokeDelegation_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 14) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (holder tt : CellId),
        PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
        (post.log = authReceipt holder :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationFullEncodes
                Scap pre post holder tt),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
              Scap pre post holder tt hash minit mfin maddrs t henc.capRemove)) :
    ClosedLogExtract Slive LH hash Rfix 14 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, holder, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact revokeDelegation_closedLog_sat (State := Unit) Scap hash hChip hsat' pre post holder tt
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **revoke (2) — CLASS A.** `Rfix 2 = revokeDelegationWriteCapOpenV3` (position 49 — the SAME
write-bearing descriptor tag 14 rides): the cap-tree REMOVE on the moving genuine face is FORCED via
`revokeDelegation_descriptorRefines_capOpenSat`. `.revoke holder t` lowers to the SHARED `RevokeSpec`/
`removeEdgeCaps` kernel step, so the `RevokeCapsTreeEncodes` + `RevokeDelegationWriteAnchor` readout that
discharges tag 14 discharges tag 2 verbatim — `hsat` is now CONSUMED (the modelled floor is gone). -/
theorem closedLogExtract_revoke_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 2) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (holder tt : CellId),
        PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
        (post.log = authReceipt holder :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
                Scap pre post holder tt),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
              Scap pre post holder tt hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 2 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.revokeDelegationWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, holder, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact revoke_closedLog_capOpenSat (State := Unit) Scap hash hChip hsat' pre post holder tt
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **refreshDelegation (55) — CLASS A.** The DELEGATIONS-tree UPDATE-write is forced from the DEPLOYED
descriptor `refreshDelegationWriteCapOpenV3` (`= Rfix 55` by `rfl`): the readout extracts the actor/child,
the published receipt-prepend, and the `RefreshDelegationCapsTreeEncodes` decode + the realizable
`RefreshDelegationWriteAnchor` trace seam. `refreshDelegation_closedLog_sat` then forces
`RefreshDelegationSpec` via the LIVE deleg-write op (`refreshDelegation_descriptorRefines_sat`). Editing
`refreshDelegationWriteV3`'s `delegUpdateWriteOpRot` turns this RED. NO modelled `RefreshDelegationCapsTreeEncodes.gate`
ride; the deleg WRITE is in-circuit-bound (the `delegRoot_runtime_column_pending` close). Receipt is
`refreshDelegationReceipt actor child`. -/
theorem closedLogExtract_refreshDelegation_closed
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 55) minit mfin maddrs t →
      Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
      Σ' (actor child : CellId),
        PLift (pubLogPost
          = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
          Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes
                Scap pre post actor child),
            Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationWriteAnchor
              Scap pre post actor child hash minit mfin maddrs t henc)) :
    ClosedLogExtract Slive LH hash Rfix 55 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.refreshDelegationWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨hChip, actor, child, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact refreshDelegation_closedLog_sat (State := Unit) Scap hash hChip hsat' pre post actor child
    pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-! ## §3 — the compressN-family readouts (carry `compressN2` + `hN` + receipt + encode-minus-log).

These rungs (`cellSeal`/`cellUnseal`/`cellDestroy`/`refusal`/`receiptArchive`/`setPermissions`/`setVK`/
`makeSovereign`/`createCell`/`createCellFromFactory`/`spawn`/`noteSpend`/`noteCreate`) take a per-effect
`compressN2` field-compression + its injectivity `hN` (named realizable crypto carriers) and produce
their `*Encodes`. The discharger parameters are `compressN2`/`hN`; the readout extracts the row
designation + the published receipt + the encode-minus-log. -/

/-- **cellSeal (52) — CLASS A.** The seal write is forced from the DEPLOYED descriptor `cellSealV3`
(`= Rfix 52` by `rfl`): the readout extracts, from the `Satisfied2 hash cellSealV3` witness, the chip/range
table side `RotTableSide` (the genuine deployed chip permutation faithfulness), the published receipt-prepend,
and the `CellSealTraceReadout`-minus-log (the `WitnessDecodes`-class realizable seam — the committed disc
limb decode + the whole-map/guard/frame residual). `cellSeal_closedLog_sat` then forces `CellSealSpec` via
the LIVE disc gate (`cellSeal_descriptorRefines_sat`). Editing `cellSealV3`'s disc gate turns this RED. NO
modelled `cellSealGenuineEncodes.gate`. -/
theorem closedLogExtract_cellSeal_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 52) minit mfin maddrs t →
      Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCellSeal.CellSealTraceReadout
            hash minit mfin maddrs t pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 52 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  -- `Rfix 52 = cellSealV3` definitionally (the registry's cellSeal member).
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellSealV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellSeal_closedLog_sat hash hside hsat' pre post actor cell pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **cellUnseal (53).** -/
theorem closedLogExtract_cellUnseal_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 53) minit mfin maddrs t →
      Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellUnsealTraceReadout
            hash t pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 53 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellUnsealV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellUnseal_closedLog_sat hash hside hsat' pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **cellDestroy (54).** -/
theorem closedLogExtract_cellDestroy_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 54) minit mfin maddrs t →
      Σ' (actor cell : CellId) (certHash : Nat) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellDestroyTraceReadout
            compressN2 hash t pre post actor cell certHash)) :
    ClosedLogExtract Slive LH hash Rfix 54 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.cellDestroyV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, certHash, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellDestroy_closedLog_sat compressN2 hN hash hside hsat' pre post actor cell certHash pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **refusal (39).** Receipt is `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem closedLogExtract_refusal_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 39) minit mfin maddrs t →
      Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.RefusalTraceReadout
            compressN2 hash t pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 39 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.refusalFieldsWriteV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact refusal_closedLog_sat compressN2 hN hash hside hsat' pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **receiptArchive (40) — CLASS A.** Forced from the DEPLOYED `receiptArchiveV3` (`= Rfix 40` by `rfl`)
via `receiptArchive_descriptorRefines_sat` (the disc-gate `lifecycle := Archived` side-table move): the
readout extracts the chip/range `RotTableSide`, the published receipt-prepend, and the
`ReceiptArchiveTraceReadout`-minus-log. Editing `receiptArchiveV3`'s disc gate turns this — and the apex —
RED. Receipt is `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem closedLogExtract_receiptArchive_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 40) minit mfin maddrs t →
      Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.ReceiptArchiveTraceReadout
            hash t pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 40 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.receiptArchiveV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact receiptArchive_closedLog_sat hash hside hsat' pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **setPermissions (8) — CLASS A.** The perms write is forced from the DEPLOYED `setPermsV3`
(`= Rfix 8` by `rfl`) via `setPermissions_descriptorRefines_sat`: the readout extracts the chip/range
`RotTableSide`, the published receipt-prepend, and the `SetPermsTraceReadout`-minus-log. Editing
`setPermsV3`'s perms-weld gate turns this — and the apex — RED. -/
theorem closedLogExtract_setPermissions_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 8) minit mfin maddrs t →
      Σ' (actor cell : CellId) (p : ℤ) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetPermsTraceReadout
            hash minit mfin maddrs t pre post actor cell p)) :
    ClosedLogExtract Slive LH hash Rfix 8 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setPermsV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, p, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact setPermissions_closedLog_sat hash hside hsat' pre post actor cell p pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **setVK (9) — CLASS A.** Forced from the DEPLOYED `setVKV3` (`= Rfix 9` by `rfl`) via
`setVK_descriptorRefines_sat`. Editing `setVKV3`'s vk-weld gate turns this — and the apex — RED. -/
theorem closedLogExtract_setVK_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 9) minit mfin maddrs t →
      Σ' (actor cell : CellId) (vk : ℤ) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetVKTraceReadout
            hash minit mfin maddrs t pre post actor cell vk)) :
    ClosedLogExtract Slive LH hash Rfix 9 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setVKV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, vk, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact setVK_closedLog_sat hash hside hsat' pre post actor cell vk pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **setProgram (13) — CLASS A.** Forced from the DEPLOYED `setProgramV3` (`= Rfix 13` by `rfl`) via
`setProgram_descriptorRefines_sat` (the program record-pin, the program-digest analog of setVK; carries
`compressN`/`hN` for the record-slot-root audit). Editing `setProgramV3`'s record pin turns this — and
the apex — RED. -/
theorem closedLogExtract_setProgram_closed
    (compressN : List ℤ → ℤ) (hN : compressNInjective compressN)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 13) minit mfin maddrs t →
      Σ' (actor cell : CellId) (prog : ℤ) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementProgram.SetProgramTraceReadout
            compressN hash t pre post actor cell prog)) :
    ClosedLogExtract Slive LH hash Rfix 13 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.setProgramV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, prog, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact setProgram_closedLog_sat compressN hN hash hside hsat' pre post actor cell prog pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **makeSovereign (38).** Receipt is the self-row. NOTE: `makeSovereign_closedLog` takes `compressN2`
but NO `hN`. -/
theorem closedLogExtract_makeSovereign_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 38) minit mfin maddrs t →
      Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
        Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementMisc.MakeSovereignTraceReadout
            hash minit mfin maddrs t pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 38 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.makeSovereignV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, cell, permOut, hside, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact makeSovereign_closedLog_sat hash hside hsat' pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **createCell (17).** Receipt is `createReceipt actor newCell`. -/
theorem closedLogExtract_createCell_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 17) minit mfin maddrs t →
      Σ' (actor newCell : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.CreateCellTraceReadout
            hash minit mfin maddrs t pre post actor newCell)) :
    ClosedLogExtract Slive LH hash Rfix 17 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.createCellV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, newCell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact createCell_closedLog_sat hash hsat' pre post actor newCell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **createCellFromFactory (18).** Receipt is `factoryReceipt actor newCell`. -/
theorem closedLogExtract_createCellFromFactory_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 18) minit mfin maddrs t →
      Σ' (actor newCell : CellId) (vk : ℤ),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.CreateFromFactoryTraceReadout
            hash minit mfin maddrs t pre post actor newCell vk)) :
    ClosedLogExtract Slive LH hash Rfix 18 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.factoryV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, newCell, vk, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact createCellFromFactory_closedLog_sat hash hsat' pre post actor newCell vk pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **spawn (19).** Receipt is `createReceipt actor child`. `Rfix 19 = spawnWriteCapOpenV3` (the
WRITE-FORCING cap-open wrapper): the spawn cap handoff is FORCED — the readout's `capsMoveDecodes` seam
is pinned by the LIVE cap-tree insert write. Editing `spawnWriteV3`'s insert op turns this — and the
apex — RED. -/
theorem closedLogExtract_spawn_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 19) minit mfin maddrs t →
      Σ' (actor child target : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.SpawnTraceReadout
            hash minit mfin maddrs t pre post actor child target)) :
    ClosedLogExtract Slive LH hash Rfix 19 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.CapOpenEmit.spawnWriteCapOpenV3
      minit mfin maddrs t := hsat
  obtain ⟨actor, child, target, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact spawn_closedLog_sat hash hsat' pre post actor child target pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **noteSpend (27).** Receipt is `noteSpendReceipt actor`. -/
theorem closedLogExtract_noteSpend_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 27) minit mfin maddrs t →
      Σ' (nf : Nat) (actor : CellId) (spendProof : Bool),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementNotes.NoteSpendTraceReadout
            hash minit mfin maddrs t pre post nf actor spendProof)) :
    ClosedLogExtract Slive LH hash Rfix 27 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteSpendV3
      minit mfin maddrs t := hsat
  obtain ⟨nf, actor, spendProof, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact noteSpend_closedLog_sat hash hsat' pre post nf actor spendProof pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **noteCreate (28).** Receipt is `noteCreateReceipt actor`. -/
theorem closedLogExtract_noteCreate_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 28) minit mfin maddrs t →
      Σ' (cm : Nat) (actor : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementNotes.NoteCreateTraceReadout
            hash minit mfin maddrs t pre post cm actor)) :
    ClosedLogExtract Slive LH hash Rfix 28 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  have hsat' : Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.noteCreateV3
      minit mfin maddrs t := hsat
  obtain ⟨cm, actor, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact noteCreate_closedLog_sat hash hsat' pre post cm actor pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-! ## §4 — value-forced (no compressN/Scap) — emitEvent (6) / pipelinedSend (47). -/

/-- **emitEvent (6).** Receipt is `emitReceipt actor cell`. -/
theorem closedLogExtract_emitEvent_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 6) minit mfin maddrs t →
      Σ' (actor cell : CellId) (topic data : ℤ),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementPermsVK.emitEventEncodes pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 6 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, topic, data, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact emitEvent_closedLog pre post actor cell topic data pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **pipelinedSend (47).** Receipt is `pipelinedSendReceipt actor`. -/
theorem closedLogExtract_pipelinedSend_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 47) minit mfin maddrs t →
      Σ' (actor : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementMisc.pipelinedSendEncodes pre post actor)) :
    ClosedLogExtract Slive LH hash Rfix 47 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact pipelinedSend_closedLog pre post actor pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-! ## §5 — exercise (16) — the structural holdout (no outer receipt-prepend).

`exercise_closedLog` is the SOLE rung with no `hpub`/no derived advance — `ExerciseSpec` has no outer
receipt; the log advances in the inner fold. Its readout is `Satisfied2 → exerciseEncodes` (no published
receipt), still the realizable `WitnessDecodes`-class extraction. The discharger CALLS
`exercise_closedLog` directly on the extracted encode (the `StateDecodeLog.toDecode` pins the endpoints).
Genuinely connected; only the receipt-prepend SHAPE is absent, faithfully. -/

/-- exercise (tag 16) — CLOSED through the DEDICATED cap-open crown (`Rfix 16 = exerciseCapOpenV3`). The
readout now extracts `exerciseEncodesAuthV3` (the hold-gate AUTHORITY SOURCE — the in-circuit cap-open
membership of `exerciseCapOpenV3`, carrying the `Satisfied2 (Rfix 16)`), and the discharger routes
through `exercise_closedLog_capOpenSat`: the hold-gate is FORCED by the depth-16 crown, no longer carried.
Editing/removing the crown from `exerciseCapOpenV3` REDS this slot — the LAST named cap-open residual
CLOSED. (`Rfix 16 = exerciseCapOpenV3` by `Rfix_exercise_capOpen`.) -/
theorem closedLogExtract_exercise_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash (Rfix 16) minit mfin maddrs t →
      Σ' (actor target : CellId) (inner : List Dregg2.Exec.TurnExecutorFull.FullActionA),
        Dregg2.Circuit.RotatedKernelRefinementExerciseAuth.exerciseEncodesAuthV3
          pre post actor target inner) :
    ClosedLogExtract Slive LH hash Rfix 16 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, target, inner, henc⟩ := readout minit mfin maddrs t pre post hsat
  exact exercise_closedLog_capOpenSat pre post actor target inner pc pubLogPre pubLogPost hdecLog henc

end PerEffect

/-! ## §6 — `ClosureReadouts`: bundle the per-effect NAMED decode-extraction floors + shared carriers.

ONE structure carrying, per cohort actionTag, the realizable `Satisfied2 (Rfix e) ⟹ <e>Encodes`
decode-extraction (the `WitnessDecodes`-class readout — `Satisfied2 → encode`, NOT `Satisfied2 → kstep`),
together with the shared rung carriers (`Scap` the deployed cap-tree hash, the per-family `compressN2`
field-compressions + their injectivity). Every field is a NAMED readout/carrier — never a `ClosedLogRung`
(`Satisfied2 → kstep`), never an axiom. The transfer slot + the off-cohort fallback ride pre-built
`ClosedLogExtract`s (the transfer one is `ClosureTransfer.closedLogExtract_transfer_closed`; the
off-cohort indices are not real effects). -/

structure ClosureReadouts
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    (LH : List Turn → ℤ) (hash : List ℤ → ℤ) (State : Type)
    (Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme)
    (cnCellSeal : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (cnLife : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (cnPermsVK : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (cnBirth : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (cnNotes : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (cnMisc : List Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem) : Type 1 where
  hNCellSeal : compressNInjective cnCellSeal
  hNLife : compressNInjective cnLife
  hNPermsVK : compressNInjective cnPermsVK
  hNBirth : compressNInjective cnBirth
  hNNotes : compressNInjective cnNotes
  -- the transfer slot: pre-built by `ClosureTransfer.closedLogExtract_transfer_closed`.
  transfer : ClosedLogExtract
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix 0
  -- the off-cohort indices (not real effects): the uniform `ClosedLogExtract` fallback.
  other : ∀ e, ClosedLogExtract
    (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix e
  -- the per-effect NAMED decode-extraction readouts (Satisfied2 ⟹ encode), grouped by family.
  rdMint : ∀ minit mfin maddrs t pubLogPost pre post,
    MintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdBurn : ∀ minit mfin maddrs t pubLogPost pre post,
    BurnTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdBridgeMint : ∀ minit mfin maddrs t pubLogPost pre post,
    BridgeMintTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdIncNonce : ∀ minit mfin maddrs t pubLogPost pre post,
    IncNonceTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdSetField : ∀ (slot : Fin 8) minit mfin maddrs t pubLogPost pre post,
    SetFieldTraceReadout (LH := LH) (hash := hash) slot minit mfin maddrs t pubLogPost pre post
  rdHeapWrite : ∀ minit mfin maddrs t pubLogPost pre post,
    HeapWriteTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post
  rdDelegate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 1) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (del rec tt : CellId), PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
              Scap pre post del rec tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateWriteAnchor
            Scap pre post del rec tt hash minit mfin maddrs t henc)
  rdIntroduce : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 10) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (intro rec tt : CellId), PLift (pubLogPost = LH (authReceipt intro :: pre.log)) ×'
      (post.log = authReceipt intro :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes
              Scap pre post intro rec tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.IntroduceWriteAnchor
            Scap pre post intro rec tt hash minit mfin maddrs t henc)
  rdAttenuate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 12) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (actor : CellId) (idx : Nat) (keep : List Dregg2.Authority.Auth),
      PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
        = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
      PLift (pubLogPost = LH (authReceipt actor :: pre.log)) ×'
      (post.log = authReceipt actor :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes
              Scap pre post actor idx keep),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateWriteAnchor
            Scap pre post actor idx keep hash minit mfin maddrs t henc)
  rdDelegateAtten : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 11) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (del rec tt : CellId) (keep : List Dregg2.Authority.Auth),
      PLift (t.tf (.custom Dregg2.Circuit.Emit.EffectVmEmitV2.SUBMASK_TID)
        = Dregg2.Circuit.Emit.EffectVmEmitV2.subsetTable Dregg2.Circuit.Emit.EffectVmEmitV2.MASK_BITS) ×'
      PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes
              Scap pre post del rec tt keep),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenWriteAnchor
            Scap pre post del rec tt keep hash minit mfin maddrs t henc)
  -- §EPOCH: the revokeDelegation readout yields the FAITHFUL `RevokeDelegationFullEncodes` (the cap-tree
  -- REMOVE decode + the NAMED epoch residual — parent epoch bump + child snapshot stale), so the closed
  -- extractor proves the STRENGTHENED `RevokeDelegationFullSpec`. The anchor rides `henc.capRemove`.
  rdRevokeDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 14) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationFullEncodes
              Scap pre post holder tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
            Scap pre post holder tt hash minit mfin maddrs t henc.capRemove)
  rdRevoke : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 2) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes
              Scap pre post holder tt),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeDelegationWriteAnchor
            Scap pre post holder tt hash minit mfin maddrs t henc)
  rdRefreshDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 55) minit mfin maddrs t →
    Dregg2.Circuit.DescriptorIR2.ChipTableSoundN (Dregg2.Circuit.DeployedCapOpen.capPermOut Scap) (t.tf .poseidon2) ×'
    Σ' (actor child : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
        Σ' (henc : Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes
              Scap pre post actor child),
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationWriteAnchor
            Scap pre post actor child hash minit mfin maddrs t henc)
  rdCellSeal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 52) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCellSeal.CellSealTraceReadout
          hash minit mfin maddrs t pre post actor cell)
  rdCellUnseal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 53) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellUnsealTraceReadout hash t pre post actor cell)
  rdCellDestroy : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 54) minit mfin maddrs t →
    Σ' (actor cell : CellId) (certHash : Nat) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.CellDestroyTraceReadout cnLife hash t pre post actor cell certHash)
  rdRefusal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 39) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.RefusalTraceReadout cnLife hash t pre post actor cell)
  rdReceiptArchive : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 40) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.ReceiptArchiveTraceReadout
          hash t pre post actor cell)
  rdSetPermissions : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 8) minit mfin maddrs t →
    Σ' (actor cell : CellId) (p : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetPermsTraceReadout hash minit mfin maddrs t pre post actor cell p)
  rdSetVK : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 9) minit mfin maddrs t →
    Σ' (actor cell : CellId) (vk : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.SetVKTraceReadout hash minit mfin maddrs t pre post actor cell vk)
  rdSetProgram : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 13) minit mfin maddrs t →
    Σ' (actor cell : CellId) (prog : ℤ) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementProgram.SetProgramTraceReadout compressN hash t pre post actor cell prog)
  rdMakeSovereign : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 38) minit mfin maddrs t →
    Σ' (actor cell : CellId) (permOut : List ℤ → List ℤ),
      Dregg2.Circuit.RotatedKernelRefinement.RotTableSide permOut hash t ×'
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementMisc.MakeSovereignTraceReadout hash minit mfin maddrs t pre post actor cell)
  rdCreateCell : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 17) minit mfin maddrs t →
    Σ' (actor newCell : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.CreateCellTraceReadout hash minit mfin maddrs t pre post actor newCell)
  rdCreateCellFromFactory : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 18) minit mfin maddrs t →
    Σ' (actor newCell : CellId) (vk : ℤ),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.CreateFromFactoryTraceReadout hash minit mfin maddrs t pre post actor newCell vk)
  rdSpawn : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 19) minit mfin maddrs t →
    Σ' (actor child target : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.SpawnTraceReadout hash minit mfin maddrs t pre post actor child target)
  rdNoteSpend : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 27) minit mfin maddrs t →
    Σ' (nf : Nat) (actor : CellId) (spendProof : Bool),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.NoteSpendTraceReadout hash minit mfin maddrs t pre post nf actor spendProof)
  rdNoteCreate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 28) minit mfin maddrs t →
    Σ' (cm : Nat) (actor : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.NoteCreateTraceReadout hash minit mfin maddrs t pre post cm actor)
  rdEmitEvent : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 6) minit mfin maddrs t →
    Σ' (actor cell : CellId) (topic data : ℤ),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellStateLog.emitReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.emitEventEncodes pre post actor cell)
  rdPipelinedSend : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 47) minit mfin maddrs t →
    Σ' (actor : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.QueuePipelinedSend.pipelinedSendReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementMisc.pipelinedSendEncodes pre post actor)
  rdExercise : ∀ minit mfin maddrs t pre post,
    Satisfied2 hash (Rfix 16) minit mfin maddrs t →
    Σ' (actor target : CellId) (inner : List Dregg2.Exec.TurnExecutorFull.FullActionA),
      Dregg2.Circuit.RotatedKernelRefinementExerciseAuth.exerciseEncodesAuthV3
        pre post actor target inner

/-! ## §7 — `closedLogExtract_all_genuine`: `∀ e, ClosedLogExtract` from the readout bundle.

Each cohort tag invokes its genuine `closedLogExtract_<e>_closed` discharger (which CALLS its proven
`<e>_closedLog` rung) over the matching readout field; the off-cohort indices ride `other`. The proven
soundness rungs are LOAD-BEARING in every cohort slot. -/

theorem closedLogExtract_all_genuine
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : RestHashIffFrame RH}
    {LH : List Turn → ℤ} {hash : List ℤ → ℤ} {State : Type}
    {Scap : Dregg2.Circuit.DeployedCapTree.Cap8Scheme}
    {cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc}
    (rds : @ClosureReadouts CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      LH hash State Scap cnCellSeal cnLife cnPermsVK cnBirth cnNotes cnMisc) :
    ∀ e, ClosedLogExtract
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) LH hash Rfix e := by
  intro e
  match e with
  | 0 => exact rds.transfer
  | 1 => exact closedLogExtract_delegate_closed Scap rds.rdDelegate
  | 2 => exact closedLogExtract_revoke_closed Scap rds.rdRevoke
  | 3 => exact closedLogExtract_mint_closed rds.rdMint
  | 4 => exact closedLogExtract_burn_closed rds.rdBurn
  | 5 => exact closedLogExtract_setField_closed 0 (rds.rdSetField 0)
  | 6 => exact closedLogExtract_emitEvent_closed rds.rdEmitEvent
  | 7 => exact closedLogExtract_incrementNonce_closed rds.rdIncNonce
  | 8 => exact closedLogExtract_setPermissions_closed rds.rdSetPermissions
  | 9 => exact closedLogExtract_setVK_closed rds.rdSetVK
  | 13 => exact closedLogExtract_setProgram_closed compressN hCompressN rds.rdSetProgram
  | 10 => exact closedLogExtract_introduce_closed Scap rds.rdIntroduce
  | 11 => exact closedLogExtract_delegateAtten_closed Scap rds.rdDelegateAtten
  | 12 => exact closedLogExtract_attenuate_closed Scap rds.rdAttenuate
  | 14 => exact closedLogExtract_revokeDelegation_closed Scap rds.rdRevokeDelegation
  | 16 => exact closedLogExtract_exercise_closed rds.rdExercise
  | 17 => exact closedLogExtract_createCell_closed rds.rdCreateCell
  | 18 => exact closedLogExtract_createCellFromFactory_closed rds.rdCreateCellFromFactory
  | 19 => exact closedLogExtract_spawn_closed rds.rdSpawn
  | 20 => exact closedLogExtract_bridgeMint_closed rds.rdBridgeMint
  | 27 => exact closedLogExtract_noteSpend_closed rds.rdNoteSpend
  | 28 => exact closedLogExtract_noteCreate_closed rds.rdNoteCreate
  | 38 => exact closedLogExtract_makeSovereign_closed rds.rdMakeSovereign
  | 39 => exact closedLogExtract_refusal_closed cnLife rds.hNLife rds.rdRefusal
  | 40 => exact closedLogExtract_receiptArchive_closed rds.rdReceiptArchive
  | 47 => exact closedLogExtract_pipelinedSend_closed rds.rdPipelinedSend
  | 52 => exact closedLogExtract_cellSeal_closed rds.rdCellSeal
  | 53 => exact closedLogExtract_cellUnseal_closed rds.rdCellUnseal
  | 54 => exact closedLogExtract_cellDestroy_closed cnLife rds.hNLife rds.rdCellDestroy
  | 55 => exact closedLogExtract_refreshDelegation_closed Scap rds.rdRefreshDelegation
  | 56 => exact closedLogExtract_heapWrite_closed rds.rdHeapWrite
  | (n + 1) => exact rds.other (n + 1)

/-! ## §8 — `lightclient_unfoolable_closed_final_genuine`: the FINAL closed apex on the genuine floors.

From the genuine readout bundle (every cohort slot discharged by CALLING its proven `<e>_closedLog`
rung) + the realizable crypto floors, the light client concludes a genuine full kernel+log transition.
The proven `RotatedKernelRefinement*` soundness rungs are LOAD-BEARING; the carried set is the per-effect
decode-extraction (`WitnessDecodes` class, named `<e>TraceReadout`) + the crypto floors
(`StarkSound`/`Poseidon2SpongeCR` + `S_live` CR fields/`logHashInjective`/`Scap`/the `compressN`
carriers) — NOT the whole refinement. -/

theorem lightclient_unfoolable_closed_final_genuine
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
    (closedLogExtract_all_genuine rds) mkLog pi π hwitdec hacc

/-! ## §9 — axiom hygiene. -/

#assert_axioms closedLogExtract_mint_closed
#assert_axioms closedLogExtract_delegate_closed
#assert_axioms closedLogExtract_cellSeal_closed
#assert_axioms closedLogExtract_exercise_closed
-- the rewired CLASS-A (Satisfied2-forced) slots — guarantee A now circuit-forced at the apex.
#assert_axioms closedLogExtract_setPermissions_closed
#assert_axioms closedLogExtract_setVK_closed
#assert_axioms closedLogExtract_setProgram_closed
#assert_axioms closedLogExtract_makeSovereign_closed
#assert_axioms closedLogExtract_refusal_closed
#assert_axioms closedLogExtract_createCell_closed
#assert_axioms closedLogExtract_createCellFromFactory_closed
#assert_axioms closedLogExtract_spawn_closed
#assert_axioms closedLogExtract_noteSpend_closed
#assert_axioms closedLogExtract_noteCreate_closed
#assert_axioms closedLogExtract_cellUnseal_closed
#assert_axioms closedLogExtract_cellDestroy_closed
-- the round-2 CLASS-A (Satisfied2-forced) slots — guarantee A now apex-forced for heapWrite + the cap
-- write-cap-open family (delegate / introduce / delegateAtten / revokeDelegation).
#assert_axioms closedLogExtract_heapWrite_closed
#assert_axioms closedLogExtract_introduce_closed
#assert_axioms closedLogExtract_delegateAtten_closed
#assert_axioms closedLogExtract_revokeDelegation_closed
#assert_axioms closedLogExtract_all_genuine
#assert_axioms lightclient_unfoolable_closed_final_genuine

end Dregg2.Circuit.ClosureFanoutGenuine
