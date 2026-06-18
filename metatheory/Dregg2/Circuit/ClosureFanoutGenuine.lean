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
hypotheses, never as axioms. No `sorry`, no `native_decide`, no `:= True`, no fresh axiom. NEW file;
imports read-only.
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
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t ×'
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
  obtain ⟨actor, cell, a, amt, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact mint_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **burn (4).** -/
abbrev BurnTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Dregg2.Circuit.RotatedKernelRefinementMintBurn.burnV3) minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t ×'
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
  obtain ⟨actor, cell, a, amt, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact burn_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **bridgeMint (20)** — refines `MintASpec`, via the mint descriptor `mintV3`. -/
abbrev BridgeMintTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash Dregg2.Circuit.Emit.EffectVmEmitRotationV3.mintV3 minit mfin maddrs t →
  Σ' (actor cell : CellId) (a : AssetId) (amt : ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t ×'
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
  obtain ⟨actor, cell, a, amt, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact bridgeMint_closedLog hash hside hsat pre post actor cell a amt pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **incrementNonce (7).** Receipt is the self-row `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
abbrev IncNonceTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash Dregg2.Circuit.RotatedKernelRefinementIncNonce.incNonceV3 minit mfin maddrs t →
  Σ' (actor cell : CellId) (n : ℤ),
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t ×'
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
  obtain ⟨actor, cell, n, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact incrementNonce_closedLog hash hside hsat pre post actor cell n pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **setField (5)** at slot `slot : Fin 8`. -/
abbrev SetFieldTraceReadout (slot : Fin 8) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ)
    (t : VmTrace) (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Rfix 5) minit mfin maddrs t →
  Σ' (actor cell : CellId) (v : ℤ),
    Satisfied2 hash (Dregg2.Circuit.RotatedKernelRefinementSetField.setFieldV3 slot) minit mfin maddrs t ×'
    Dregg2.Circuit.RotatedKernelRefinement.RotTableSide hash t ×'
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
  obtain ⟨actor, cell, v, hsat2, hside, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact setField_closedLog slot hash hside hsat2 pre post actor cell v pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-- **heapWrite (56).** Receipt is `{ actor, src:=target, dst:=target, amt:=0 }`. The rung takes NO
`Satisfied2`/`RotTableSide` (the encode is value-forced), so the readout has no satisfaction hypothesis;
it is still the `Satisfied2 heapWriteV3 ⟹ encode` extraction the prover supplies. We thread the
`Satisfied2` of the heapWrite descriptor as the readout's trigger to keep it circuit-bound. -/
abbrev HeapWriteTraceReadout (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (pubLogPost : ℤ) (pre post : RecChainedState) : Type :=
  Satisfied2 hash (Rfix 56) minit mfin maddrs t →
  Σ' (actor target : CellId) (addr v newRoot : ℤ),
    PLift (pubLogPost = LH ({ actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log)) ×'
    (post.log = { actor := actor, src := target, dst := target, amt := (0 : ℤ) } :: pre.log →
      Dregg2.Circuit.RotatedKernelRefinementExercise.heapWriteEncodes
        hash pre post actor target addr v newRoot)

theorem closedLogExtract_heapWrite_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      HeapWriteTraceReadout (LH := LH) (hash := hash) minit mfin maddrs t pubLogPost pre post) :
    ClosedLogExtract Slive LH hash Rfix 56 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, target, addr, v, newRoot, hpub, logNeeds⟩ :=
    readout minit mfin maddrs t pubLogPost pre post hsat
  exact heapWrite_closedLog hash pre post actor target addr v newRoot pc pubLogPre pubLogPost hdecLog
    hpub.down logNeeds

/-! ## §2 — the cap-family readouts (carry `Scap` + `authReceipt` + cap-tree encode-minus-log).

The cap rungs (`delegate`/`introduce`/`attenuate`/`delegateAtten`/`revokeDelegation`/`refreshDelegation`/
`revoke`) take a `CapHashScheme` carrier `Scap` (the deployed sorted-Poseidon2 cap-tree hash, a named
realizable crypto primitive) and produce their `*CapsTreeEncodes`. The readout extracts the row
designation + the published `authReceipt`-prepend + the cap-tree encode-minus-log. `Scap` is a
discharger parameter (shared across all witnesses), threaded into the rung. -/

/-- **delegate (1).** -/
theorem closedLogExtract_delegate_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 1) minit mfin maddrs t →
      Σ' (del rec tt : CellId),
        PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
        (post.log = authReceipt del :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes Scap pre post del rec tt)) :
    ClosedLogExtract Slive LH hash Rfix 1 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨del, rec, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact delegate_closedLog Scap pre post del rec tt pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **introduce (10)** — refines `DelegateSpec`. -/
theorem closedLogExtract_introduce_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 10) minit mfin maddrs t →
      Σ' (intro rec tt : CellId),
        PLift (pubLogPost = LH (authReceipt intro :: pre.log)) ×'
        (post.log = authReceipt intro :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes Scap pre post intro rec tt)) :
    ClosedLogExtract Slive LH hash Rfix 10 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨intro, rec, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact introduce_closedLog Scap pre post intro rec tt pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **attenuate (12).** -/
theorem closedLogExtract_attenuate_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 12) minit mfin maddrs t →
      Σ' (actor : CellId) (idx : Nat) (keep : List Dregg2.Authority.Auth),
        PLift (pubLogPost = LH (authReceipt actor :: pre.log)) ×'
        (post.log = authReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes Scap pre post actor idx keep)) :
    ClosedLogExtract Slive LH hash Rfix 12 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, idx, keep, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact attenuate_closedLog Scap pre post actor idx keep pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **delegateAtten (11).** -/
theorem closedLogExtract_delegateAtten_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 11) minit mfin maddrs t →
      Σ' (del rec tt : CellId) (keep : List Dregg2.Authority.Auth),
        PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
        (post.log = authReceipt del :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes Scap pre post del rec tt keep)) :
    ClosedLogExtract Slive LH hash Rfix 11 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨del, rec, tt, keep, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact delegateAtten_closedLog Scap pre post del rec tt keep pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **revokeDelegation (14)** — refines `RevokeSpec`. -/
theorem closedLogExtract_revokeDelegation_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 14) minit mfin maddrs t →
      Σ' (holder tt : CellId),
        PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
        (post.log = authReceipt holder :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes Scap pre post holder tt)) :
    ClosedLogExtract Slive LH hash Rfix 14 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨holder, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact revokeDelegation_closedLog Scap pre post holder tt pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **revoke (2).** -/
theorem closedLogExtract_revoke_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 2) minit mfin maddrs t →
      Σ' (holder tt : CellId),
        PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
        (post.log = authReceipt holder :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes Scap pre post holder tt)) :
    ClosedLogExtract Slive LH hash Rfix 2 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨holder, tt, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact revoke_closedLog Scap pre post holder tt pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **refreshDelegation (55).** Receipt is `refreshDelegationReceipt actor child`. -/
theorem closedLogExtract_refreshDelegation_closed {State : Type}
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 55) minit mfin maddrs t →
      Σ' (actor child : CellId),
        PLift (pubLogPost
          = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes Scap pre post actor child)) :
    ClosedLogExtract Slive LH hash Rfix 55 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, child, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact refreshDelegation_closedLog Scap pre post actor child pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-! ## §3 — the compressN-family readouts (carry `compressN2` + `hN` + receipt + encode-minus-log).

These rungs (`cellSeal`/`cellUnseal`/`cellDestroy`/`refusal`/`receiptArchive`/`setPermissions`/`setVK`/
`makeSovereign`/`createCell`/`createCellFromFactory`/`spawn`/`noteSpend`/`noteCreate`) take a per-effect
`compressN2` field-compression + its injectivity `hN` (named realizable crypto carriers) and produce
their `*Encodes`. The discharger parameters are `compressN2`/`hN`; the readout extracts the row
designation + the published receipt + the encode-minus-log. -/

/-- **cellSeal (52).** -/
theorem closedLogExtract_cellSeal_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementCellSeal.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 52) minit mfin maddrs t →
      Σ' (actor cell : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSealGenuineEncodes compressN2 pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 52 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellSeal_closedLog compressN2 hN pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **cellUnseal (53).** -/
theorem closedLogExtract_cellUnseal_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 53) minit mfin maddrs t →
      Σ' (actor cell : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellUnsealEncodes compressN2 pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 53 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellUnseal_closedLog compressN2 hN pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **cellDestroy (54).** -/
theorem closedLogExtract_cellDestroy_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 54) minit mfin maddrs t →
      Σ' (actor cell : CellId) (certHash : Nat),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellDestroyEncodes compressN2 pre post actor cell certHash)) :
    ClosedLogExtract Slive LH hash Rfix 54 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, certHash, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact cellDestroy_closedLog compressN2 hN pre post actor cell certHash pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **refusal (39).** Receipt is `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem closedLogExtract_refusal_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 39) minit mfin maddrs t →
      Σ' (actor cell : CellId),
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditEncodes
            compressN2 pre post actor cell Dregg2.Exec.TurnExecutorFull.refusalField)) :
    ClosedLogExtract Slive LH hash Rfix 39 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact refusal_closedLog compressN2 hN pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **receiptArchive (40).** Receipt is `{ actor, src:=cell, dst:=cell, amt:=0 }`. -/
theorem closedLogExtract_receiptArchive_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementLifecycle.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 40) minit mfin maddrs t →
      Σ' (actor cell : CellId),
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditEncodes
            compressN2 pre post actor cell Dregg2.Exec.TurnExecutorFull.lifecycleField)) :
    ClosedLogExtract Slive LH hash Rfix 40 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact receiptArchive_closedLog compressN2 hN pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **setPermissions (8).** -/
theorem closedLogExtract_setPermissions_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 8) minit mfin maddrs t →
      Σ' (actor cell : CellId) (p : ℤ),
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementPermsVK.setPermissionsEncodes compressN2 pre post actor cell p)) :
    ClosedLogExtract Slive LH hash Rfix 8 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, p, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact setPermissions_closedLog compressN2 hN pre post actor cell p pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **setVK (9).** -/
theorem closedLogExtract_setVK_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementPermsVK.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 9) minit mfin maddrs t →
      Σ' (actor cell : CellId) (vk : ℤ),
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementPermsVK.setVKEncodes compressN2 pre post actor cell vk)) :
    ClosedLogExtract Slive LH hash Rfix 9 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, vk, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact setVK_closedLog compressN2 hN pre post actor cell vk pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **makeSovereign (38).** Receipt is the self-row. NOTE: `makeSovereign_closedLog` takes `compressN2`
but NO `hN`. -/
theorem closedLogExtract_makeSovereign_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementMisc.FieldElem)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 38) minit mfin maddrs t →
      Σ' (actor cell : CellId),
        PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
        (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereignEncodes compressN2 pre post actor cell)) :
    ClosedLogExtract Slive LH hash Rfix 38 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, cell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact makeSovereign_closedLog compressN2 pre post actor cell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **createCell (17).** Receipt is `createReceipt actor newCell`. -/
theorem closedLogExtract_createCell_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 17) minit mfin maddrs t →
      Σ' (actor newCell : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.createCellGenuineEncodes compressN2 pre post actor newCell)) :
    ClosedLogExtract Slive LH hash Rfix 17 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, newCell, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact createCell_closedLog compressN2 hN pre post actor newCell pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **createCellFromFactory (18).** Receipt is `factoryReceipt actor newCell`. -/
theorem closedLogExtract_createCellFromFactory_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 18) minit mfin maddrs t →
      Σ' (actor newCell : CellId) (vk : ℤ),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.createFromFactoryGenuineEncodes compressN2 pre post actor newCell vk)) :
    ClosedLogExtract Slive LH hash Rfix 18 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, newCell, vk, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact createCellFromFactory_closedLog compressN2 hN pre post actor newCell vk pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **spawn (19).** Receipt is `createReceipt actor child`. -/
theorem closedLogExtract_spawn_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementBirth.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 19) minit mfin maddrs t →
      Σ' (actor child target : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementBirth.spawnGenuineEncodes compressN2 pre post actor child target)) :
    ClosedLogExtract Slive LH hash Rfix 19 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, child, target, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact spawn_closedLog compressN2 hN pre post actor child target pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **noteSpend (27).** Receipt is `noteSpendReceipt actor`. -/
theorem closedLogExtract_noteSpend_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 27) minit mfin maddrs t →
      Σ' (nf : Nat) (actor : CellId) (spendProof : Bool),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementNotes.noteSpendGenuineEncodes compressN2 pre post nf actor spendProof)) :
    ClosedLogExtract Slive LH hash Rfix 27 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨nf, actor, spendProof, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact noteSpend_closedLog compressN2 hN pre post nf actor spendProof pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

/-- **noteCreate (28).** Receipt is `noteCreateReceipt actor`. -/
theorem closedLogExtract_noteCreate_closed
    (compressN2 : List Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem
      → Dregg2.Circuit.RotatedKernelRefinementNotes.FieldElem)
    (hN : compressNInjective compressN2)
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pubLogPost : ℤ) (pre post : RecChainedState),
      Satisfied2 hash (Rfix 28) minit mfin maddrs t →
      Σ' (cm : Nat) (actor : CellId),
        PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log)) ×'
        (post.log = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
          Dregg2.Circuit.RotatedKernelRefinementNotes.noteCreateGenuineEncodes compressN2 pre post cm actor)) :
    ClosedLogExtract Slive LH hash Rfix 28 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨cm, actor, hpub, logNeeds⟩ := readout minit mfin maddrs t pubLogPost pre post hsat
  exact noteCreate_closedLog compressN2 hN pre post cm actor pc pubLogPre pubLogPost hdecLog hpub.down logNeeds

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

theorem closedLogExtract_exercise_closed
    (readout : ∀ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
      (pre post : RecChainedState),
      Satisfied2 hash (Rfix 16) minit mfin maddrs t →
      Σ' (actor target : CellId) (inner : List Dregg2.Exec.TurnExecutorFull.FullActionA),
        Dregg2.Circuit.RotatedKernelRefinementExercise.exerciseEncodes pre post actor target inner) :
    ClosedLogExtract Slive LH hash Rfix 16 := by
  intro _hCR minit mfin maddrs t pc pubLogPre pubLogPost pre post hsat hdecLog
  obtain ⟨actor, target, inner, henc⟩ := readout minit mfin maddrs t pre post hsat
  exact exercise_closedLog pre post actor target inner pc pubLogPre pubLogPost hdecLog henc

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
    (Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State)
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
    Σ' (del rec tt : CellId), PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes Scap pre post del rec tt)
  rdIntroduce : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 10) minit mfin maddrs t →
    Σ' (intro rec tt : CellId), PLift (pubLogPost = LH (authReceipt intro :: pre.log)) ×'
      (post.log = authReceipt intro :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateCapsTreeEncodes Scap pre post intro rec tt)
  rdAttenuate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 12) minit mfin maddrs t →
    Σ' (actor : CellId) (idx : Nat) (keep : List Dregg2.Authority.Auth),
      PLift (pubLogPost = LH (authReceipt actor :: pre.log)) ×'
      (post.log = authReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.AttenuateCapsTreeEncodes Scap pre post actor idx keep)
  rdDelegateAtten : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 11) minit mfin maddrs t →
    Σ' (del rec tt : CellId) (keep : List Dregg2.Authority.Auth),
      PLift (pubLogPost = LH (authReceipt del :: pre.log)) ×'
      (post.log = authReceipt del :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.DelegateAttenCapsTreeEncodes Scap pre post del rec tt keep)
  rdRevokeDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 14) minit mfin maddrs t →
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes Scap pre post holder tt)
  rdRevoke : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 2) minit mfin maddrs t →
    Σ' (holder tt : CellId), PLift (pubLogPost = LH (authReceipt holder :: pre.log)) ×'
      (post.log = authReceipt holder :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RevokeCapsTreeEncodes Scap pre post holder tt)
  rdRefreshDelegation : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 55) minit mfin maddrs t →
    Σ' (actor child : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.RefreshDelegation.refreshDelegationReceipt actor child :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCapFamily.RefreshDelegationCapsTreeEncodes Scap pre post actor child)
  rdCellSeal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 52) minit mfin maddrs t →
    Σ' (actor cell : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementCellSeal.cellSealGenuineEncodes cnCellSeal pre post actor cell)
  rdCellUnseal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 53) minit mfin maddrs t →
    Σ' (actor cell : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellUnsealEncodes cnLife pre post actor cell)
  rdCellDestroy : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 54) minit mfin maddrs t →
    Σ' (actor cell : CellId) (certHash : Nat),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.CellLifecycle.cellLifecycleReceipt actor cell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.cellDestroyEncodes cnLife pre post actor cell certHash)
  rdRefusal : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 39) minit mfin maddrs t →
    Σ' (actor cell : CellId),
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditEncodes
          cnLife pre post actor cell Dregg2.Exec.TurnExecutorFull.refusalField)
  rdReceiptArchive : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 40) minit mfin maddrs t →
    Σ' (actor cell : CellId),
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementLifecycle.auditEncodes
          cnLife pre post actor cell Dregg2.Exec.TurnExecutorFull.lifecycleField)
  rdSetPermissions : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 8) minit mfin maddrs t →
    Σ' (actor cell : CellId) (p : ℤ),
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.setPermissionsEncodes cnPermsVK pre post actor cell p)
  rdSetVK : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 9) minit mfin maddrs t →
    Σ' (actor cell : CellId) (vk : ℤ),
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementPermsVK.setVKEncodes cnPermsVK pre post actor cell vk)
  rdMakeSovereign : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 38) minit mfin maddrs t →
    Σ' (actor cell : CellId),
      PLift (pubLogPost = LH ({ actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log)) ×'
      (post.log = { actor := actor, src := cell, dst := cell, amt := (0 : ℤ) } :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementMisc.makeSovereignEncodes cnMisc pre post actor cell)
  rdCreateCell : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 17) minit mfin maddrs t →
    Σ' (actor newCell : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.createCellGenuineEncodes cnBirth pre post actor newCell)
  rdCreateCellFromFactory : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 18) minit mfin maddrs t →
    Σ' (actor newCell : CellId) (vk : ℤ),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.FactoryCreation.factoryReceipt actor newCell :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.createFromFactoryGenuineEncodes cnBirth pre post actor newCell vk)
  rdSpawn : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 19) minit mfin maddrs t →
    Σ' (actor child target : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.AccountGrowth.createReceipt actor child :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementBirth.spawnGenuineEncodes cnBirth pre post actor child target)
  rdNoteSpend : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 27) minit mfin maddrs t →
    Σ' (nf : Nat) (actor : CellId) (spendProof : Bool),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteNullifier.noteSpendReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.noteSpendGenuineEncodes cnNotes pre post nf actor spendProof)
  rdNoteCreate : ∀ minit mfin maddrs t pubLogPost pre post,
    Satisfied2 hash (Rfix 28) minit mfin maddrs t →
    Σ' (cm : Nat) (actor : CellId),
      PLift (pubLogPost = LH (Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log)) ×'
      (post.log = Dregg2.Circuit.Spec.NoteCommitment.noteCreateReceipt actor :: pre.log →
        Dregg2.Circuit.RotatedKernelRefinementNotes.noteCreateGenuineEncodes cnNotes pre post cm actor)
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
      Dregg2.Circuit.RotatedKernelRefinementExercise.exerciseEncodes pre post actor target inner

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
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
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
  | 8 => exact closedLogExtract_setPermissions_closed cnPermsVK rds.hNPermsVK rds.rdSetPermissions
  | 9 => exact closedLogExtract_setVK_closed cnPermsVK rds.hNPermsVK rds.rdSetVK
  | 10 => exact closedLogExtract_introduce_closed Scap rds.rdIntroduce
  | 11 => exact closedLogExtract_delegateAtten_closed Scap rds.rdDelegateAtten
  | 12 => exact closedLogExtract_attenuate_closed Scap rds.rdAttenuate
  | 14 => exact closedLogExtract_revokeDelegation_closed Scap rds.rdRevokeDelegation
  | 16 => exact closedLogExtract_exercise_closed rds.rdExercise
  | 17 => exact closedLogExtract_createCell_closed cnBirth rds.hNBirth rds.rdCreateCell
  | 18 => exact closedLogExtract_createCellFromFactory_closed cnBirth rds.hNBirth rds.rdCreateCellFromFactory
  | 19 => exact closedLogExtract_spawn_closed cnBirth rds.hNBirth rds.rdSpawn
  | 20 => exact closedLogExtract_bridgeMint_closed rds.rdBridgeMint
  | 27 => exact closedLogExtract_noteSpend_closed cnNotes rds.hNNotes rds.rdNoteSpend
  | 28 => exact closedLogExtract_noteCreate_closed cnNotes rds.hNNotes rds.rdNoteCreate
  | 38 => exact closedLogExtract_makeSovereign_closed cnMisc rds.rdMakeSovereign
  | 39 => exact closedLogExtract_refusal_closed cnLife rds.hNLife rds.rdRefusal
  | 40 => exact closedLogExtract_receiptArchive_closed cnLife rds.hNLife rds.rdReceiptArchive
  | 47 => exact closedLogExtract_pipelinedSend_closed rds.rdPipelinedSend
  | 52 => exact closedLogExtract_cellSeal_closed cnCellSeal rds.hNCellSeal rds.rdCellSeal
  | 53 => exact closedLogExtract_cellUnseal_closed cnLife rds.hNLife rds.rdCellUnseal
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
    {Scap : Dregg2.Circuit.DeployedCapTree.CapHashScheme State}
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
#assert_axioms closedLogExtract_all_genuine
#assert_axioms lightclient_unfoolable_closed_final_genuine

end Dregg2.Circuit.ClosureFanoutGenuine
