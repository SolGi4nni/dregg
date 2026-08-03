/-
# Dregg2.Circuit.CircuitCompletenessTransferConstruct — the VALUE-leg (transfer) floor REDUCTION.

## The laundering this shrinks

`CircuitCompleteness.transfer_descriptorComplete` takes a `buildWitness` floor that bundles, per move,
ELEVEN things: the satisfying trace `Satisfied2 hash transferV3 … t`, its publication of the kernel
commitment, the FOUR spec-determined boundary `CellState.balLo` equalities, the FOUR spec-determined
`TransferParams` direction/amount equalities, AND the `TransferTraceProver` rows. Of these, only the
TRACE realizability (the `Satisfied2` + its publication) genuinely needs the prover (it is the
StarkComplete-class floor — the constraint-satisfaction over a CONCRETE `VmTrace`, which no amount of
spec-reasoning can synthesize, exactly the Stage-0 finding). The other NINE are spec-DETERMINED: the
boundary limbs ARE the kernel ledger and the tags ARE the transfer's direction/amount — bundling them
into the floor LAUNDERS the satisfiability claim with data the kernel already fixes.

## What this module does

It reduces the carried floor to the MINIMAL `TransferSatFloor`: ONE realizability, `∃ a satisfying
transfer trace publishing the kernel's own commitment` — NOTHING else. Everything the kernel move
determines (the commitment via `stateDecode_construct`; the genuine-debit non-vacuity via
`transfer_descriptorComplete_genuine`) is CONSTRUCTED. `transfer_descriptorComplete_reduced` re-proves
the transfer satisfiability rung from `TransferSatFloor` alone — a STRICTLY leaner floor than the fat
`buildWitness`. This is the value-leg analog of the authority-leg `CapOpenTraceFloor` reduction.

## The honest accounting (what irreducibly remains)

`TransferSatFloor` carries exactly `Satisfied2 hash transferV3 minit mfin maddrs t` (the descriptor's
IR-v2 constraints all evaluate to 0 on the concrete trace + the chip/memory/map table faithfulness) and
`tracePublishedCommit t = commitOf S pre post turn` (the trace publishes the kernel's own roots). By
Stage 0, `Satisfied2` is PURE constraint satisfaction over a concrete `VmTrace` — there is NO FRI /
polynomial / AIR-prover content inside it; the FRI gap is the SEPARATE `StarkComplete` bridge. So
`TransferSatFloor` is the minimal legitimate "the honest prover's transfer run produces a satisfying
trace publishing the kernel commitment" realizability — the dual of the soundness `StarkSound`
extraction, NOT the conclusion. The decode/commitment/non-vacuity are all constructed here.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `Satisfied2` is CARRIED (the named floor),
not assumed as an axiom; `stateDecode_construct` is CONSTRUCTIVE. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompleteness

namespace Dregg2.Circuit.CircuitCompletenessTransferConstruct

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitSoundnessAssembled
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.Spec.BalanceMovement (BalanceMovementSpec)
open Dregg2.Circuit.StateCommit (AccountsWF compressInjective compressNInjective cellLeafInjective
  RestHashIffFrame)
open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2)
open Dregg2.Circuit.ClosureSurface (S_live)
open Dregg2.Circuit.CircuitCompleteness (commitOf stateDecode_construct)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `TransferSatFloor`: the MINIMAL trace realizability (the StarkComplete dual).

The honest prover's transfer run, REDUCED to ONLY what genuinely needs it: a memory boundary, a
concrete `VmTrace`, the `Satisfied2` of the live `transferV3` descriptor, and the publication of the
kernel's own commitment. NONE of the spec-determined boundary limbs / tags / rows are here — they are
the encode the kernel fixes (`transfer_rotatedEncodes_construct`), not a floor. -/

/-- **`TransferSatFloor hash S pre post turn` — the MINIMAL transfer trace realizability (NAMED).** A
memory boundary `(minit, mfin, maddrs)`, a concrete `VmTrace t`, the `Satisfied2` of the live
`transferV3` descriptor over `t`, and the fact that `t` publishes the kernel's own commitment
`commitOf S pre post turn`. This is the StarkComplete-class floor (the prover's actual satisfying
transfer trace) — the dual of the soundness `StarkSound` extraction, with everything the kernel move
determines (the commitment, the decode, the genuine debit) CONSTRUCTED elsewhere, NOT bundled here.
DATA-bearing (`Type`). -/
structure TransferSatFloor (hash : List ℤ → ℤ) (S : CommitSurface)
    (pre post : RecChainedState) (turn : BoundaryTurn) : Type where
  minit : ℤ → ℤ
  mfin : ℤ → ℤ × Nat
  maddrs : List ℤ
  t : VmTrace
  /-- the prover's BUILT satisfying transfer trace of the live `transferV3` descriptor. -/
  hsat : Satisfied2 hash transferV3 minit mfin maddrs t
  /-- the trace publishes the kernel's OWN commitment (the prover's PI is the genuine roots). -/
  hpub : tracePublishedCommit t = commitOf S pre post turn

/-! ## §2 — `transfer_descriptorComplete_reduced`: the rung from the MINIMAL floor.

The transfer satisfiability rung, re-proved from `TransferSatFloor` ALONE — a strictly leaner floor
than the fat `buildWitness` (which carried the trace PLUS nine spec-determined conjuncts). The
commitment decode is CONSTRUCTED (`stateDecode_construct`), the satisfiability is the carried floor;
the spec-determined boundary data is NOT needed to STATE satisfiability (it was needed only for the
non-vacuity tooth, which is the SEPARATE `transfer_descriptorComplete_genuine`). -/

/-- **`transfer_descriptorComplete_reduced` — the transfer satisfiability rung from the MINIMAL floor.**
Given the MINIMAL `TransferSatFloor` (the prover's satisfying transfer trace publishing the kernel
commitment) and `AccountsWF` boundary kernels, there is a circuit witness of `transferV3` whose
published commitment decodes to `(pre, post)`. The decode is CONSTRUCTED (`stateDecode_construct`); the
ONLY carried realizability is the floor's `Satisfied2` + publication. This is `transfer_descriptorComplete`
with the floor SHRUNK to the irreducible StarkComplete-class core — the nine spec-determined conjuncts
the fat `buildWitness` bundled are GONE (they are determined by the kernel move, not assumed). -/
theorem transfer_descriptorComplete_reduced
    {CH : CellId → Value → ℤ} {RH : RecordKernelState → ℤ}
    {cmb compress : ℤ → ℤ → ℤ} {compressN : List ℤ → ℤ}
    {hCmb : compressInjective cmb} {hCompress : compressInjective compress}
    {hCompressN : compressNInjective compressN} {hLeaf : cellLeafInjective CH}
    {hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH}
    (hash : List ℤ → ℤ)
    (pre post : RecChainedState) (turn : BoundaryTurn)
    (hpreWF : AccountsWF pre.kernel) (hpostWF : AccountsWF post.kernel)
    (floor : TransferSatFloor hash
      (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pre post turn) :
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash transferV3 minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf
        (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest) pre post turn ∧
      StateDecode (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
        (commitOf (S_live CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest)
          pre post turn) pre post :=
  ⟨floor.minit, floor.mfin, floor.maddrs, floor.t, floor.hsat, floor.hpub,
   stateDecode_construct _ pre post turn hpreWF hpostWF⟩

/-! ## §3 — the floor is REACHED from the fat `buildWitness` (the reduction is FAITHFUL, not a fork).

To pin that `TransferSatFloor` is a genuine REDUCTION of the original `buildWitness` (not a divergent,
weaker floor), we exhibit that the fat floor's output PRODUCES a `TransferSatFloor`: the nine
spec-determined conjuncts are DISCARDED (they were determined by the kernel move), and only the trace +
publication survive. So anything provable with the old floor is provable with the new — the floor
genuinely SHRANK. -/

/-- **`buildWitness_to_satFloor` — the fat `buildWitness` output REDUCES to the minimal floor.** The
`Satisfied2` + publication that the original per-move `buildWitness` produces ARE a `TransferSatFloor`;
the nine spec-determined conjuncts it additionally bundled are dropped. This witnesses that the
reduction is faithful: the minimal floor is reached from the old one, so the carried set strictly
shrank (the new rung needs only the trace, the old needed the trace AND the spec-redundant data). -/
def buildWitness_to_satFloor (hash : List ℤ → ℤ) (S : CommitSurface)
    (pre post : RecChainedState) (turn : BoundaryTurn)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash transferV3 minit mfin maddrs t)
    (hpub : tracePublishedCommit t = commitOf S pre post turn) :
    TransferSatFloor hash S pre post turn where
  minit := minit
  mfin := mfin
  maddrs := maddrs
  t := t
  hsat := hsat
  hpub := hpub

/-! ## §4 — axiom hygiene. -/

#assert_axioms transfer_descriptorComplete_reduced
#assert_axioms buildWitness_to_satFloor

end Dregg2.Circuit.CircuitCompletenessTransferConstruct
