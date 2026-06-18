/-
# Dregg2.Circuit.CircuitCompletenessSatFloor — the UNIFORM value-leg realizability floor.

## The laundering this finishes

Every VALUE/RECORD/LIFECYCLE/SET-INSERT completeness rung (`<e>_descriptorComplete`) took a fat
`buildWitness` callback returning, per kernel step, `Σ' … (Satisfied2 hash d …) ×' publication ×'
<e>TraceProver/<e>RootProver …`. The trailing `<e>TraceProver`/`<e>RootProver` is SPEC-DETERMINED: each
rung's PROOF consumes it ONLY to build an UNUSED `rotatedEncodes`/`<e>Encodes` decode (`have _henc`),
which the conclusion (`Satisfied2 ∧ publication ∧ StateDecode`) never references — the genuine encode
survives as the SEPARATE `<e>_descriptorComplete_genuine` tooth. So the rung genuinely needs ONLY the
`Satisfied2 + publication`; bundling the prover floor LAUNDERS the satisfiability with the
kernel-determined decode data.

## What this module does

It folds those per-effect `Satisfied2`-publication carriers into ONE descriptor-AGNOSTIC realizability:
`SatFloor S hash d kstep` — "every kernel `kstep pre post` (with `AccountsWF` boundary kernels) admits a
satisfying trace of `d` publishing the kernel's own `commitOf S pre post turn`". The shape is uniform
across all 21 value-leg effects (no per-effect trace/root prover data), the StarkComplete-class dual of
the soundness `StarkSound` extraction. `descriptorComplete_of_satFloor` then re-proves the per-effect
satisfiability rung `descriptorComplete` from `SatFloor` ALONE: the decode is CONSTRUCTED
(`stateDecode_construct`), the satisfiability is the carried floor, and the spec-determined prover data is
GONE (it is determined by the kernel move, the `<e>_rotatedEncodes_construct` family, not assumed).

This is the value-leg analog of the authority-leg `CapOpenTraceFloor` reduction
(`CircuitCompletenessAuthorityConstruct`): the fat carrier shrinks to the irreducible realizability, and
the kernel-determined data is constructed, not bundled.

## The honest accounting (what irreducibly remains)

`SatFloor` carries exactly `Satisfied2 hash d minit mfin maddrs t` (the descriptor's IR-v2 constraints
all evaluate to 0 on a concrete `VmTrace` + the chip/memory/map faithfulness) and `tracePublishedCommit t
= commitOf S pre post turn` (the trace publishes the kernel's own roots). By Stage 0, `Satisfied2` is PURE
constraint satisfaction over a concrete trace — there is NO FRI/polynomial/AIR-prover content inside it;
the FRI gap is the SEPARATE `StarkComplete` bridge. So `SatFloor` is the minimal legitimate "the honest
prover's run produces a satisfying trace publishing the kernel commitment" realizability — the dual of the
soundness `StarkSound` extraction, NOT the conclusion. The decode/commitment/non-vacuity are constructed
elsewhere.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. `Satisfied2` is CARRIED (the named floor),
not assumed as an axiom; `stateDecode_construct` is CONSTRUCTIVE. No `sorry`, no `native_decide`, no
`:= True`, no fresh axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitCompleteness

namespace Dregg2.Circuit.CircuitCompletenessSatFloor

open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.CircuitCompleteness (commitOf descriptorComplete stateDecode_construct)
open Dregg2.Circuit.StateCommit (AccountsWF)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 VmTrace Satisfied2)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false

/-! ## §1 — `SatFloor`: the UNIFORM descriptor-agnostic trace realizability (the StarkComplete dual).

The honest prover's run, REDUCED to ONLY what genuinely needs it: per kernel step, a memory boundary, a
concrete `VmTrace`, the `Satisfied2` of the live descriptor `d`, and the publication of the kernel's own
commitment. NONE of the per-effect spec-determined trace/root prover data is here — that is the
`<e>_rotatedEncodes_construct` the kernel move fixes, not a floor. The SAME shape for ALL value-leg
effects. -/

/-- **`SatFloor S hash d kstep` — the UNIFORM value-leg trace realizability (NAMED).** For every kernel
step `kstep pre post` (with `AccountsWF` boundary kernels), a memory boundary `(minit, mfin, maddrs)`, a
concrete `VmTrace t`, the `Satisfied2` of the live descriptor `d` over `t`, and the fact that `t`
publishes the kernel's own commitment `commitOf S pre post turn`. This is the StarkComplete-class floor
(the prover's actual satisfying trace) — the dual of the soundness `StarkSound` extraction, with
everything the kernel move determines (the commitment, the decode, the genuine effect) CONSTRUCTED
elsewhere, NOT bundled here. Descriptor-AGNOSTIC: one shape for every value-leg effect. -/
def SatFloor (S : CommitSurface) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (kstep : RecChainedState → RecChainedState → Prop) : Prop :=
  ∀ (pre post : RecChainedState) (turn : BoundaryTurn),
    kstep pre post → AccountsWF pre.kernel → AccountsWF post.kernel →
    ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 hash d minit mfin maddrs t ∧
      tracePublishedCommit t = commitOf S pre post turn

/-! ## §2 — `descriptorComplete_of_satFloor`: the per-effect rung from the UNIFORM floor.

The per-effect satisfiability rung `descriptorComplete`, re-proved from `SatFloor` ALONE — a strictly
leaner floor than the fat per-effect `buildWitness` (which carried the trace PLUS the spec-determined
trace/root prover). The commitment decode is CONSTRUCTED (`stateDecode_construct`); the satisfiability is
the carried floor; the spec-determined decode data is NOT needed to STATE satisfiability (it was the
SEPARATE non-vacuity tooth `<e>_descriptorComplete_genuine`). -/

/-- **`descriptorComplete_of_satFloor` — the per-effect satisfiability rung from the UNIFORM floor.**
Given the uniform `SatFloor S hash d kstep` (the prover's satisfying traces publishing the kernel
commitment), the per-effect `descriptorComplete S hash d kstep` follows: the decode is CONSTRUCTED
(`stateDecode_construct`), the ONLY carried realizability is `SatFloor`. This is every value-leg
`<e>_descriptorComplete` with the floor SHRUNK to the irreducible StarkComplete-class core — the
spec-determined trace/root prover the fat `buildWitness` bundled is GONE (it is determined by the kernel
move, not assumed). One theorem covers ALL value-leg effects. -/
theorem descriptorComplete_of_satFloor (S : CommitSurface) (hash : List ℤ → ℤ)
    (d : EffectVmDescriptor2) (kstep : RecChainedState → RecChainedState → Prop)
    (floor : SatFloor S hash d kstep) :
    descriptorComplete S hash d kstep := by
  intro _hCR pre post turn hstep hpreWF hpostWF
  obtain ⟨minit, mfin, maddrs, t, hsat, hpub⟩ := floor pre post turn hstep hpreWF hpostWF
  exact ⟨minit, mfin, maddrs, t, hsat, hpub, stateDecode_construct S pre post turn hpreWF hpostWF⟩

/-! ## §3 — axiom hygiene. -/

#assert_axioms descriptorComplete_of_satFloor

end Dregg2.Circuit.CircuitCompletenessSatFloor
