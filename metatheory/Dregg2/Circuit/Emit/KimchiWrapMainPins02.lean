/-
# Dregg2.Circuit.Emit.KimchiWrapMainPins02 — ⚑ the REALITY GATE (§12a): the transcript sponge of a REAL accepted proof, in the kernel

⚑ **ONE MODULE OF THE `KimchiWrapMain` SPLIT.** The namespace is unchanged
(`Dregg2.Circuit.Emit.KimchiWrapMain`), so nothing here is renamed and no consumer moves; the file
boundary exists only so a pin re-elaborates without the emitter's 5,000 lines of `def` behind it.
The in-file rule that keeps it stable is the step side's: **a `def` goes in `…Core`/`…Fixture`, a
pin goes in its section's `…PinsNN`.**

⚠ The `set_option` block below is VERBATIM `KimchiWrapMain`'s and must stay that way. `set_option`
does not cross an import, and `KimchiWrapFinalizeSpongeGate` shipped four proofs as `sorryAx` --
each still landing in the environment with the right statement -- because a split dropped it.

Pins only. Every `def` this section had is in `…Fixture`; the namespace-wide axiom pin is in the
`KimchiWrapMain` umbrella, which imports every one of these.

-/
import Dregg2.Circuit.Emit.KimchiWrapMainFixture

namespace Dregg2.Circuit.Emit.KimchiWrapMain
open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaPoseidonFq (fqParams rcsQ mdsQ)

set_option autoImplicit false
set_option maxRecDepth 100000
-- ⚠ §12/§14b reduce whole sponge trajectories IN THE KERNEL (`rfl`/`decide`), which is strictly
-- stronger than the `#guard`s they replace and correspondingly slower to elaborate.
set_option maxHeartbeats 4000000

/-! ## §12 — the in-CI PINS on the smoke instance (`#guard`, interpreter-reduced).

Nullary `def`s so the interpreter evaluates the chains ONCE. -/

/-! ### §12a — ⚑ **THE REALITY GATE: this file's sponge IS upstream's.**

`PastaPoseidonFq.fqPhase1` re-derives β, γ, α′, ζ′ and the phase-1 digest of a REAL Vesta-committed
kimchi proof that `kimchi::verifier::verify` ACCEPTS, from the verifier-index digest and the
commitments. If `runSpongeQ`'s state machine is upstream's, driving it on THAT tape reproduces THAT
tuple exactly — including where the permutations fall, since a single misplaced one changes every
value below it. This is a cross-source check on the transcript machinery itself, not on a value
this file chose. -/

/-- ⚑ **The four challenges and the digest of a REAL accepted proof, out of THIS file's emitter.**
Closed in the KERNEL, so this is strictly stronger than the `#guard`s it replaces
(`metatheory/docs/GUARD-DISCIPLINE.md`) and it is a term later work can cite. -/
theorem real_transcript_reproduces_the_accepted_proof :
    realChals.getD 0 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
    ∧ realChals.getD 1 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
    ∧ realChals.getD 2 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
    ∧ realChals.getD 3 0 = Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL
    ∧ realDigest = Dregg2.Circuit.Emit.PastaPoseidonFq.FQDIGEST := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem real_transcript_bends_on_one_absorbed_word :
    realBentChals.getD 0 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.BETA_N
    ∧ realBentChals.getD 1 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.GAMMA_N
    ∧ realBentChals.getD 2 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ALPHA_CHAL
    ∧ realBentChals.getD 3 0 ≠ Dregg2.Circuit.Emit.PastaPoseidonFq.ZETA_CHAL := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end Dregg2.Circuit.Emit.KimchiWrapMain
