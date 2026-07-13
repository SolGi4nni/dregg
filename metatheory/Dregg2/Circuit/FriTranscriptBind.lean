import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics

/-!
# Transcript-binding the OOD challenge ζ (survey finding #4)

The modeled `verifyAlgo` derives ONLY the FRI betas and query indices from the Challenger; the OOD
point ζ is read straight from the prover-supplied `proof.oodPoint` (`batchTablesCheck`,
FriVerifier.lean:655) and NEVER checked against the transcript. So in the model a malicious prover
chooses ζ freely — only the *carried* `FriLdtExtractV3` clause forbids the exceptional choice, and the
proved Schwartz–Zippel ε-bound (`OodSoundnessGame.oodNonExc_winProb_le`) is decorative because ζ isn't
a transcript squeeze.

The DEPLOYED p3 verifier does not do this: it observes the trace commitment and SQUEEZES ζ from the
duplex sponge. This file closes the modeling infidelity: `deriveOod` performs that squeeze, and
`verifyAlgoTB` = `verifyAlgo` AND `proof.oodPoint = deriveOod …`. Acceptance then FORCES ζ to be the
transcript-derived value — a prover can no longer choose it. This is the deterministic half of the FS
argument (ζ is a function of the transcript); the probabilistic half (the squeeze behaves as a uniform
sample, so ζ is non-exceptional except with ε ≤ deg/|F|) is the ROM soundness follow-on that now has a
transcript-bound ζ to reason about instead of a free field.
-/

namespace Dregg2.Circuit.FriTranscriptBind

open Dregg2.Circuit.FriVerifier

/-- **Derive the OOD point from the transcript.** Observe the trace commitment into the duplex sponge,
then squeeze one extension-field element — the challenge derivation the deployed p3 verifier performs.
Matches `oodPoint`'s singleton shape (`sampleExt … 1` yields a length-1 list). -/
def deriveOod {F : Type} [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (initState : List F) (traceCommit : List F) : List F :=
  (Challenger.sampleExt perm RATE 1
    (Challenger.observeList perm RATE (Challenger.init initState) traceCommit)).1

/-- **The transcript-binding check.** The prover's OOD point must EQUAL the transcript-derived one. -/
def oodTranscriptCheck {F : Type} [Inhabited F] [DecidableEq F] (perm : List F → List F) (RATE : Nat)
    (initState : List F) (proof : BatchProofData F) : Bool :=
  decide (proof.oodPoint = deriveOod perm RATE initState proof.traceCommit)

/-- **The transcript-bound verifier.** `verifyAlgo` AND the OOD point is transcript-derived — the
faithful model of the deployed verifier, closing the free-ζ gap. -/
def verifyAlgoTB {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  verifyAlgo perm RATE toNat params vk checks initState logN proof pub
    && oodTranscriptCheck perm RATE initState proof

/-- **`verifyAlgoTB` acceptance FORCES the OOD point transcript-bound.** ζ is no longer a free prover
choice: acceptance pins `proof.oodPoint` to `deriveOod` of the trace commitment. -/
theorem verifyAlgoTB_forces_ood_transcript_bound {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoTB perm RATE toNat params vk checks initState logN proof pub = true) :
    proof.oodPoint = deriveOod perm RATE initState proof.traceCommit := by
  unfold verifyAlgoTB at hacc
  simp only [Bool.and_eq_true] at hacc
  exact of_decide_eq_true hacc.2

/-- **`verifyAlgoTB` is a strengthening.** Whatever it accepts, `verifyAlgo` accepts — so every
existing `verifyAlgo`-soundness theorem transports to `verifyAlgoTB` unchanged. -/
theorem verifyAlgoTB_imp_verifyAlgo {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoTB perm RATE toNat params vk checks initState logN proof pub = true) :
    verifyAlgo perm RATE toNat params vk checks initState logN proof pub = true := by
  unfold verifyAlgoTB at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.1

/-- **The check is LOAD-BEARING (anti-forgery tooth).** A prover-chosen OOD point that differs from the
transcript-derived one is REJECTED — exactly the free-ζ forgery the plain verifier admitted. -/
theorem oodTranscriptCheck_rejects_free_ood {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (proof : BatchProofData F)
    (h : proof.oodPoint ≠ deriveOod perm RATE initState proof.traceCommit) :
    oodTranscriptCheck perm RATE initState proof = false := by
  unfold oodTranscriptCheck
  exact decide_eq_false h

/-- **Non-vacuity (positive): the honest transcript-derived OOD point PASSES.** When the prover supplies
exactly the derived ζ, the check accepts — so `verifyAlgoTB` is not vacuously false. -/
theorem oodTranscriptCheck_accepts_honest {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (proof : BatchProofData F)
    (h : proof.oodPoint = deriveOod perm RATE initState proof.traceCommit) :
    oodTranscriptCheck perm RATE initState proof = true := by
  unfold oodTranscriptCheck
  exact decide_eq_true h

#assert_axioms deriveOod
#assert_axioms verifyAlgoTB_forces_ood_transcript_bound
#assert_axioms verifyAlgoTB_imp_verifyAlgo
#assert_axioms oodTranscriptCheck_rejects_free_ood
#assert_axioms oodTranscriptCheck_accepts_honest

end Dregg2.Circuit.FriTranscriptBind
