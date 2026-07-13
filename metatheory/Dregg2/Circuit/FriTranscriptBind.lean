import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics

/-!
# Transcript-binding the OOD challenge ζ (survey finding #4), faithful to the deployed p3 order

The modeled `verifyAlgo` derives ONLY the FRI betas and query indices from the Challenger; the OOD
point ζ is read straight from the prover-supplied `proof.oodPoint` (`batchTablesCheck`,
FriVerifier.lean:655) and NEVER checked against the transcript. So in the model a malicious prover
chooses ζ freely, and the proved Schwartz–Zippel ε-bound is decorative.

## The deployed transcript order (READ from the deployed verifier)

`circuit-prove` calls `p3_uni_stark::verify` (plonky3 @82cfad7, `uni-stark/src/verifier.rs`). Its
challenger sequence around ζ is, verbatim (ZK is OFF at deployment, so the random-commitment branch is
inert):

```
observe(degree_bits); observe(base_degree_bits); observe(preprocessed_width);   -- 361-363
observe(commitments.trace);                                                     -- 369
observe_slice(public_values);                                                   -- 373
let alpha = challenger.sample_algebra_element();   -- Λ, the constraint RLC challenge  -- 379
observe(commitments.quotient_chunks);                                           -- 380
let zeta  = challenger.sample_algebra_element();   -- ζ, the OOD point           -- 390
```

FINDING: BOTH ζ and α(=Λ) are transcript-derived in the DEPLOYED verifier. The survey's "Λ appears
nowhere in verifyAlgo" was true of the MODEL, not the deployment.

## What `deriveOod` models — now the FULL squeeze sequence

`deriveOod` replicates the deployed sequence TERM-FOR-TERM: `observe(trace); observe(public);
sample α; observe(quotient_chunks); squeeze ζ`. The α RLC-challenge squeeze and the quotient-chunks
observation between the public values and ζ — previously an abstraction gap — are now MODELED: the
`quotientCommit` field was added to `BatchProofData` for exactly this, and α's sponge advance is threaded
(its value discarded, only its effect on the challenger state kept). So `deriveOod` squeezes ζ at the
SAME challenger state the deployed verifier does; an honest deployed proof (whose `oodPoint` is that
deployed ζ) PASSES `oodTranscriptCheck`, so the deployed `verifyBatch → verifyAlgoTB` swap is FAITHFUL
(it does not reject honest proofs), not merely additive.

Residual abstraction, named honestly (the standing model↔deployment correspondence, validated by the KAT
corpus): (i) the `degree_bits`/`base_degree_bits`/`preprocessed_width` preamble (public constants absorbed
before the trace); (ii) the base-field vs extension-field representation — the whole model is a base-field
FRI abstraction of p3's extension-field challenges (α/ζ squeezed as base-field lanes here, matching the
model's base-field `oodPoint`). The probabilistic half (the squeeze is a uniform draw ⇒ ζ non-exceptional
except ε ≤ dN/|F|, the verifier's own "Soundness Error: dN/|EF|") is `OodRomBound`, over this ζ.
-/

namespace Dregg2.Circuit.FriTranscriptBind

open Dregg2.Circuit.FriVerifier

/-- **Derive the OOD point — the EXACT deployed p3 squeeze.** Replicates the verifier's challenger
sequence around ζ, faithfully (`uni-stark/src/verifier.rs`): observe the trace commitment, observe the
public values, SAMPLE the constraint RLC challenge `α` (Λ — advancing the sponge, its value discarded
here), observe the quotient-chunks commitment, then squeeze ζ. Because α is sampled BETWEEN the
observations, this cannot be folded into one prefix — the `quotientCommit` field (added to
`BatchProofData` for exactly this) and `extDeg` (the α squeeze width) are threaded. So for an honest
deployed proof — whose `oodPoint` IS the deployed ζ and whose trace/public/quotient are the deployed
commitments — `deriveOod = proof.oodPoint`, i.e. the honest proof PASSES, and a prover who chose ζ
freely does not. -/
def deriveOod {F : Type} [Inhabited F] (perm : List F → List F) (RATE extDeg : Nat)
    (initState : List F) (proof : BatchProofData F) (pub : WrapPublics F) : List F :=
  let c := Challenger.observeList perm RATE (Challenger.init initState) proof.traceCommit
  let c := Challenger.observeList perm RATE c pub.segment
  let c := (Challenger.sampleExt perm RATE extDeg c).2          -- sample α (Λ), keep the challenger
  let c := Challenger.observeList perm RATE c proof.quotientCommit
  (Challenger.sampleExt perm RATE 1 c).1                         -- squeeze ζ

/-- **The transcript-binding check.** The prover's OOD point must EQUAL the exact transcript-derived ζ. -/
def oodTranscriptCheck {F : Type} [Inhabited F] [DecidableEq F] (perm : List F → List F)
    (RATE extDeg : Nat) (initState : List F) (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  decide (proof.oodPoint = deriveOod perm RATE extDeg initState proof pub)

/-- **The transcript-bound verifier.** `verifyAlgo` AND the OOD point is transcript-derived — the
faithful model of the deployed verifier, closing the free-ζ gap. -/
def verifyAlgoTB {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F) : Bool :=
  verifyAlgo perm RATE toNat params vk checks initState logN proof pub
    && oodTranscriptCheck perm RATE params.extDeg initState proof pub

/-- **`verifyAlgoTB` acceptance FORCES the OOD point transcript-bound.** ζ is no longer a free prover
choice: acceptance pins `proof.oodPoint` to `deriveOod` of the trace commitment and public values. -/
theorem verifyAlgoTB_forces_ood_transcript_bound {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoTB perm RATE toNat params vk checks initState logN proof pub = true) :
    proof.oodPoint = deriveOod perm RATE params.extDeg initState proof pub := by
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
    (perm : List F → List F) (RATE extDeg : Nat) (initState : List F) (proof : BatchProofData F)
    (pub : WrapPublics F)
    (h : proof.oodPoint ≠ deriveOod perm RATE extDeg initState proof pub) :
    oodTranscriptCheck perm RATE extDeg initState proof pub = false := by
  unfold oodTranscriptCheck
  exact decide_eq_false h

/-- **Non-vacuity (positive): the honest transcript-derived OOD point PASSES.** -/
theorem oodTranscriptCheck_accepts_honest {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE extDeg : Nat) (initState : List F) (proof : BatchProofData F)
    (pub : WrapPublics F)
    (h : proof.oodPoint = deriveOod perm RATE extDeg initState proof pub) :
    oodTranscriptCheck perm RATE extDeg initState proof pub = true := by
  unfold oodTranscriptCheck
  exact decide_eq_true h

#assert_axioms deriveOod
#assert_axioms verifyAlgoTB_forces_ood_transcript_bound
#assert_axioms verifyAlgoTB_imp_verifyAlgo
#assert_axioms oodTranscriptCheck_rejects_free_ood
#assert_axioms oodTranscriptCheck_accepts_honest

end Dregg2.Circuit.FriTranscriptBind
