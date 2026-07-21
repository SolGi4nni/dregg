/-
# `Dregg2.Circuit.FriWrapHonest` — the HONEST soundness statement for the DEPLOYED gnark wrap,
the vacuity CANARY welded to it, and the machine-checked refutation that no per-proof genuine
witness is extractable from the emitted object at all.

## The object this is about

`EmitVerifier.emitVerifier_wrap_sound` (`EmitVerifier.lean:342`) is the theorem the shipped gnark
verifier inherits. It takes `[carrier : FriLowDegreeSound …]` as an instance binder and concludes
`∃ w : GenuineWitness Fr, w.exists_ ∧ proof.exposedSegment = pub.segment` for a `gnarkDenote I`-
accepted proof. Wave 1 (`FriCarrierVacuity`) proved that carrier is `↔ True`
(`friLowDegreeSound_content_iff_true`), that it admits NO falsifier
(`friLowDegreeSound_has_no_falsifier`), and that the whole conclusion follows from acceptance
alone (`wrap_sound_needs_no_carrier`) — but wave 1 stated that GENERICALLY over an abstract
`gnark`+`GnarkRefines`, and never touched the emitted object `gnarkDenote I` itself. This file
does, ADDITIVELY (imports read-only, edits nothing).

## What is shipped here

**(a) THE HONEST DEPLOYED WRAP.** `emitVerifier_wrap_sound_honest` is `emitVerifier_wrap_sound`
with the vacuous `[FriLowDegreeSound]` binder and the `GenuineWitness` prefix STRIPPED: from a
`gnarkDenote I`-accepted proof it concludes exactly `proof.exposedSegment = pub.segment` — the
ONLY thing acceptance genuinely implies (it is the sixth `&&` of the emitted circuit).
`emitVerifier_wrap_needs_no_carrier` then reproduces the OLD conclusion verbatim with the carrier
binder DELETED, exhibiting that the deployed carrier discharges nothing.

**(b) WHY NO REAL PER-PROOF WITNESS EXISTS AT THE DEPLOYED OBJECT (refutes option b).**
`gnarkDenote_blind` proves the emitted circuit's verdict depends on the proof through
`exposedSegment` and NOTHING ELSE (its FRI leaves `bCanon/bFold/bMerkle/bBatch/bQPow` are
constants of the emitted inputs `I`, not of the proof — `EmitVerifier.lean:251`). Consequently
`emitVerifier_wrap_cannot_certify_fri_content`: the moment the emitted circuit accepts ANY proof
carrying FRI data, it also accepts that proof's GARBAGE TWIN — same segment, every FRI field
emptied — so even the WEAKEST genuine-content predicate `proof.friCommitments ≠ []` has a
`Falsifier` against `gnarkDenote I`. There is no witness predicate depending on the proof beyond
its segment that a wrap over the deployed object can soundly conclude. (This is not a modelling
artifact: the extractor lane's `FriColumnLogExtract` independently finds Merkle binding yields no
TOTAL committed column, `treeExtract … = none`.)

**(c) THE HONEST FRI FLOOR IS THE Q-BOUNDED ε BOUND, NOT A PER-PROOF EXTRACTION.**
`deployed_wrap_honest_floor` re-states, as the named residual of the honest wrap, wave 1's
`FriCarrierEpsilon.deployed_forgery_bound`: a `Q`-attempt adversary against the DEPLOYED
`sampleBits` sampler forges a `δ = 7/16` (unique-decoding radius) far word with probability at most
`Q·((9/16)+2^logN/|F|)^38`. That is adversary-quantified, carries an explicit `ε`, and is
REFUTABLE (`FriCarrierEpsilon.friQueryForgeryBound_false_without_defect` knocks it over at a wrong
`ε`). `deployed_wrap_ceiling` records the honest bit-ceiling: the bound exceeds `1` already at
`Q = 2^32` — **~31 bits, not the `3·38+16 = 130` the config claims.** This floor is a MEASURE over
the FS randomness; it is NOT a conclusion about any single `(proof, pub)` and the deployed emitted
object cannot deliver it per accepted proof (it is blind to that randomness — the sampling is baked
into `I` before the `(proof, pub)` interface).

**(d) THE VACUITY CANARY, PERMANENT + REUSABLE.** `NonVacuousCarrier acc C` is inhabited iff `C`
ships a `Falsifier` against `acc`. `old_carrier_fails_canary` proves the deployed
`FriLowDegreeSound` consequent CANNOT inhabit it (no falsifier, from wave 1). The honest deployed
carrier CAN (`honest_deployed_carrier_passes_canary`, given any accepting FRI-carrying proof).
`wrap_floor_trivial_instance_dichotomy` is the discharge-with-trivial-instance detector: the OLD
carrier is constructible at ARBITRARY parameters with no hypotheses (`friLowDegreeSoundTrivial`),
whereas the honest floor is NOT universally true (false at a concrete witness). If a future edit
ever makes the honest floor implied-by-its-own-antecedent, the falsifier term becomes unprovable
and this file stops compiling.

## Honest verdict (stated in the code, not narrated)

The honest per-proof deployed wrap (`emitVerifier_wrap_sound_honest`) is an HONEST PARTIAL: it
concludes segment-equality, which is genuinely all acceptance gives, with the vacuous carrier
removed. It is NOT itself refutable — because it asserts exactly a conjunct of the verifier, and
that is the point. The adversary-quantified, non-trivializable, refutable object is the SEPARATE
FRI floor `FriQueryForgeryBound` (~31 bits at deployed knobs), which the deployed emitted circuit
provably cannot deliver per accepted proof.

## Discipline
ADDITIVE. `FriVerifier`, `FriCarrierVacuity`, `FriCarrierEpsilon`, `EmitVerifier` are imported
read-only and untouched; wave-1/codex results are REUSED, not re-derived. No `sorry`, no fresh
`axiom`, no `native_decide`. `#assert_all_clean` over every keystone.
-/
import Dregg2.Circuit.FriCarrierEpsilon
import Dregg2.Circuit.Emit.GnarkVerifier.EmitVerifier
import Dregg2.Tactics
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.FriWrapHonest

open Finset
open Dregg2.Circuit.R1csFr (Fr)
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.Emit.GnarkVerifier
open Dregg2.Circuit.FriCarrierVacuity
  (Falsifier ImpliedByAcceptance falsifier_refutes_implied implied_has_no_falsifier
   friLowDegreeSoundTrivial friLowDegreeSound_has_no_falsifier verifyAlgo_imp_segment
   wrap_sound_conclusion_iff_segment)
open Dregg2.Circuit.FriCarrierEpsilon
  (FriQueryForgeryBound friQueryForgeryBound_false_without_defect deployed_forgery_bound
   deployed_bound_useless_at_2pow32)

/-! ## §1 — THE HONEST DEPLOYED WRAP (option a).

`emitVerifier_wrap_sound` (`EmitVerifier.lean:342`), with the vacuous `[FriLowDegreeSound]` binder
and the `GenuineWitness` prefix removed. -/

/-- **⚑ THE HONEST DEPLOYED WRAP.** From a `gnarkDenote I`-accepted proof — the exact antecedent of
`emitVerifier_wrap_sound` — the ONLY sound conclusion is `proof.exposedSegment = pub.segment`, the
sixth `&&` of the emitted circuit. No `[FriLowDegreeSound]` carrier, no `GenuineWitness` hole. -/
theorem emitVerifier_wrap_sound_honest (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr)
    (haccept : gnarkDenote I proof pub = true) :
    proof.exposedSegment = pub.segment := by
  simp only [gnarkDenote, segmentTooth, Bool.and_eq_true, decide_eq_true_eq] at haccept
  exact haccept.2

/-- **⚑ THE DEPLOYED WRAP NEEDS NO CARRIER.** The FULL conclusion of `emitVerifier_wrap_sound`
(`∃ w : GenuineWitness Fr, w.exists_ ∧ …`), reproduced verbatim from acceptance alone with the
`[FriLowDegreeSound]` instance binder DELETED. The deployed carrier discharges nothing:
`GenuineWitness` is inhabited by `⟨True⟩` and the segment conjunct is acceptance's own. -/
theorem emitVerifier_wrap_needs_no_carrier (I : Inputs) (proof : BatchProofData Fr)
    (pub : WrapPublics Fr) (haccept : gnarkDenote I proof pub = true) :
    ∃ w : GenuineWitness Fr, w.exists_ ∧ proof.exposedSegment = pub.segment :=
  ⟨⟨True⟩, trivial, emitVerifier_wrap_sound_honest I proof pub haccept⟩

/-- The old conclusion adds nothing over the honest one: the `GenuineWitness` existential is
EQUIVALENT to the bare segment equality (wave 1's `wrap_sound_conclusion_iff_segment`). So
`emitVerifier_wrap_sound_honest` LOSES nothing real relative to `emitVerifier_wrap_sound` — it only
drops the vacuous dressing. -/
theorem honest_wrap_loses_nothing (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    (∃ w : GenuineWitness Fr, w.exists_ ∧ proof.exposedSegment = pub.segment)
      ↔ proof.exposedSegment = pub.segment :=
  wrap_sound_conclusion_iff_segment proof pub

/-! ## §2 — ⚑ WHY NO PER-PROOF GENUINE WITNESS EXISTS AT THE DEPLOYED OBJECT (refutes option b).

The emitted circuit's FRI leaves are constants of `I`, not of `proof` (`EmitVerifier.lean:251`), so
`gnarkDenote I proof pub` depends on `proof` ONLY through `segmentTooth`. -/

/-- **⚑ THE DEPLOYED CIRCUIT IS BLIND.** `gnarkDenote I` cannot distinguish two proofs with the same
exposed segment — its five FRI/canonicity leaves are `bCanon I … bQPow I`, none of which reads the
proof. Instantiates wave 1's `verifyAlgo_blind_to_proof_of_constant_checks` at the ACTUAL emitted
verdicts. -/
theorem gnarkDenote_blind (I : Inputs) (p₁ p₂ : BatchProofData Fr) (pub : WrapPublics Fr)
    (hseg : p₁.exposedSegment = p₂.exposedSegment) :
    gnarkDenote I p₁ pub = gnarkDenote I p₂ pub := by
  unfold gnarkDenote segmentTooth
  rw [hseg]

/-- The garbage twin of a proof: same exposed segment, every FRI-bearing field emptied — no trace
commitment, no fold commitments, no final poly, no query openings. -/
def garbageTwin (p : BatchProofData Fr) : BatchProofData Fr :=
  { p with traceCommit := [], friCommitments := [], finalPoly := [], queries := [] }

theorem garbageTwin_seg (p : BatchProofData Fr) :
    (garbageTwin p).exposedSegment = p.exposedSegment := rfl

theorem garbageTwin_no_fri (p : BatchProofData Fr) :
    (garbageTwin p).friCommitments = [] := rfl

/-- **⚑⚑ THE DEPLOYED WRAP CANNOT CERTIFY ANY FRI CONTENT.** Whenever `gnarkDenote I` accepts a
proof `p` (carrying real FRI commitments or not), it ALSO accepts `p`'s garbage twin — same segment,
all FRI data stripped. So even the weakest genuine-content predicate, "`friCommitments ≠ []`", has a
`Falsifier` against `gnarkDenote I`: an accepted instance where it fails. A wrap over the deployed
emitted object therefore CANNOT soundly conclude that an accepted proof carries so much as one FRI
commitment — the option-(b) "real witness tied to the committed word" is unreachable HERE, at the
object the gnark verifier inherits, not merely unproven. -/
theorem emitVerifier_wrap_cannot_certify_fri_content
    (I : Inputs) (p : BatchProofData Fr) (pub : WrapPublics Fr)
    (haccept : gnarkDenote I p pub = true) :
    Falsifier (gnarkDenote I) (fun (q : BatchProofData Fr) (_ : WrapPublics Fr) => q.friCommitments ≠ []) := by
  refine ⟨garbageTwin p, pub, ?_, ?_⟩
  · show gnarkDenote I (garbageTwin p) pub = true
    rw [← gnarkDenote_blind I p (garbageTwin p) pub (garbageTwin_seg p).symm]
    exact haccept
  · show ¬ ((garbageTwin p).friCommitments ≠ [])
    rw [garbageTwin_no_fri]; exact fun h => h rfl

/-- The corollary in canary form: "the accepted proof carries FRI content" is NOT
implied-by-acceptance for the deployed object, given any accepting FRI proof. -/
theorem fri_content_not_implied_by_acceptance
    (I : Inputs) (p : BatchProofData Fr) (pub : WrapPublics Fr)
    (haccept : gnarkDenote I p pub = true) :
    ¬ ImpliedByAcceptance (gnarkDenote I)
        (fun (q : BatchProofData Fr) (_ : WrapPublics Fr) => q.friCommitments ≠ []) :=
  falsifier_refutes_implied _ _ (emitVerifier_wrap_cannot_certify_fri_content I p pub haccept)

/-! ## §3 — THE HONEST FRI FLOOR: Q-BOUNDED, EXPLICIT ε, REFUTABLE, ~31-BIT CEILING.

The soundness the wrap actually rests on is a MEASURE over the FS query randomness — wave 1's
`FriCarrierEpsilon.deployed_forgery_bound` — not a per-proof extraction. Re-stated here as the
honest wrap's named residual. -/

/-- **⚑ THE HONEST FLOOR FOR THE DEPLOYED WRAP.** At the shipped BabyBear field `|F| = 2013265921`,
`k = 38` queries, `2^logN` buckets, and the unique-decoding radius `δ = 7/16` (the ONLY radius the
tree proves), a `Q`-attempt adversary against the DEPLOYED `sampleBits` sampler forges a far word
with probability at most `Q·((9/16)+2^logN/|F|)^38`. Adversary-quantified, explicit `ε`. Composed
from `FriCarrierEpsilon.deployed_forgery_bound` (the `Q`-attempt Bernoulli union bound over codex's
deployed-sampler defect bound). -/
theorem deployed_wrap_honest_floor (logN Q : ℕ) (Emiss : Finset ℕ)
    (hE : Emiss.card ≤ 2 ^ logN)
    (hmiss : (Emiss.card : ℝ) / ((2 : ℕ) ^ logN : ℕ) ≤ 1 - (7 / 16 : ℝ)) :
    FriQueryForgeryBound 2013265921 (2 ^ logN) 38 Q Emiss
      ((Q : ℝ) * ((9 / 16 : ℝ) + ((2 ^ logN : ℕ) : ℝ) / (2013265921 : ℝ)) ^ 38) :=
  deployed_forgery_bound logN Q Emiss hE hmiss

/-- **⚑ THE HONEST CEILING.** The floor's un-biased base `(9/16)^38` exceeds `2^-32`, so at
`Q = 2^32` attempts the bound exceeds `1` and asserts nothing: **~31 bits**, against the config's
claimed `3·38+16 = 130`. (`FriCarrierEpsilon.deployed_bound_useless_at_2pow32`.) -/
theorem deployed_wrap_ceiling : (1 : ℝ) < ((2 : ℝ) ^ 32) * ((9 / 16 : ℝ)) ^ 38 :=
  deployed_bound_useless_at_2pow32

/-- **⚑ THE HONEST FLOOR IS REFUTABLE.** At `N=3, m=2, k=1, Q=1, δ=1/2` the un-defected value
`Q·(1−δ)^k = 1/2` does NOT bound the true forgery fraction `2/3`, so `FriQueryForgeryBound` is
FALSE there. A wrong `ε` knocks it over — the falsifier `FriLowDegreeSound` provably could not have
(`friLowDegreeSound_has_no_falsifier`). Re-exported so it sits beside the deployed wrap.
(`FriCarrierEpsilon.friQueryForgeryBound_false_without_defect`.) -/
theorem deployed_wrap_floor_refutable :
    ¬ FriQueryForgeryBound 3 2 1 1 ({0} : Finset ℕ) ((1 : ℝ) * (1 - (1 / 2 : ℝ)) ^ 1) :=
  friQueryForgeryBound_false_without_defect

/-! ## §4 — ⚑ THE VACUITY CANARY, welded to the deployed wrap (permanent + reusable). -/

/-- **THE CANARY TYPE.** A carrier `C` over acceptance `acc` PASSES iff it ships a `Falsifier` — an
accepted instance at which `C` fails. Ship a `NonVacuousCarrier acc C` term beside any wrap carrier;
if the carrier is ever weakened until acceptance implies it, `implied_has_no_falsifier` makes the
`falsifier` field unprovable and the term stops compiling. -/
structure NonVacuousCarrier {P U : Type} (acc : P → U → Bool) (C : P → U → Prop) : Prop where
  falsifier : Falsifier acc C

/-- **⚑ THE OLD DEPLOYED CARRIER FAILS THE CANARY.** `FriLowDegreeSound`'s consequent admits no
falsifier at any parameters (wave 1), so it CANNOT inhabit `NonVacuousCarrier` — the machine-checked
statement that the binder `emitVerifier_wrap_sound` carries is vacuous. -/
theorem old_carrier_fails_canary {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat)
    (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
    (initState : List F) (logN : Nat) :
    ¬ NonVacuousCarrier
        (fun proof pub => verifyAlgo perm RATE toNat params vk checks initState logN proof pub)
        (fun proof pub => ∃ w : GenuineWitness F, w.exists_ ∧ proof.exposedSegment = pub.segment) := by
  rintro ⟨hf⟩
  exact friLowDegreeSound_has_no_falsifier perm RATE toNat params vk checks initState logN hf

/-- **⚑ THE HONEST DEPLOYED CARRIER PASSES THE CANARY.** Given any FRI-carrying proof the emitted
circuit accepts, the "carries FRI content" predicate ships a falsifier against `gnarkDenote I` — the
positive side of the canary, contrasting `old_carrier_fails_canary`. -/
theorem honest_deployed_carrier_passes_canary
    (I : Inputs) (p : BatchProofData Fr) (pub : WrapPublics Fr)
    (haccept : gnarkDenote I p pub = true) :
    NonVacuousCarrier (gnarkDenote I)
      (fun (q : BatchProofData Fr) (_ : WrapPublics Fr) => q.friCommitments ≠ []) :=
  ⟨emitVerifier_wrap_cannot_certify_fri_content I p pub haccept⟩

/-- **⚑⚑ THE DISCHARGE-WITH-TRIVIAL-INSTANCE DETECTOR.** The two facts side by side:

  * LEFT — the OLD carrier `FriLowDegreeSound` is `Nonempty` at ARBITRARY parameters with NO
    hypotheses (`friLowDegreeSoundTrivial`). That is the smell: an instance binder every
    `[carrier : FriLowDegreeSound …]` in the tree resolves to for free.
  * RIGHT — the honest floor is NOT universally true: `FriQueryForgeryBound` is FALSE at a concrete
    parameter setting, so no trivial/universal instance of it can exist.

If a future edit ever collapses the honest floor into a universally-true (trivially dischargeable)
carrier, the RIGHT conjunct becomes unprovable and this theorem stops compiling. -/
theorem wrap_floor_trivial_instance_dichotomy :
    (∀ {F : Type} [Inhabited F] [DecidableEq F] (perm : List F → List F) (RATE : Nat)
        (toNat : F → Nat) (params : FriParams) (vk : RecursionVk F) (checks : FriChecks F)
        (initState : List F) (logN : Nat),
        Nonempty (FriLowDegreeSound perm RATE toNat params vk checks initState logN))
      ∧ ¬ (∀ (N m k Q : ℕ) (Emiss : Finset ℕ) (ε : ℝ), FriQueryForgeryBound N m k Q Emiss ε) := by
  refine ⟨?_, ?_⟩
  · intro F _ _ perm RATE toNat params vk checks initState logN
    exact ⟨friLowDegreeSoundTrivial perm RATE toNat params vk checks initState logN⟩
  · intro hall
    exact friQueryForgeryBound_false_without_defect
      (hall 3 2 1 1 ({0} : Finset ℕ) ((1 : ℝ) * (1 - (1 / 2 : ℝ)) ^ 1))

#assert_all_clean [
  emitVerifier_wrap_sound_honest,
  emitVerifier_wrap_needs_no_carrier,
  honest_wrap_loses_nothing,
  gnarkDenote_blind,
  garbageTwin_seg,
  garbageTwin_no_fri,
  emitVerifier_wrap_cannot_certify_fri_content,
  fri_content_not_implied_by_acceptance,
  deployed_wrap_honest_floor,
  deployed_wrap_ceiling,
  deployed_wrap_floor_refutable,
  old_carrier_fails_canary,
  honest_deployed_carrier_passes_canary,
  wrap_floor_trivial_instance_dichotomy
]

end Dregg2.Circuit.FriWrapHonest
