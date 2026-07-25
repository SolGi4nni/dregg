/-
# `Dregg2.Circuit.RlcRomBound` — the SECOND Fiat–Shamir conjunct of the deployed extraction
bundle (the constraint-RLC challenge Λ), as a genuinely adversary-quantified bound.

## What was missing

`AlgoStarkSoundTransferV3.FriLdtExtractV3` carries TWO Fiat–Shamir non-exceptionality clauses:

  * ζ (`:157`) — DISCHARGED as a bounded-advantage event by
    `OodRomBound.ood_nonexceptionality_is_bounded`: over an ARBITRARY adaptive prover strategy
    `proofOf : Ω → BatchProofData F`, `winProb (accept ∧ ζ exceptional) ≤ deg R / |F|`.
  * Λ (`:155`) — NOT discharged. `rlc_lambda_is_bounded_fs_form` (`:295`) exhibits only the
    CARDINALITY fact `#(exceptionalSet (batchResidual …)) < #constraints`. There is no acceptance
    event in it, no prover, and no probability: it says the bad set is small, never that a prover
    running against the DEPLOYED verifier lands in it rarely.

This file supplies the missing half, on the ζ recipe exactly: deterministic forcing + uniform
transport + the combinatorial cap.

## The three ingredients (all already proven in-tree)

  1. **Forcing.** `FriChallengerUnified.verifyAlgoUnifiedFaithful_forces_challenges` (`:196`):
     faithful acceptance forces `singleAirChallengesBound`, i.e. EVERY opened single-AIR instance's
     `alpha` field equals `(deriveTranscript …).constraintAlpha.headD` — the prover cannot declare
     an RLC challenge of its choosing. (`verifyAlgoUnifiedFaithfulExt`, the predicate the apex's
     `verifyBatch` runs, strengthens this, so §4 lands the same bound on the deployed verifier.)
  2. **Transport.** `OodRomBound.RomUniform` / `transcriptBound_ood_escape_le`: under the named ROM
     idealization of the sponge squeeze, the induced distribution of the squeezed challenge IS
     uniform, and the Schwartz–Zippel game bound applies to it.
  3. **Cap.** `OodSoundnessGame.batchResidual_natDegree_lt` / `_exceptionalSet_card_lt`: the RLC
     batching polynomial has degree `< #constraints`.

## What is PROVED here

  * `rlc_lambda_nonexceptionality_is_bounded` — for ANY adaptive prover `proofOf : Ω → BatchProofData F`,
    under `RomUniformAlpha`, `winProb (verifyAlgoUnifiedFaithful ACCEPTS ∧ the declared RLC challenge
    is exceptional for R) ≤ natDegree R / |F|`.
  * `rlc_lambda_nonexceptionality_is_bounded_ext` — the same at
    `ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, i.e. at the verifier `CircuitSoundness.verifyBatch`
    actually evaluates.
  * `rlc_lambda_bounded_babybear` / `hLam_clause_bounded_babybear` — the deployed instances: at the
    batching polynomial of a residual family the error is `≤ (n−1)/2013265921`, and at
    `Rfam transferV3` it is the `FriLdtExtractV3` Λ-clause itself, bounded by
    `(#(arithList transferV3) − 1)/2013265921`.

## SCOPE — what the bounded event is, stated at its real resolution

The event is about the prover's DECLARED challenge (the `alpha` field of the opened single-AIR
instances), exactly as `OodRomBound`'s ζ bound is about the proof's declared `oodPoint.headI`.
`FriLdtExtractV3`'s Λ is an EXISTENTIALLY quantified `BabyBear` produced by the extraction, and the
bundle does not itself equate it to the declared field — it does not for ζ either (`ood : ℤ` and
`ζ : BabyBear` are separate binders there). Tying the extracted Λ to the declared α is the same
unmodeled-plumbing wire the column-layout clause names, and it is NOT closed here. What IS closed is
the half that was entirely missing: the challenge a DEPLOYED-accepting prover can get away with
declaring is transcript-forced, and lands exceptional only with probability `≤ deg/|F|`.

## THE FALSIFIER (§6) — the forcing is load-bearing, not decorative

The identical statement with `verifyAlgoUnifiedFaithful` replaced by BARE `verifyAlgo` is FALSE, and
the counterexample is exhibited, not argued: one prover strategy `attackProof : ZMod 7 → BatchProofData`
over the REAL `deriveTranscript`, for which

  * `RomUniformAlpha` HOLDS (the transcript α is literally the sampled ω — `attack_alpha_is_id`), so
    the hypothesis is satisfied, not dodged;
  * bare `verifyAlgo` ACCEPTS every ω (it never reads `singleAirOpenings` — `fullChecks.batchTables`
    is `batchTablesCheck`, which walks `tableOpenings` only), and the strategy declares the constant
    exceptional challenge `alpha := 0`, so the joint event has probability **1**, exceeding the claimed
    `natDegree X / 7 = 1/7`;
  * the SAME strategy against `verifyAlgoUnifiedFaithful` is accepted ONLY at `ω = 0` — precisely
    because the α-binding tooth rejects the free challenge — so there the joint event has probability
    exactly `1/7`, TIGHT against the bound.

One family, two verifiers, `1` versus `1/7` (`forcing_is_load_bearing`): the difference is the forcing
lemma. That it is the forcing and not some incidental arithmetic failure is itself pinned —
`fixture_arithmetic_teeth_pass` shows the fixture's degree/vanishing/inverse/quotient teeth all HOLD
for every `ω ≠ 1` whatever challenge is declared, so on `ω ∈ {2,…,6}` the α binding is the only tooth
that can reject. And the bound is not tight only where an attacker degenerates: the HONEST strategy
(identical except that it declares the transcript's own challenge) is ACCEPTED on six of the seven
runs and its joint event is still exactly `1/7` (`rlc_lambda_bound_fires_and_is_tight`).

## Residual

`RomUniformAlpha` — the ROM idealization of the Poseidon2 duplex squeeze that produces α, the exact
analogue of `OodRomBound.RomUniformDerive` for ζ, and satisfiable/refutable by the same argument
(`romUniform_of_bijective` / `not_romUniform_const`, both re-used here at the real transcript).
Everything else — forcing, transport, the degree cap, the composition — is proved.
-/
import Dregg2.Circuit.OodRomBound
import Dregg2.Circuit.AlgoStarkSoundTransferV3
import Dregg2.Circuit.ExtFieldChallenge

namespace Dregg2.Circuit.RlcRomBound

open Polynomial
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodSoundnessGame
  (oodNonExcAcc oodNonExc_winProb_le batchResidual batchResidual_natDegree_lt
   batchResidual_exceptionalSet_card_lt babybear_card)
open Dregg2.Circuit.OodRomBound
  (RomUniform romUniform_id romUniform_of_bijective not_romUniform_const winProb_mono
   transcriptBound_ood_escape_le)
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith fullChecks)
open Dregg2.Circuit.BatchTablesSingleAir (SingleAirOpening)
open Dregg2.Circuit.FriChallengerUnified
  (verifyAlgoUnifiedFaithful singleAirChallengesBound verifyAlgoUnifiedFaithful_forces_challenges)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt
   verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful)

/-! ## §1 — the transcript-derived RLC challenge, and its ROM idealization. -/

/-- **The transcript-derived constraint-RLC challenge Λ**, as a base-field scalar: the head lane of
the ONE continued transcript's `constraintAlpha` squeeze. This is EXACTLY the value
`FriChallengerUnified.singleAirChallengesBound` pins every opened instance's `alpha` field to, so it
is the object the deployed verifier's α-binding tooth is about. -/
def transcriptAlpha {F : Type} [Inhabited F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F) : F :=
  (Dregg2.Circuit.FriChallengerUnified.deriveTranscript
    perm RATE toNat params initState logN proof pub).constraintAlpha.headD default

/-- **`RomUniformAlpha` — the named residual AT THE REAL α SQUEEZE.** `OodRomBound.RomUniform`
instantiated with `ζmap ω = transcriptAlpha … (proofOf ω) pub`: over the finite sampled-transcript
space `Ω` (the adaptive prover strategy `proofOf` mapping each freshly sampled commitment/randomness
to the submitted proof data), the ACTUAL continued-challenger α squeeze induces the uniform
distribution on `F`. This is the standard ROM idealization for the deployed Poseidon2-w16 permutation
— the exact analogue of `OodRomBound.RomUniformDerive` for ζ, named and visible, never an axiom. It
genuinely discriminates: satisfiable at a bijective squeeze (`romUniformAlpha_attack_holds` runs the
REAL `deriveTranscript`), refutable at a degenerate one (`not_romUniform_const`). -/
def RomUniformAlpha {F : Type} [Inhabited F] [Fintype F] {Ω : Type} [Fintype Ω]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat)
    (proofOf : Ω → BatchProofData F) (pub : WrapPublics F) : Prop :=
  RomUniform (fun ω => transcriptAlpha perm RATE toNat params initState logN (proofOf ω) pub)

/-- The escape bound at the real α squeeze: under `RomUniformAlpha`, the transcript-derived RLC
challenge lands in `exceptionalSet R` with probability `≤ natDegree R / |F|`. One rewrite across the
distribution equality onto the already-proved Schwartz–Zippel game bound. -/
theorem alphaEscape_le {F : Type} [Inhabited F] [Fintype F] [CommRing F] [IsDomain F] [DecidableEq F]
    {Ω : Type} [Fintype Ω]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (initState : List F) (logN : Nat)
    (proofOf : Ω → BatchProofData F) (pub : WrapPublics F)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    (R : Polynomial F) :
    winProb (fun ω =>
        oodNonExcAcc R (transcriptAlpha perm RATE toNat params initState logN (proofOf ω) pub))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) :=
  transcriptBound_ood_escape_le _ hrom R

/-! ## §2 — the event, and the FORCING bridge. -/

/-- **The prover's DECLARED RLC challenge is exceptional.** The escape event at Λ: some opened
single-AIR instance declares a constraint-RLC challenge lying in `exceptionalSet R` — exactly the
configuration `OodSoundnessGame.rlc_debatch`'s `hnonexc` precondition (and hence the
`FriLdtExtractV3` Λ-clause) rules out. Stated over the PROVER's own `alpha` fields, so it is an
observable of the submitted proof, not of the verifier's internals. -/
noncomputable def declaredAlphaExceptional {F : Type} [CommRing F] [IsDomain F] [DecidableEq F]
    (R : Polynomial F) (proof : BatchProofData F) : Bool :=
  proof.singleAirOpenings.any fun o => decide (o.alpha ∈ exceptionalSet R)

/-- **THE FORCING, read off.** On a `verifyAlgoUnifiedFaithful`-accepting run, EVERY opened
single-AIR instance's declared `alpha` IS the transcript-derived RLC challenge. Pure consequence of
the landed `verifyAlgoUnifiedFaithful_forces_challenges`; this is the step the bare `verifyAlgo` does
NOT provide (see §6). -/
theorem forced_alpha_of_faithful {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (hacc : verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN proof pub
      = true)
    (o : SingleAirOpening F) (ho : o ∈ proof.singleAirOpenings) :
    o.alpha = transcriptAlpha perm RATE toNat params initState logN proof pub := by
  have h := verifyAlgoUnifiedFaithful_forces_challenges perm RATE toNat params vk core A
    initState logN proof pub hacc
  unfold singleAirChallengesBound at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have ho' := h.2 o ho
  simp only [decide_eq_true_eq] at ho'
  exact ho'.1

/-! ## §3 — THE PAYOFF at the faithful verifier. -/

/-- **`rlc_lambda_nonexceptionality_is_bounded` — the Λ conjunct as a bounded-advantage event.**

For ANY adaptive prover strategy `proofOf : Ω → BatchProofData F` (the ROM variable: each sampled
transcript randomness `ω` yields the submitted proof data), under the named `RomUniformAlpha`: the
probability that `verifyAlgoUnifiedFaithful` ACCEPTS **and** the proof's declared constraint-RLC
challenge lies in `exceptionalSet R` is at most `natDegree R / |F|`.

The composition is genuine, on the `ood_nonexceptionality_is_bounded` recipe:
`verifyAlgoUnifiedFaithful_forces_challenges` pins the accepted proof's declared α to the ACTUAL
continued-transcript squeeze (§2), and the `RomUniform` transport (§1) bounds that squeeze's escape
probability. The `FriLdtExtractV3` clause `Λ ∉ exceptionalSet (batchResidual …)` is thereby a
bounded-advantage event under transcript-binding + `RomUniformAlpha`, no longer a free prover choice.

The forcing is LOAD-BEARING: §6 exhibits a strategy for which this statement is FALSE at bare
`verifyAlgo`. -/
theorem rlc_lambda_nonexceptionality_is_bounded {Ω F : Type} [Fintype Ω] [Fintype F] [Inhabited F]
    [CommRing F] [IsDomain F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (initState : List F) (logN : Nat)
    (pub : WrapPublics F) (proofOf : Ω → BatchProofData F)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    (R : Polynomial F) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional R (proofOf ω))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans
    (winProb_mono
      (w2 := fun ω =>
        oodNonExcAcc R (transcriptAlpha perm RATE toNat params initState logN (proofOf ω) pub)) ?_)
    (alphaEscape_le perm RATE toNat params initState logN proofOf pub hrom R)
  intro ω hω
  rw [Bool.and_eq_true] at hω
  obtain ⟨hacc, hexc⟩ := hω
  unfold declaredAlphaExceptional at hexc
  rw [List.any_eq_true] at hexc
  obtain ⟨o, ho, hoexc⟩ := hexc
  have halpha := forced_alpha_of_faithful perm RATE toNat params vk core A initState logN
    (proofOf ω) pub hacc o ho
  show oodNonExcAcc R (transcriptAlpha perm RATE toNat params initState logN (proofOf ω) pub) = true
  unfold oodNonExcAcc
  rw [← halpha]
  exact hoexc

/-! ## §4 — the same bound at the verifier the APEX RUNS (`verifyBatch`'s predicate). -/

/-- **`rlc_lambda_nonexceptionality_is_bounded_ext` — the Λ bound at the DEPLOYED verifier.**
`CircuitSoundness.verifyBatch` evaluates `ExtFieldChallenge.verifyAlgoUnifiedFaithfulExt`, which
STRENGTHENS `verifyAlgoUnifiedFaithful`; monotonicity of `winProb` in the event therefore carries §3
onto the deployed predicate verbatim. So the bundle's Λ clause is a bounded-advantage event about the
verifier the light client actually runs, not about a weaker stand-in. -/
theorem rlc_lambda_nonexceptionality_is_bounded_ext {Ω F : Type} [Fintype Ω] [Fintype F] [Inhabited F]
    [CommRing F] [IsDomain F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat)
    (pub : WrapPublics F) (proofOf : Ω → BatchProofData F) (extViewOf : Ω → ExtVerifierView F)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    (R : Polynomial F) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
            initState logN (proofOf ω) pub (extViewOf ω)
          && declaredAlphaExceptional R (proofOf ω))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans
    (winProb_mono
      (w2 := fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional R (proofOf ω)) ?_)
    (rlc_lambda_nonexceptionality_is_bounded perm RATE toNat params vk core A initState logN
      pub proofOf hrom R)
  intro ω hω
  rw [Bool.and_eq_true] at hω
  rw [Bool.and_eq_true]
  exact ⟨verifyAlgoUnifiedFaithfulExt_imp_verifyAlgoUnifiedFaithful perm RATE toNat params vk core A
    extCore extA W initState logN (proofOf ω) pub (extViewOf ω) hω.1, hω.2⟩

/-! ## §5 — the DEPLOYED instances (BabyBear, and the `FriLdtExtractV3` Λ-clause itself). -/

section BabyBear

open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.DescriptorIR2 (VmTrace VmConstraint2)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.AlgoStarkSoundTransferV3 (Rfam arithList)

/-- **The Λ error at the deployed field, with the combinatorial cap applied.** For a per-constraint
residual family `Rf : Fin n → BabyBear` (`n = #arith constraints`), the probability the deployed
faithful verifier accepts with a declared RLC challenge in the batching polynomial's bad set is at
most `(n − 1)/2013265921` — the `batchResidual_natDegree_lt` degree cap ridden through §3. -/
theorem rlc_lambda_bounded_babybear {Ω : Type} [Fintype Ω]
    (perm : List BabyBear → List BabyBear) (RATE : Nat) (toNat : BabyBear → Nat)
    (params : FriParams) (vk : RecursionVk BabyBear) (core : FriCore BabyBear)
    (A : FieldArith BabyBear) (initState : List BabyBear) (logN : Nat)
    (pub : WrapPublics BabyBear) (proofOf : Ω → BatchProofData BabyBear)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    {n : ℕ} (hn : 0 < n) (Rf : Fin n → BabyBear) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional (batchResidual Rf) (proofOf ω))
      ≤ ((n - 1 : ℕ) : ℝ) / 2013265921 := by
  have hbase := rlc_lambda_nonexceptionality_is_bounded perm RATE toNat params vk core A
    initState logN pub proofOf hrom (batchResidual Rf)
  rw [show ((Fintype.card BabyBear : ℝ)) = 2013265921 by exact_mod_cast babybear_card] at hbase
  refine le_trans hbase ?_
  have hd : (batchResidual Rf).natDegree ≤ n - 1 := by
    have := batchResidual_natDegree_lt hn Rf; omega
  -- `gcongr` reduces to the numerator inequality and discharges it from `hd`.
  gcongr

/-- **The `FriLdtExtractV3` Λ-clause itself, bounded.** At the EXACT object the deployed bundle
carries — `Λ ∉ exceptionalSet (batchResidual (Rfam transferV3 t ζ qp))`
(`AlgoStarkSoundTransferV3.lean:155`) — the probability that the deployed faithful verifier accepts
while the prover's declared RLC challenge violates the clause is at most
`(#(arithList transferV3) − 1)/2013265921`. This is what `rlc_lambda_is_bounded_fs_form` (`:295`) was
missing: an acceptance event, an adaptive prover, and a probability. -/
theorem hLam_clause_bounded_babybear {Ω : Type} [Fintype Ω]
    (perm : List BabyBear → List BabyBear) (RATE : Nat) (toNat : BabyBear → Nat)
    (params : FriParams) (vk : RecursionVk BabyBear) (core : FriCore BabyBear)
    (A : FieldArith BabyBear) (initState : List BabyBear) (logN : Nat)
    (pub : WrapPublics BabyBear) (proofOf : Ω → BatchProofData BabyBear)
    (hrom : RomUniformAlpha perm RATE toNat params initState logN proofOf pub)
    (t : VmTrace) (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (hn : 0 < (arithList transferV3).length) :
    winProb (fun ω =>
        verifyAlgoUnifiedFaithful perm RATE toNat params vk core A initState logN (proofOf ω) pub
          && declaredAlphaExceptional (batchResidual (Rfam transferV3 t ζ qp)) (proofOf ω))
      ≤ (((arithList transferV3).length - 1 : ℕ) : ℝ) / 2013265921 :=
  rlc_lambda_bounded_babybear perm RATE toNat params vk core A initState logN pub proofOf hrom
    hn (Rfam transferV3 t ζ qp)

end BabyBear

/-! ## §6 — THE FALSIFIER: the bound is FALSE at bare `verifyAlgo`.

One prover strategy over the REAL `deriveTranscript`, run against two verifiers. `RomUniformAlpha`
HOLDS for it (the transcript α is the sampled element itself), so no hypothesis is dodged.

  * against BARE `verifyAlgo` at the fully concrete `fullChecks`: accepted for EVERY ω — the bare
    verifier never inspects `singleAirOpenings` (`fullChecks.batchTables = batchTablesCheck`, which
    walks `tableOpenings`) — and the strategy declares the constant exceptional challenge `alpha := 0`,
    so the joint event has probability `1 > 1/7 = natDegree X / |ZMod 7|`. FALSE.
  * against `verifyAlgoUnifiedFaithful`: accepted ONLY at `ω = 0`, because the α-binding tooth
    demands `alpha = transcriptAlpha = ω`. Joint-event probability exactly `1/7` — the §3 bound,
    ATTAINED.

So §3 is neither vacuous nor slack, and it is the forcing lemma (nothing else) that separates the
two. -/

section Falsifier

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance : Inhabited (ZMod 7) := ⟨0⟩

/-- Identity permutation: the squeeze returns exactly what was observed, so the derived α is a
bijection of the sampled element (the honest positive pole of the ROM residual). -/
private def fPerm : List (ZMod 7) → List (ZMod 7) := id
private def fRATE : Nat := 1
private def fToNat : ZMod 7 → Nat := fun x => x.val
private def fInit : List (ZMod 7) := [0]
private def fLogN : Nat := 1

/-- Toy params: NO queries (so the FRI query legs are structurally discharged and the fixture
isolates the α tooth), `powBits = 0`, `extDeg = 1` (α and ζ are single base lanes). -/
private def fParams : FriParams :=
  { logBlowup := 1, numQueries := 0, powBits := 0, maxLogArity := 1,
    logFinalPolyLen := 0, extDeg := 1 }

private def fVk : RecursionVk (ZMod 7) := ⟨fun _ => true⟩

private def fCore : FriCore (ZMod 7) :=
  { compress := fun a b => [a.headD 0 * 3 + b.headD 0 * 5 + 1],
    foldCombine := fun beta _x e0 e1 => e0 + beta * e1 }

/-- Genuine `ZMod 7` field arithmetic (not a stub): the real `+`, `*`, `^`. -/
private def fArith : FieldArith (ZMod 7) :=
  { add := (· + ·), mul := (· * ·), pow := fun b n => b ^ n, zero := 0, one := 1 }

private def fPub : WrapPublics (ZMod 7) := ⟨[]⟩

/-- A single-AIR opening at a declared RLC challenge `a`, honest in every OTHER field: `zeta` tracks
the transcript, `vanishing = ζ − 1` is the genuine `Z_H(ζ)` at `degreeBits = 0`, `invVanishing` is its
GENUINE field inverse `(ζ−1)^5` (Fermat over `ZMod 7`), and the quotient identity holds. So the only
tooth `a` can trip is the α-BINDING one — which is exactly the point being isolated. -/
private def openingAt (ω a : ZMod 7) : SingleAirOpening (ZMod 7) :=
  { zeta := ω, degreeBits := 0, expectedDegreeBits := 0, alpha := a,
    constraintEvals := [0], zps := [], quotientChunks := [],
    vanishing := ω - 1, invVanishing := (ω - 1) ^ 5, logupCumSum := 0 }

/-- A well-formed no-query proof carrying one opening declaring the RLC challenge `a`. Each sampled
`ω` is submitted as the trace commitment, so the transcript genuinely varies with the sampled
randomness. -/
private def proofAt (ω a : ZMod 7) : BatchProofData (ZMod 7) :=
  { degreeBitsPreamble := [0], baseDegreeBitsPreamble := [0], preprocessedWidthPreamble := [0],
    traceCommit := [ω], friCommitments := [], finalPoly := [0], queries := [],
    exposedSegment := [], oodPoint := [ω], powWitness := [0], friLogArities := [],
    singleAirOpenings := [openingAt ω a] }

/-- **The ATTACK strategy**: declare the FIXED exceptional challenge `0` on every run, whatever the
transcript squeezed. This is the free-Λ prover the bare verifier cannot see. -/
private def attackProof (ω : ZMod 7) : BatchProofData (ZMod 7) := proofAt ω 0

/-- **The HONEST strategy**: declare the transcript's own challenge `ω`. Identical in every other
field to the attack; the two differ ONLY in the `alpha` they declare. -/
private def honestProof (ω : ZMod 7) : BatchProofData (ZMod 7) := proofAt ω ω

/-- Running the REAL continued challenger (`FriVerifier.deriveTranscript`, identity permutation,
RATE 1, `extDeg = 1`, init `[0]`, the full preamble/trace/publics absorb sequence) on the attack
proof squeezes back exactly the sampled `ω` — computed by the kernel over all of `ZMod 7`. -/
theorem attack_alpha_is_id : ∀ ω : ZMod 7,
    transcriptAlpha fPerm fRATE fToNat fParams fInit fLogN (attackProof ω) fPub = ω := by decide

/-- **The ROM residual HOLDS for the attack strategy** — at the real squeeze, not an abstract map.
So the falsifier below satisfies every hypothesis of §3 except the verifier. -/
theorem romUniformAlpha_attack_holds :
    RomUniformAlpha fPerm fRATE fToNat fParams fInit fLogN attackProof fPub := by
  show RomUniform (fun ω : ZMod 7 =>
    transcriptAlpha fPerm fRATE fToNat fParams fInit fLogN (attackProof ω) fPub)
  have hz : (fun ω : ZMod 7 =>
        transcriptAlpha fPerm fRATE fToNat fParams fInit fLogN (attackProof ω) fPub)
      = fun ω => ω := by
    funext ω; exact attack_alpha_is_id ω
  rw [hz]
  exact romUniform_id

/-- `0` is exceptional for the residual `X` (its unique root). -/
theorem zero_mem_exceptionalSet_X : (0 : ZMod 7) ∈ exceptionalSet (X : Polynomial (ZMod 7)) := by
  unfold exceptionalSet
  rw [roots_X]
  simp

/-- The declared challenge is exceptional on EVERY run: the strategy always submits `alpha = 0`. -/
theorem attack_declares_exceptional (ω : ZMod 7) :
    declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω) = true := by
  unfold declaredAlphaExceptional
  rw [List.any_eq_true]
  refine ⟨openingAt ω 0, by simp [attackProof, proofAt], ?_⟩
  exact decide_eq_true zero_mem_exceptionalSet_X

/-- **The arithmetic teeth of the fixture pass for every `ω ≠ 1`**, whatever challenge is declared:
the degree pin, the vanishing recompute, the genuine inverse, and the quotient identity all hold.
(`ω = 1` is intrinsically degenerate — `Z_H(1) = 0` has no inverse — not a fixture artifact.) So on
`ω ∈ {2,…,6}` the ONLY tooth that can reject the attack is the α binding: the discriminator below is
the forcing lemma, not some incidental arithmetic failure. -/
theorem fixture_arithmetic_teeth_pass : ∀ ω a : ZMod 7, ω ≠ 1 →
    Dregg2.Circuit.BatchTablesSingleAir.batchTablesCheckUnified fArith
      (proofAt ω a).singleAirOpenings = true := by decide

/-- **The bare verifier ACCEPTS the attack on every run.** `fullChecks` never reads
`singleAirOpenings`, so the free RLC challenge costs the prover nothing. Kernel-computed over all of
`ZMod 7`. -/
theorem bare_accepts_attack : ∀ ω : ZMod 7,
    verifyAlgo fPerm fRATE fToNat fParams fVk (fullChecks fCore fArith fToNat fParams.powBits)
      fInit fLogN (attackProof ω) fPub = true := by decide

/-- **The faithful verifier accepts the attack EXACTLY at `ω = 0`.** For `ω ≠ 0` the α-binding tooth
(`singleAirChallengesBound`) rejects: the declared `0` is not the transcript's `ω`. Kernel-computed
over all of `ZMod 7`. -/
theorem faithful_accepts_attack_iff : ∀ ω : ZMod 7,
    verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
      (attackProof ω) fPub = decide (ω = 0) := by decide

/-- **THE FALSIFIER — §3 is FALSE at bare `verifyAlgo`.** With the ROM residual SATISFIED
(`romUniformAlpha_attack_holds`), the joint event "bare `verifyAlgo` accepts ∧ the declared RLC
challenge is exceptional for `X`" has probability `1`, which is NOT `≤ natDegree X / |ZMod 7| = 1/7`.
So the α-forcing of `verifyAlgoUnifiedFaithful` is load-bearing: drop it and the bound collapses. -/
theorem rlc_lambda_bound_FALSE_at_bare_verifyAlgo :
    RomUniformAlpha fPerm fRATE fToNat fParams fInit fLogN attackProof fPub
      ∧ winProb (fun ω : ZMod 7 =>
        verifyAlgo fPerm fRATE fToNat fParams fVk (fullChecks fCore fArith fToNat fParams.powBits)
            fInit fLogN (attackProof ω) fPub
          && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω)) = 1
      ∧ ¬ (winProb (fun ω : ZMod 7 =>
            verifyAlgo fPerm fRATE fToNat fParams fVk
                (fullChecks fCore fArith fToNat fParams.powBits) fInit fLogN (attackProof ω) fPub
              && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω))
          ≤ ((X : Polynomial (ZMod 7)).natDegree : ℝ) / (Fintype.card (ZMod 7) : ℝ)) := by
  have hev : (fun ω : ZMod 7 =>
      verifyAlgo fPerm fRATE fToNat fParams fVk (fullChecks fCore fArith fToNat fParams.powBits)
          fInit fLogN (attackProof ω) fPub
        && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω))
      = fun _ : ZMod 7 => true := by
    funext ω
    rw [bare_accepts_attack ω, attack_declares_exceptional ω]
    rfl
  have h1 : winProb (fun ω : ZMod 7 =>
      verifyAlgo fPerm fRATE fToNat fParams fVk (fullChecks fCore fArith fToNat fParams.powBits)
          fInit fLogN (attackProof ω) fPub
        && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω)) = 1 := by
    rw [hev]; exact winProb_top
  refine ⟨romUniformAlpha_attack_holds, h1, ?_⟩
  rw [h1, natDegree_X, show Fintype.card (ZMod 7) = 7 from ZMod.card 7]
  norm_num

/-- **The SAME strategy at the FAITHFUL verifier: probability exactly `1/7`, the §3 bound ATTAINED.**
The α-binding tooth admits the run only when the declared challenge IS the transcript's, i.e. at
`ω = 0`. So the bound holds where it failed at bare `verifyAlgo`, and holds TIGHTLY. -/
theorem attack_at_faithful_is_one_seventh :
    winProb (fun ω : ZMod 7 =>
        verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
            (attackProof ω) fPub
          && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω))
      = ((X : Polynomial (ZMod 7)).natDegree : ℝ) / (Fintype.card (ZMod 7) : ℝ) := by
  have hev : (fun ω : ZMod 7 =>
      verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
          (attackProof ω) fPub
        && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω))
      = fun ω : ZMod 7 => decide (ω = 0) := by
    funext ω
    rw [faithful_accepts_attack_iff ω, attack_declares_exceptional ω, Bool.and_true]
  rw [hev, natDegree_X]
  unfold winProb
  rw [show (Finset.univ.filter (fun ω : ZMod 7 => decide (ω = 0) = true)) = {0} by
      ext x; simp,
    Finset.card_singleton, show Fintype.card (ZMod 7) = 7 from ZMod.card 7]

/-- The falsifier's two poles, side by side: the SAME prover strategy against the two verifiers, with
`RomUniformAlpha` satisfied in both cases. Bare: `1`. Faithful: `1/7`. The gap IS the forcing. -/
theorem forcing_is_load_bearing :
    RomUniformAlpha fPerm fRATE fToNat fParams fInit fLogN attackProof fPub
      ∧ winProb (fun ω : ZMod 7 =>
          verifyAlgo fPerm fRATE fToNat fParams fVk (fullChecks fCore fArith fToNat fParams.powBits)
              fInit fLogN (attackProof ω) fPub
            && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω)) = 1
      ∧ winProb (fun ω : ZMod 7 =>
          verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
              (attackProof ω) fPub
            && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (attackProof ω)) = 1 / 7 :=
  ⟨romUniformAlpha_attack_holds,
   rlc_lambda_bound_FALSE_at_bare_verifyAlgo.2.1,
   by
     have h := attack_at_faithful_is_one_seventh
     rwa [natDegree_X, show Fintype.card (ZMod 7) = 7 from ZMod.card 7, Nat.cast_one,
       show ((7 : ℕ) : ℝ) = 7 by norm_num] at h⟩

/-! ### The bound FIRES on an HONEST prover too (not only on a rejected attacker).

The attack family is admitted by the faithful verifier on exactly one run, so its `1/7` could be read
as "the bound is tight only where the attack degenerates". It is not: the HONEST strategy — identical
in every field except that it declares the transcript's own challenge — is admitted on SIX of the
seven runs, and its joint event still has probability exactly `1/7`. -/

/-- The exceptional set of the residual `X` over `ZMod 7` is exactly its root `{0}`. -/
theorem exceptionalSet_X_eq : exceptionalSet (X : Polynomial (ZMod 7)) = {0} := by
  unfold exceptionalSet
  rw [roots_X]
  simp

/-- The honest strategy declares the transcript's challenge, so its declared challenge is exceptional
exactly when the transcript squeezed the root `0`. -/
theorem honest_declares_exceptional_iff (ω : ZMod 7) :
    declaredAlphaExceptional (X : Polynomial (ZMod 7)) (honestProof ω) = decide (ω = 0) := by
  unfold declaredAlphaExceptional honestProof proofAt openingAt
  simp [exceptionalSet_X_eq]

/-- **The faithful verifier ACCEPTS the honest strategy on six of the seven runs.** Only the
intrinsically degenerate `ω = 1` (where `Z_H(ζ) = 0` has no inverse) is rejected — so the fixture is
not rigged to reject, and the attack's rejection above is the α tooth, not the arithmetic. -/
theorem faithful_accepts_honest_iff : ∀ ω : ZMod 7,
    verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
      (honestProof ω) fPub = decide (ω ≠ 1) := by decide

/-- The honest strategy satisfies the ROM residual too (`deriveTranscript` never observes
`singleAirOpenings`, so the squeeze is the same map as for the attack). Needed so the tightness below
is tightness OF §3 — attained at an instance meeting §3's hypotheses, not at an instance that dodges
them. -/
theorem romUniformAlpha_honest_holds :
    RomUniformAlpha fPerm fRATE fToNat fParams fInit fLogN honestProof fPub := by
  show RomUniform (fun ω : ZMod 7 =>
    transcriptAlpha fPerm fRATE fToNat fParams fInit fLogN (honestProof ω) fPub)
  have hz : (fun ω : ZMod 7 =>
        transcriptAlpha fPerm fRATE fToNat fParams fInit fLogN (honestProof ω) fPub)
      = fun ω => ω := by
    funext ω
    revert ω
    decide
  rw [hz]
  exact romUniform_id

/-- **THE BOUND FIRES, TIGHTLY, ON AN ACCEPTED HONEST RUN.** For the honest strategy — which
satisfies §3's ROM hypothesis and is admitted by the faithful verifier on six of seven runs — the
joint event "the verifier ACCEPTS ∧ the bound-to-transcript RLC challenge is exceptional for `X`" has
probability exactly `natDegree X / |ZMod 7| = 1/7`. So §3 is neither vacuous (the event genuinely
occurs, on an ACCEPTING run, with positive probability) nor slack (its bound is ATTAINED). -/
theorem rlc_lambda_bound_fires_and_is_tight :
    RomUniformAlpha fPerm fRATE fToNat fParams fInit fLogN honestProof fPub
      ∧ winProb (fun ω : ZMod 7 =>
          verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
              (honestProof ω) fPub
            && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (honestProof ω))
        = ((X : Polynomial (ZMod 7)).natDegree : ℝ) / (Fintype.card (ZMod 7) : ℝ) := by
  refine ⟨romUniformAlpha_honest_holds, ?_⟩
  have hev : (fun ω : ZMod 7 =>
      verifyAlgoUnifiedFaithful fPerm fRATE fToNat fParams fVk fCore fArith fInit fLogN
          (honestProof ω) fPub
        && declaredAlphaExceptional (X : Polynomial (ZMod 7)) (honestProof ω))
      = fun ω : ZMod 7 => decide (ω = 0) := by
    funext ω
    rw [faithful_accepts_honest_iff ω, honest_declares_exceptional_iff ω]
    revert ω
    decide
  rw [hev, natDegree_X]
  unfold winProb
  rw [show (Finset.univ.filter (fun ω : ZMod 7 => decide (ω = 0) = true)) = {0} by
      ext x; simp,
    Finset.card_singleton, show Fintype.card (ZMod 7) = 7 from ZMod.card 7]

end Falsifier

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms alphaEscape_le
#assert_axioms forced_alpha_of_faithful
#assert_axioms rlc_lambda_nonexceptionality_is_bounded
#assert_axioms rlc_lambda_nonexceptionality_is_bounded_ext
#assert_axioms rlc_lambda_bounded_babybear
#assert_axioms hLam_clause_bounded_babybear
#assert_axioms attack_alpha_is_id
#assert_axioms romUniformAlpha_attack_holds
#assert_axioms attack_declares_exceptional
#assert_axioms fixture_arithmetic_teeth_pass
#assert_axioms bare_accepts_attack
#assert_axioms faithful_accepts_attack_iff
#assert_axioms rlc_lambda_bound_FALSE_at_bare_verifyAlgo
#assert_axioms attack_at_faithful_is_one_seventh
#assert_axioms forcing_is_load_bearing
#assert_axioms exceptionalSet_X_eq
#assert_axioms honest_declares_exceptional_iff
#assert_axioms faithful_accepts_honest_iff
#assert_axioms romUniformAlpha_honest_holds
#assert_axioms rlc_lambda_bound_fires_and_is_tight

end Dregg2.Circuit.RlcRomBound
