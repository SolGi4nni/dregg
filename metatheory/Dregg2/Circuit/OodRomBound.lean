/-
# `Dregg2.Circuit.OodRomBound` — the ROM half of survey finding #4: bounding the
exceptional-probability of the TRANSCRIPT-BOUND OOD point.

Part (a) (`FriTranscriptBind`) made ζ a FUNCTION of the transcript: `verifyAlgoTB` acceptance
forces `proof.oodPoint = deriveOod perm RATE initState proof.traceCommit`
(`verifyAlgoTB_forces_ood_transcript_bound`). Part (b), here, is the PROBABILISTIC half: how
often does that transcript-derived ζ land in the exceptional set of a residual `R`?

## The honest floor — `RomUniform` (THE named residual of this file)

For a FIXED permutation `perm`, `deriveOod` is a deterministic function and NO uniformity of the
squeezed ζ is provable — a fixed sponge output is whatever it is. The standard cryptographic move
is the RANDOM-ORACLE idealization: over a freshly sampled trace commitment, the squeeze output is
distributed as a uniform draw from `F`. We state this HONESTLY as the named Prop `RomUniform`:
the distribution the map `ω ↦ ζ(ω)` induces on `F` (over the finite sampled-transcript space `Ω`)
EQUALS the uniform sampling distribution — expressed event-by-event as an equality of `winProb`s,
`winProb (acc ∘ ζmap) = winProb acc` for every event `acc : F → Bool`. This is exactly "the
induced distribution of `deriveOod` equals the uniform `oodNonExcAcc` sampling distribution", and
it is where the argument bottoms out. It is a GENUINE assumption, not a tautology:

  * SATISFIABLE — and satisfiable at the REAL `deriveOod` algorithm: for the identity permutation
    over `ZMod 7` (RATE 1) the derived ζ is a bijection of the observed commitment, so
    `RomUniform` HOLDS (`romUniformDerive_id_perm_holds`, via `romUniform_of_bijective`).
  * REFUTABLE — a degenerate constant permutation makes `deriveOod` constant, and `RomUniform`
    FAILS (`romUniformDerive_const_perm_fails`, via `not_romUniform_const`). So the Prop
    genuinely discriminates good squeezes from bad ones; assuming it for Poseidon2 is the ROM
    idealization, named and visible, never an axiom.

## What is PROVED under that named floor

  * `transcriptBound_ood_escape_le` — THE TRANSPORT: under `RomUniform ζmap`, the probability the
    transcript-bound ζ lands in `exceptionalSet R` is `≤ natDegree R / |F|`. One rewrite across
    the distribution equality lands on the already-proved Schwartz–Zippel game bound
    (`OodSoundnessGame.oodNonExc_winProb_le`); nothing further is assumed.
  * `deriveOod_escape_le` / `…_babybear` — the same bound with `ζmap` the ACTUAL
    `FriTranscriptBind.deriveOod ∘ enc` squeeze (`RomUniformDerive`), specialized to the deployed
    field: `≤ natDegree R / 2013265921`.
  * `ood_nonexceptionality_is_bounded` — THE PAYOFF: the joint event "`verifyAlgoTB` ACCEPTS and
    the proof's OOD point is exceptional for `R`" has probability `≤ natDegree R / |F|`. The
    composition is real: acceptance FORCES ζ transcript-bound (part (a)), and the bound rides the
    forced value through `RomUniform`. The carried `FriLdtExtractV3` "ζ non-exceptional" clause is
    thereby a BOUNDED-ADVANTAGE event under transcript-binding + `RomUniform` — no longer a free
    prover choice. `hnonexc_clause_bounded_babybear` states it at the deployed residual
    `constraintPoly d t c − vanishingPoly t · qp c` over BabyBear.

## FIRE (non-vacuity, both poles)

`transcriptBound_escape_fires`: on the concrete `ZMod 7` instance with the REAL `deriveOod`, the
escape probability is EXACTLY `1/7 = natDegree X / |F|` — a genuine positive real in `[0,1]`,
tight against the bound. Plus the satisfiable/refutable poles of `RomUniform` above, and the
concrete-degree unit-interval check `ood_escape_deg4_babybear`.

## Residual after this file

`RomUniform` (equivalently its `deriveOod` instance `RomUniformDerive` at the deployed
Poseidon2-w16 permutation) — the ROM idealization of the duplex-sponge squeeze. Everything else
(the transport, the composition with transcript-binding, the Schwartz–Zippel numerator) is proved.
-/
import Dregg2.Tactics
import Dregg2.Crypto.ProbCrypto
import Dregg2.Circuit.OodSoundnessGame
import Dregg2.Circuit.FriTranscriptBind

namespace Dregg2.Circuit.OodRomBound

open Polynomial
open Dregg2.Crypto.ProbCrypto
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Circuit.OodSoundnessGame
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.FriTranscriptBind

/-! ## §0 — `winProb` transport plumbing (monotonicity; not in `ProbCrypto`). -/

/-- **`winProb` is monotone in the event.** If every `w1`-win is a `w2`-win, the favorable set is
a subset and the counting probability can only grow. The plumbing that lets the joint event
"accept ∧ exceptional" ride the pure escape event's bound. -/
theorem winProb_mono {Ω : Type*} [Fintype Ω] {w1 w2 : Ω → Bool}
    (h : ∀ ω, w1 ω = true → w2 ω = true) : winProb w1 ≤ winProb w2 := by
  unfold winProb
  have hsub : Finset.univ.filter (fun o => w1 o = true)
      ⊆ Finset.univ.filter (fun o => w2 o = true) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact h x hx
  gcongr

/-! ## §1 — `RomUniform`: THE NAMED RESIDUAL (the ROM idealization of the sponge squeeze). -/

/-- **`RomUniform ζmap` — the random-oracle idealization, stated honestly.** Over the finite
sampled-transcript space `Ω` (fresh trace commitments), the map `ζmap : Ω → F` (the sponge squeeze
`deriveOod`) induces on `F` EXACTLY the uniform sampling distribution: for EVERY event
`acc : F → Bool`, the probability of the event under the induced distribution equals its
probability under a uniform draw — `winProb (acc ∘ ζmap) = winProb acc`. This is the distribution
equality "`deriveOod` over the idealized random permutation ≡ the uniform `oodNonExcAcc` sampling
distribution". It is NOT provable for a fixed permutation (a fixed sponge output is deterministic)
— it is the floor this file's bounds stand on, a named hypothesis, never an axiom. It genuinely
discriminates: satisfiable (`romUniform_of_bijective`, `romUniformDerive_id_perm_holds`), refutable
(`not_romUniform_const`, `romUniformDerive_const_perm_fails`). -/
def RomUniform {Ω F : Type*} [Fintype Ω] [Fintype F] (ζmap : Ω → F) : Prop :=
  ∀ acc : F → Bool, winProb (fun ω => acc (ζmap ω)) = winProb acc

/-- The identity squeeze is `RomUniform` (the trivial positive pole; the honest one at the real
`deriveOod` is `romUniformDerive_id_perm_holds` below). -/
theorem romUniform_id {F : Type*} [Fintype F] : RomUniform (fun x : F => x) := fun _ => rfl

/-- **A BIJECTIVE squeeze is `RomUniform`.** If `ζmap` is a bijection of a same-size transcript
space onto `F`, each field element is hit by exactly one transcript, so every event's counting
probability is preserved: the favorable sets biject (`Finset.card_bij`) and `|Ω| = |F|`. The
generic satisfiability certificate for the named floor. -/
theorem romUniform_of_bijective {Ω F : Type*} [Fintype Ω] [Fintype F]
    {ζmap : Ω → F} (hbij : Function.Bijective ζmap) : RomUniform ζmap := by
  intro acc
  unfold winProb
  have hcardΩ : Fintype.card Ω = Fintype.card F := Fintype.card_of_bijective hbij
  have hcard : (Finset.univ.filter (fun ω => acc (ζmap ω) = true)).card
      = (Finset.univ.filter (fun x => acc x = true)).card := by
    apply Finset.card_bij (fun ω _ => ζmap ω)
    · intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact hω
    · intro a _ b _ hab
      exact hbij.1 hab
    · intro x hx
      obtain ⟨ω, hω⟩ := hbij.2 x
      refine ⟨ω, ?_, hω⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hω]
      exact hx
  rw [hcard, hcardΩ]

/-- **A CONSTANT squeeze is NOT `RomUniform` (the refutable pole).** A squeeze that always outputs
`z` puts all mass on one point; testing the event `{z}` gives probability `1` on the left but
`1/|F| < 1` on the right. So `RomUniform` is a genuine assumption with bite — a degenerate sponge
violates it. -/
theorem not_romUniform_const {Ω F : Type*} [Fintype Ω] [Nonempty Ω] [Fintype F] [DecidableEq F]
    (z : F) (hF : 1 < Fintype.card F) : ¬ RomUniform (fun _ : Ω => z) := by
  intro h
  have hspec := h (fun x => decide (x = z))
  have hL : winProb (fun _ : Ω => decide (z = z)) = 1 := by
    have hfun : (fun _ : Ω => decide (z = z)) = fun _ : Ω => true := by
      funext _; simp
    rw [hfun]
    exact winProb_top
  have hR : winProb (fun x : F => decide (x = z)) = 1 / (Fintype.card F : ℝ) := by
    unfold winProb
    have hfilter : Finset.univ.filter (fun x : F => decide (x = z) = true) = {z} := by
      ext x
      simp
    rw [hfilter, Finset.card_singleton]
    norm_num
  rw [hL, hR] at hspec
  have hc : (2 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hF
  have hcpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  rw [eq_div_iff (ne_of_gt hcpos), one_mul] at hspec
  linarith

/-! ## §2 — THE TRANSPORT: the escape bound across the `RomUniform` distribution equality. -/

/-- **`transcriptBound_ood_escape_le` — THE MAIN BOUND.** Under the named ROM idealization
`RomUniform ζmap`, the probability that the transcript-bound OOD point lands in
`exceptionalSet R` is at most `natDegree R / |F|`. The proof is exactly the distribution
transport: rewrite the induced-distribution probability into the uniform one (`hrom` at the event
`oodNonExcAcc R`), then the already-proved Schwartz–Zippel game bound
`OodSoundnessGame.oodNonExc_winProb_le` finishes. Nothing is assumed beyond `RomUniform`. -/
theorem transcriptBound_ood_escape_le {Ω : Type*} [Fintype Ω]
    {F : Type*} [Fintype F] [CommRing F] [IsDomain F] [DecidableEq F]
    (ζmap : Ω → F) (hrom : RomUniform ζmap) (R : Polynomial F) :
    winProb (fun ω => oodNonExcAcc R (ζmap ω))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  rw [hrom (oodNonExcAcc R)]
  exact oodNonExc_winProb_le R

/-! ## §3 — the ζmap IS `deriveOod`: wiring to the part-(a) transcript squeeze. -/

/-- **The transcript-derived OOD point as a field element** — the single squeezed coefficient of
`FriTranscriptBind.deriveOod` (a length-1 list; `sampleExt … 1`). -/
def transcriptZeta {F : Type} [Inhabited F] (perm : List F → List F) (RATE : Nat)
    (initState : List F) (traceCommit : List F) : F :=
  (deriveOod perm RATE initState traceCommit).headI

/-- **`RomUniformDerive` — the named residual AT THE REAL SQUEEZE.** `RomUniform` instantiated
with `ζmap = transcriptZeta ∘ enc`: over the finite sampled-commitment space `Ω` (encoded into the
observed field-element stream by `enc`), the ACTUAL `deriveOod` duplex-sponge squeeze induces the
uniform distribution on `F`. Assuming this for the deployed Poseidon2-w16 permutation is the
standard ROM idealization — the precise honest floor of finding #4(b). -/
def RomUniformDerive {F : Type} [Inhabited F] [Fintype F] {Ω : Type} [Fintype Ω]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (enc : Ω → List F) : Prop :=
  RomUniform (fun ω => transcriptZeta perm RATE initState (enc ω))

/-- The escape bound at the real squeeze: under `RomUniformDerive`, the `deriveOod`-derived ζ is
exceptional for `R` with probability `≤ natDegree R / |F|`. -/
theorem deriveOod_escape_le {F : Type} [Inhabited F] [Fintype F]
    [CommRing F] [IsDomain F] [DecidableEq F] {Ω : Type} [Fintype Ω]
    (perm : List F → List F) (RATE : Nat) (initState : List F) (enc : Ω → List F)
    (hrom : RomUniformDerive perm RATE initState enc) (R : Polynomial F) :
    winProb (fun ω => oodNonExcAcc R (transcriptZeta perm RATE initState (enc ω)))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) :=
  transcriptBound_ood_escape_le _ hrom R

/-! ## §4 — THE PAYOFF: acceptance + exceptionality is a bounded-advantage event.

Part (a) forces the accepted proof's ζ to BE the transcript squeeze; §2 bounds the squeeze's
escape probability. Composing: the joint event "`verifyAlgoTB` accepts AND the proof's OOD point
is exceptional" is bounded — the carried `FriLdtExtractV3` non-exceptionality clause is no longer
a free prover choice. -/

/-- **`ood_nonexceptionality_is_bounded` — the composed payoff.** For any adaptive prover strategy
`proofOf : Ω → BatchProofData F` whose submitted trace commitment is the sampled one
(`hcommit`), under `RomUniformDerive`: the probability that `verifyAlgoTB` ACCEPTS and the proof's
OOD point lies in `exceptionalSet R` is `≤ natDegree R / |F|`. The composition is genuine —
`verifyAlgoTB_forces_ood_transcript_bound` (part (a)) pins the accepted ζ to
`deriveOod (traceCommit)`, `hcommit` identifies the commitment with the sample, and the
`RomUniform` transport (§2) bounds the escape. The "ζ non-exceptional" clause carried by
`FriLdtExtractV3` is now a bounded-advantage event, not an assumption about the prover's will. -/
theorem ood_nonexceptionality_is_bounded {Ω F : Type} [Fintype Ω] [Fintype F] [Inhabited F]
    [CommRing F] [IsDomain F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (checks : FriChecks F) (initState : List F) (logN : Nat)
    (pub : WrapPublics F) (enc : Ω → List F) (proofOf : Ω → BatchProofData F)
    (hcommit : ∀ ω, (proofOf ω).traceCommit = enc ω)
    (hrom : RomUniformDerive perm RATE initState enc) (R : Polynomial F) :
    winProb (fun ω =>
        verifyAlgoTB perm RATE toNat params vk checks initState logN (proofOf ω) pub
          && decide ((proofOf ω).oodPoint.headI ∈ exceptionalSet R))
      ≤ (R.natDegree : ℝ) / (Fintype.card F : ℝ) := by
  refine le_trans
    (winProb_mono
      (w2 := fun ω => oodNonExcAcc R (transcriptZeta perm RATE initState (enc ω))) ?_)
    (deriveOod_escape_le perm RATE initState enc hrom R)
  intro ω hω
  rw [Bool.and_eq_true] at hω
  have hood := verifyAlgoTB_forces_ood_transcript_bound perm RATE toNat params vk checks
    initState logN (proofOf ω) pub hω.1
  show decide (transcriptZeta perm RATE initState (enc ω) ∈ exceptionalSet R) = true
  unfold transcriptZeta
  rw [← hcommit ω, ← hood]
  exact hω.2

/-! ## §5 — specialization at the deployed field (BabyBear, `|F| = 2013265921`). -/

section BabyBear

open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.TraceColumnInterp
open Dregg2.Circuit.FieldIntegerLift

noncomputable instance : Inhabited BabyBear := ⟨0⟩

/-- The escape bound at the deployed field: `≤ natDegree R / 2013265921`. -/
theorem deriveOod_escape_le_babybear {Ω : Type} [Fintype Ω]
    (perm : List BabyBear → List BabyBear) (RATE : Nat) (initState : List BabyBear)
    (enc : Ω → List BabyBear) (hrom : RomUniformDerive perm RATE initState enc)
    (R : Polynomial BabyBear) :
    winProb (fun ω => oodNonExcAcc R (transcriptZeta perm RATE initState (enc ω)))
      ≤ (R.natDegree : ℝ) / 2013265921 := by
  have h := deriveOod_escape_le perm RATE initState enc hrom R
  rwa [show ((Fintype.card BabyBear : ℝ)) = 2013265921 by exact_mod_cast babybear_card] at h

/-- **The payoff at the DEPLOYED residual.** For the exact residual the `transferV3` frontier
carries (`constraintPoly d t c − vanishingPoly t · qp c`, the `hnonexc` object of
`ood_forces_mainAirAccept_field_of_residuals`): under transcript-binding + `RomUniformDerive`, the
probability the verifier accepts with an OOD point exceptional for that residual is at most
`natDegree(residual) / 2013265921`. The carried `hnonexc` clause is a bounded-advantage event at
the deployed field. -/
theorem hnonexc_clause_bounded_babybear {Ω : Type} [Fintype Ω]
    (perm : List BabyBear → List BabyBear) (RATE : Nat) (toNat : BabyBear → Nat)
    (params : FriParams) (vk : RecursionVk BabyBear) (checks : FriChecks BabyBear)
    (initState : List BabyBear) (logN : Nat) (pub : WrapPublics BabyBear)
    (enc : Ω → List BabyBear) (proofOf : Ω → BatchProofData BabyBear)
    (hcommit : ∀ ω, (proofOf ω).traceCommit = enc ω)
    (hrom : RomUniformDerive perm RATE initState enc)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (qp : VmConstraint2 → Polynomial BabyBear) (c : VmConstraint2) :
    winProb (fun ω =>
        verifyAlgoTB perm RATE toNat params vk checks initState logN (proofOf ω) pub
          && decide ((proofOf ω).oodPoint.headI ∈
              exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)))
      ≤ ((constraintPoly d t c - vanishingPoly t * qp c).natDegree : ℝ) / 2013265921 := by
  have h := ood_nonexceptionality_is_bounded perm RATE toNat params vk checks initState logN
    pub enc proofOf hcommit hrom (constraintPoly d t c - vanishingPoly t * qp c)
  rwa [show ((Fintype.card BabyBear : ℝ)) = 2013265921 by exact_mod_cast babybear_card] at h

/-- FIRE (concrete residual degree, bound in the unit interval): a degree-`≤ 4` residual (the
BabyBear quartic-extension shape) escapes with probability at most `4 / 2013265921` — a concrete
real number, and it genuinely lies in `[0,1]`. -/
theorem ood_escape_deg4_babybear {Ω : Type} [Fintype Ω]
    (perm : List BabyBear → List BabyBear) (RATE : Nat) (initState : List BabyBear)
    (enc : Ω → List BabyBear) (hrom : RomUniformDerive perm RATE initState enc)
    (R : Polynomial BabyBear) (hdeg : R.natDegree ≤ 4) :
    winProb (fun ω => oodNonExcAcc R (transcriptZeta perm RATE initState (enc ω)))
        ≤ 4 / 2013265921
      ∧ (0 : ℝ) ≤ 4 / 2013265921 ∧ (4 : ℝ) / 2013265921 ≤ 1 := by
  refine ⟨le_trans (deriveOod_escape_le_babybear perm RATE initState enc hrom R) ?_,
    by norm_num, by norm_num⟩
  gcongr
  exact_mod_cast hdeg

end BabyBear

/-! ## §6 — FIRE: both poles of the named residual AT THE REAL `deriveOod`, and tightness.

Everything here runs the ACTUAL sponge algorithm (`Challenger.observe`/`duplexing`/`sampleExt`)
over `ZMod 7`, RATE 1, observing the one-element commitment `[ω]`. With the identity permutation
the squeeze returns exactly the observed element (a bijection ⇒ `RomUniform` HOLDS); with a
constant permutation it is constant (⇒ `RomUniform` FAILS). So the named floor is neither
vacuously true nor vacuously false at the real algorithm, and the composed escape probability is
EXACTLY `deg/|F|` on a concrete instance. -/

section Fire

private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance : Inhabited (ZMod 7) := ⟨0⟩

/-- Running the REAL `deriveOod` with the identity permutation (RATE 1, init `[0]`) on the
commitment `[ω]` squeezes back exactly `ω` — computed by the kernel over all of `ZMod 7`. -/
theorem toyZeta_id : ∀ ω : ZMod 7,
    transcriptZeta (F := ZMod 7) id 1 [0] [ω] = ω := by decide

/-- **SATISFIABLE pole at the real squeeze**: for the identity permutation the derived ζ is a
bijection of the sampled commitment, so `RomUniformDerive` HOLDS — the named residual is
realizable by an actual run of the `deriveOod` algorithm, not just by an abstract map. -/
theorem romUniformDerive_id_perm_holds :
    RomUniformDerive (F := ZMod 7) (Ω := ZMod 7) id 1 [0] (fun ω => [ω]) := by
  show RomUniform (fun ω : ZMod 7 => transcriptZeta id 1 [0] [ω])
  have hz : (fun ω : ZMod 7 => transcriptZeta id 1 [0] [ω]) = fun ω => ω := by
    funext ω
    exact toyZeta_id ω
  rw [hz]
  exact romUniform_id

/-- Running the REAL `deriveOod` with the degenerate constant permutation `fun _ => [0]` squeezes
the constant `0` whatever was observed. -/
theorem toyZeta_const : ∀ ω : ZMod 7,
    transcriptZeta (F := ZMod 7) (fun _ => [0]) 1 [0] [ω] = 0 := by decide

/-- **REFUTABLE pole at the real squeeze**: the constant permutation makes the derived ζ constant,
and `RomUniformDerive` FAILS. The residual genuinely discriminates — assuming it for the deployed
Poseidon2 is a REAL idealization, with content. -/
theorem romUniformDerive_const_perm_fails :
    ¬ RomUniformDerive (F := ZMod 7) (Ω := ZMod 7) (fun _ => [0]) 1 [0] (fun ω => [ω]) := by
  intro h
  have h' : RomUniform (fun ω : ZMod 7 => transcriptZeta (fun _ => [0]) 1 [0] [ω]) := h
  have hz : (fun ω : ZMod 7 => transcriptZeta (fun _ => ([0] : List (ZMod 7))) 1 [0] [ω])
      = fun _ => (0 : ZMod 7) := by
    funext ω
    exact toyZeta_const ω
  rw [hz] at h'
  exact not_romUniform_const (0 : ZMod 7) (by rw [ZMod.card]; norm_num) h'

/-- **FIRE — the composed escape probability is EXACTLY `1/7`, tight against the bound.** At the
real `deriveOod` (identity permutation, `ZMod 7`) with residual `X` (degree 1), the
transcript-bound ζ lands exceptional with probability exactly `natDegree X / |F| = 1/7` — a
genuine positive real in `[0,1]`. The §2 bound is attained, so it is neither vacuous nor slack on
this instance. -/
theorem transcriptBound_escape_fires :
    winProb (fun ω : ZMod 7 =>
        oodNonExcAcc (X : Polynomial (ZMod 7)) (transcriptZeta id 1 [0] [ω])) = 1 / 7 := by
  have hz : (fun ω : ZMod 7 =>
        oodNonExcAcc (X : Polynomial (ZMod 7)) (transcriptZeta id 1 [0] [ω]))
      = oodNonExcAcc (X : Polynomial (ZMod 7)) := by
    funext ω
    exact congrArg _ (toyZeta_id ω)
  rw [hz]
  exact oodNonExc_winProb_fires

end Fire

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms winProb_mono
#assert_axioms romUniform_id
#assert_axioms romUniform_of_bijective
#assert_axioms not_romUniform_const
#assert_axioms transcriptBound_ood_escape_le
#assert_axioms deriveOod_escape_le
#assert_axioms ood_nonexceptionality_is_bounded
#assert_axioms deriveOod_escape_le_babybear
#assert_axioms hnonexc_clause_bounded_babybear
#assert_axioms ood_escape_deg4_babybear
#assert_axioms toyZeta_id
#assert_axioms romUniformDerive_id_perm_holds
#assert_axioms toyZeta_const
#assert_axioms romUniformDerive_const_perm_fails
#assert_axioms transcriptBound_escape_fires

end Dregg2.Circuit.OodRomBound
