/-
# `Dregg2.Circuit.CorrelatedAgreement.RlcDischarge` — the CA subtree's L5/L6 output CONSUMED:
`FriDeepQuotientRlc.RlcDistributes` DISCHARGED at the deployed extension code.

Rung L5·R4b of the FRI extractor ladder. Three files name the SAME hole from three sides and
none of them closes it:

* `FriDeepQuotientRlc.lean:543` states `RlcDistributes` and says, correctly, "NOT PROVED HERE,
  NOT AXIOMATIZED" — the ONE named hypothesis of the deployed DEEP-quotient argument.
* `FriDeployedExtCode.lean` supplies the extension TYPING (`deepCodeDeployedExt`) and records
  that `RlcDistributes` "is now instantiable at `deepCodeDeployedExt` … but nobody has proved it
  at those parameters".
* `CorrelatedAgreement/Theorems.lean` proves L5/L6 (`CorrelatedAgreementCurveUDParam(At)`) in the
  generic `Param` shape, including at `friCodeDeployedExt` — and has no consumer.

This file is the weld. `RlcDistributes` and `CorrelatedAgreementCurveUDParamAt` are, once the
two `closeN` vocabularies are identified (`Interface.closeN_coe_iff`, `Iff.rfl`), THE SAME
STATEMENT with `agree = n − r` and `L = thr`; §1 proves that, and §2 instantiates the proven CA
at the DEEP code `deepCodeDeployedExt = rsCode deployedPtsExt (2^21 − 1)` on the `2^24` domain.

## What is PROVED (no new hypothesis, no `sorry`, no axiom)

* §1 `rlcDistributes_of_curveUDParamAt` / `rlcDistributes_of_curveUDParam` — the bridge, generic
  in `(E, n, c, r, thr)`.
* §2 `rlcDistributes_deployed_ps` — **`RlcDistributes deepCodeDeployedExt 7340028 (psThreshold
  …) (2^24 − 7340028)` at EVERY batch width `c`, with ZERO hypotheses**, at the FULL deployed
  unique-decoding radius `r = 7340028` (doc §4's `e* − 4`). `rlcDistributes_deployed_classical`
  is the same at the TARGET threshold `(c−1)(r+1)` inside the classical radius.
* §3 `oodValues_correct_deployed_ps` / `_classical` — sub-piece 2's conclusion at the deployed
  instance with the CA hypothesis GONE: from committed columns `7340032`-close to degree
  `< 2^21` interpolants and an accepting reduced word at more than `psThreshold` challenges,
  EVERY claimed OOD value is the true value of the decoded column at `z`.
* §3b `deployed_good_card_le_ps` — the CONTRAPOSITIVE, which is the form Fiat–Shamir pricing
  consumes: a batch that is NOT simultaneously close has at most `psThreshold` good challenges,
  and `117440384 · 2⁹⁶ < |BB4|` (`deployed_alpha_price_arity8`) — the ≈ 96.8 bits, attached to
  the deployed DEEP code. (A ratio against the field size; the uniformity that would turn it into
  a probability is the separate ROM idealization, not supplied here.)
* §4 the arithmetic that makes §3 non-empty, and §5 a NON-DEGENERATE firing at `c = 2, r = 1`
  where the pre-existing discharge (`rlcDistributes_one_column`, `c = 1`) cannot reach, with the
  `r = 0` corner PROVEN FALSE on that instance (`fire_radius_zero_false`).

## NON-DEGENERACY (the acceptance test, stated plainly)

`m = 1` and `r = 0` are the corners every earlier CA object in this tree lived in. Nothing here
is at a corner:

* the deployed discharge holds at `r = 7340028 > 0` — the FULL UD radius, not a shave to zero —
  and at EVERY `c`, in particular `c = 8` (fold arity) and `c = 256` (batch width);
* the radius arithmetic §3 needs (`r + d + deg < n`) holds at the deployed numbers with exactly
  `5` of slack in the sum (`deployed_radius_slack`) — the CA-radius ceiling is `7340032` and
  fails at `7340033` (`deployed_radius_ceiling`), so it is a real fit, not a vacuous one;
* the challenge threshold is `117440384` at `c = 8` against `|BB4| = p⁴ ≈ 2^124`, and a good set
  that large EXISTS (`deployed_good_set_exists`) — the hypothesis is satisfiable, not empty;
* §5 fires at `c = 2` columns and radius `1`, and proves that the SAME conclusion at radius `0`
  is FALSE there.

## HONEST SCOPE

1. The `e`-closeness of the reduced word at more than `L` challenges is a HYPOTHESIS of §3, as it
   must be: it is what an accepting FRI run supplies. The completeness direction already in the
   tree (`deployed_deep_input_closeN_of_colsClose`) lands at radius `numCols · 7340032`, far
   outside UD — that theorem is not, and cannot be, the source of §3's `hgood`.
2. The residual band of `Theorems.lean` §5 is inherited verbatim: between the target threshold
   `(c−1)(r+1)` and `psThreshold` the conclusion is not proved at the full UD radius. At the
   deployed shape that band costs `< 1.2` bits, and it is the ONLY thing between this file and
   the target Props at their stated threshold at the deployed radius.
3. This closes `RlcDistributes`. It does NOT close `DecodedLdtLink`: the verifier-side wire
   (transcript ⟹ the oracle rows ARE the opened values, and the OOD point/values in the
   transcript ARE `z`/`vz`) is `DeployedTraceExtract`'s named residual, untouched here.

Additive new file; every import read-only. No `sorry`, no `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.CorrelatedAgreement.Theorems

namespace Dregg2.Circuit.CorrelatedAgreement.RlcDischarge

open Polynomial
open Dregg2.Circuit.FriSoundness (disagree)
open Dregg2.Circuit.FriDeepQuotientRlc (RlcDistributes colQuotWord friInputWord
  oodValues_correct_of_rlcDistributes)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (rsCode pR omega24 pR_deployed_inj)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.FriDeployedExtCode (BB4 bb4_card deployedPtsExt deployedPtsExt_inj
  deepCodeDeployedExt)

set_option linter.unusedSectionVars false

/-! ## §1 — THE BRIDGE: `RlcDistributes` IS the CA Prop, at `agree = n − r`, `L = thr`.

`RlcDistributes code d L agree u` (`FriDeepQuotientRlc.lean:543`) and
`CorrelatedAgreementCurveUDParamAt E n ↑code d c thr` (`Theorems.lean:314`) differ in exactly
two places: the CA Prop quantifies over the word family `u` (the RLC one fixes it), and the two
`closeN`s are the `hammingDist` and the `disagree` spelling of one predicate
(`Interface.closeN_coe_iff`, `Iff.rfl`). Nothing is reshaped and nothing is weakened. -/

section Bridge

variable {E : Type*} [Field E] [DecidableEq E]

/-- **THE BRIDGE.** The L5/L6 Prop at threshold `thr` gives `RlcDistributes` at list size `thr`
and agreement floor `n − r`, for EVERY word family. -/
theorem rlcDistributes_of_curveUDParamAt {n c r thr : ℕ} {code : Submodule E (Fin n → E)}
    (hCA : CorrelatedAgreementCurveUDParamAt E n (↑code : Set (Fin n → E)) r c thr)
    (u : Fin c → (Fin n → E)) :
    RlcDistributes code r thr (n - r) u := by
  intro Good hgood hL
  exact hCA u Good (fun α hα => (Interface.closeN_coe_iff code r _).mpr (hgood α hα)) hL

/-- The same at the TARGET threshold `(c−1)(r+1)` — the doc-§4 Prop, no threshold parameter. -/
theorem rlcDistributes_of_curveUDParam {n c r : ℕ} {code : Submodule E (Fin n → E)}
    (hCA : CorrelatedAgreementCurveUDParam E n (↑code : Set (Fin n → E)) r c)
    (u : Fin c → (Fin n → E)) :
    RlcDistributes code r ((c - 1) * (r + 1)) (n - r) u :=
  rlcDistributes_of_curveUDParamAt ((curveUDParamAt_target n _ r c).mpr hCA) u

end Bridge

/-! ## §2 — THE DEPLOYED DISCHARGE, at `deepCodeDeployedExt`.

`FriDeployedExtCode.deepCodeDeployedExt = rsCode deployedPtsExt (2^18·8 − 1)` — the DEEP-quotient
code, one degree below the committed code, on the embedded `2^24`-point domain, over the quartic
extension `BB4`. The CA `Param` form is field-generic and domain-generic, so it lands here with
only the RS-code vocabulary bridge. -/

section Deployed

/-- The DEEP code IS the Scaffolding RS code on the retyped domain (the `Theorems.lean`
`deployedExt_code_eq` bridge, one degree lower). -/
theorem deepCode_eq_RScode :
    (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4))
      = (RScode deployedPtsExt (2 ^ 18 * 8 - 1) : Set (Fin (8 * 2 ^ 21) → BB4)) := by
  rw [Interface.RScode_eq_rsCode (by norm_num) deployedPtsExt]
  rfl

/-- **L6 AT THE DEEP DEPLOYED CODE, classical regime** — the TARGET threshold `(m−1)(r+1)`, for
any radius inside `(m+1)·r + (2^21 − 1) ≤ 2^24`. -/
theorem curveUDParam_deepDeployed {r m : ℕ} (hm : 1 ≤ m)
    (hdist : (m + 1) * r + (2 ^ 18 * 8 - 1) ≤ 8 * 2 ^ 21) :
    CorrelatedAgreementCurveUDParam BB4 (8 * 2 ^ 21)
      (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) r m := by
  rw [deepCode_eq_RScode]
  exact curveUDParam_of_classical deployedPtsExt_inj hm hdist

/-- **L6 AT THE DEEP DEPLOYED CODE, PS regime, FULL UD RADIUS `r = 7340028`** — the L1→L2→L3.2
(Polishchuk–Spielman)→L4 composition fired at the deployed shape, for every arity `m`. -/
theorem curveUDParamAt_deepDeployed_ps (m : ℕ) :
    CorrelatedAgreementCurveUDParamAt BB4 (8 * 2 ^ 21)
      (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 7340028 m
      (psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 m) := by
  rw [deepCode_eq_RScode]
  exact curveUDParamAt_of_ps deployedPtsExt_inj (by norm_num) (by norm_num) (by norm_num)

/-- **⚑⚑ `RlcDistributes` DISCHARGED AT THE DEPLOYED PARAMETERS — no hypothesis at all.** At the
full unique-decoding radius `7340028`, for EVERY batch width `c` and every family of words: more
than `psThreshold` good challenges force a single family of DEEP-code codewords agreeing with all
`c` words simultaneously on `≥ 2^24 − 7340028 = 9437188` domain points. -/
theorem rlcDistributes_deployed_ps (c : ℕ) (u : Fin c → (Fin (8 * 2 ^ 21) → BB4)) :
    RlcDistributes deepCodeDeployedExt 7340028
      (psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 c) (8 * 2 ^ 21 - 7340028) u :=
  rlcDistributes_of_curveUDParamAt (curveUDParamAt_deepDeployed_ps c) u

/-- **`RlcDistributes` at the TARGET threshold** `(c−1)(r+1)`, inside the classical radius —
again with no hypothesis beyond the radius side condition. -/
theorem rlcDistributes_deployed_classical {r c : ℕ} (hc : 1 ≤ c)
    (hdist : (c + 1) * r + (2 ^ 18 * 8 - 1) ≤ 8 * 2 ^ 21)
    (u : Fin c → (Fin (8 * 2 ^ 21) → BB4)) :
    RlcDistributes deepCodeDeployedExt r ((c - 1) * (r + 1)) (8 * 2 ^ 21 - r) u :=
  rlcDistributes_of_curveUDParam (curveUDParam_deepDeployed hc hdist) u

/-- The deployed BATCH WIDTH `c = 256` at its classical ceiling `r = 57120`, target threshold. -/
theorem rlcDistributes_deployed_batch256 (u : Fin 256 → (Fin (8 * 2 ^ 21) → BB4)) :
    RlcDistributes deepCodeDeployedExt 57120 ((256 - 1) * (57120 + 1))
      (8 * 2 ^ 21 - 57120) u :=
  rlcDistributes_deployed_classical (by omega) (by norm_num) u

/-- The deployed FOLD ARITY `c = 8` at its classical ceiling `r = 1631118`, target threshold. -/
theorem rlcDistributes_deployed_arity8 (u : Fin 8 → (Fin (8 * 2 ^ 21) → BB4)) :
    RlcDistributes deepCodeDeployedExt 1631118 ((8 - 1) * (1631118 + 1))
      (8 * 2 ^ 21 - 1631118) u :=
  rlcDistributes_deployed_classical (by omega) (by norm_num) u

end Deployed

/-! ## §3 — THE PAYOFF: sub-piece 2's conclusion at the deployed instance, CA-hypothesis FREE.

`FriDeepQuotientRlc.oodValues_correct_of_rlcDistributes` derives "every claimed OOD value is the
true value of the decoded column at `z`" from `RlcDistributes` AND NOTHING ELSE. §2 supplies that
premise as a theorem, so the conclusion below carries no correlated-agreement assumption. -/

section Payoff

/-- **⚑⚑ THE DEPLOYED OOD-VALUE CORRECTNESS, WITH NO CA HYPOTHESIS.** Committed columns
`7340032`-close (the deployed UD radius) to degree-`< 2^21` interpolants, a valid out-of-domain
`z`, and a reduced word `7340028`-close to the DEEP code at more than `psThreshold` challenges
force every claimed OOD value to be the true one. Radius arithmetic:
`7340028 + 7340032 + (2^21 − 1) = 16777211 < 2^24` (`deployed_radius_slack`: 5 to spare). -/
theorem oodValues_correct_deployed_ps {c : ℕ}
    {z : BB4} (hz : ∀ x, deployedPtsExt x ≠ z)
    {M : MatrixOracle (Fin (8 * 2 ^ 21)) c BabyBear} {vz : Fin c → BB4}
    {p : Fin c → Polynomial BabyBear}
    (hcols : ∀ j, (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) (p j))).card ≤ 7340032)
    (hdeg : ∀ j, (p j).natDegree ≤ 2 ^ 18 * 8 - 1)
    (Good : Finset BB4)
    (hgood : ∀ α ∈ Good, Dregg2.Circuit.FriSoundness.closeN deepCodeDeployedExt 7340028
      (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz))
    (hL : psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 c < Good.card) :
    ∀ j, vz j = ((p j).map (algebraMap BabyBear BB4)).eval z :=
  oodValues_correct_of_rlcDistributes (D := 2 ^ 18 * 8 - 1) (d := 7340032) (e := 7340028)
    (m := 2 ^ 18 * 8 - 1) (agree := 8 * 2 ^ 21 - 7340028)
    pR_deployed_inj hz hcols hdeg (by norm_num) (le_refl _)
    (rlcDistributes_deployed_ps c _) Good hgood hL (by norm_num)

/-- The same at the TARGET threshold inside the classical radius — stated at the deployed batch
width `c = 256`, radius `57120`. -/
theorem oodValues_correct_deployed_batch256
    {z : BB4} (hz : ∀ x, deployedPtsExt x ≠ z)
    {M : MatrixOracle (Fin (8 * 2 ^ 21)) 256 BabyBear} {vz : Fin 256 → BB4}
    {p : Fin 256 → Polynomial BabyBear}
    (hcols : ∀ j, (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) (p j))).card ≤ 7340032)
    (hdeg : ∀ j, (p j).natDegree ≤ 2 ^ 18 * 8 - 1)
    (Good : Finset BB4)
    (hgood : ∀ α ∈ Good, Dregg2.Circuit.FriSoundness.closeN deepCodeDeployedExt 57120
      (friInputWord (pR 8 (2 ^ 21) omega24) α z M vz))
    (hL : (256 - 1) * (57120 + 1) < Good.card) :
    ∀ j, vz j = ((p j).map (algebraMap BabyBear BB4)).eval z :=
  oodValues_correct_of_rlcDistributes (D := 2 ^ 18 * 8 - 1) (d := 7340032) (e := 57120)
    (m := 2 ^ 18 * 8 - 1) (agree := 8 * 2 ^ 21 - 57120)
    pR_deployed_inj hz hcols hdeg (by norm_num) (le_refl _)
    (rlcDistributes_deployed_batch256 _) Good hgood hL (by norm_num)

end Payoff

/-! ## §3b — THE OPERATIONAL FORM: the CAP on good challenges, and what it prices.

A deployed verifier draws ONE `α`, not `psThreshold`-many. The form the Fiat–Shamir pricing
consumes is the CONTRAPOSITIVE (`Interface.curveGood_card_le`'s shape): a batch that is NOT
simultaneously close has at most `psThreshold` good challenges, so a uniformly drawn `α` is good
with probability at most `psThreshold / |BB4|`. That ratio is the per-batch soundness this whole
rung buys, and it is stated below as a machine-checked number, not an estimate. -/

section Cap

/-- **THE DEPLOYED CAP.** If the `c` committed DEEP-quotient words are NOT simultaneously
`7340028`-close to the DEEP code, at most `psThreshold` challenges are good. No hypothesis. -/
theorem deployed_good_card_le_ps {c : ℕ} (u : Fin c → (Fin (8 * 2 ^ 21) → BB4))
    (hfar : ¬ Interface.SimClose (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4))
      7340028 u) :
    (Interface.curveGood (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 7340028 u).card
      ≤ psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 c := by
  by_contra hcon
  rw [not_le] at hcon
  exact hfar (curveUDParamAt_deepDeployed_ps c u _
    (fun α hα => Interface.mem_curveGood.1 hα) hcon)

/-- The same at the TARGET threshold in the classical regime, deployed batch width `c = 256`. -/
theorem deployed_good_card_le_batch256 (u : Fin 256 → (Fin (8 * 2 ^ 21) → BB4))
    (hfar : ¬ Interface.SimClose (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4))
      57120 u) :
    (Interface.curveGood (↑deepCodeDeployedExt : Set (Fin (8 * 2 ^ 21) → BB4)) 57120 u).card
      ≤ (256 - 1) * (57120 + 1) :=
  Interface.curveGood_card_le (curveUDParam_deepDeployed (r := 57120) (m := 256)
    (by omega) (by norm_num)) hfar

/-- **⚑ WHAT IT PRICES — over 96 bits at the deployed fold arity.** The cap against the size of
the challenge field, as an integer inequality: `117440384 · 2⁹⁶ < |BB4| = p⁴ ≈ 2^123.6`. This is
the ≈ 96.8 bits `Theorems.lean` §5 quotes, now attached to the deployed DEEP code.

⚠ Read this at its resolution: it is a RATIO of the proven cap to the field size, NOT a
probability statement. Turning it into "a drawn `α` is good with probability ≤ this" needs the
challenge to be uniform, which is the separate Fiat–Shamir/ROM idealization (`OodRomBound`'s
`RomUniform` shape); nothing here supplies it. -/
theorem deployed_alpha_price_arity8 :
    psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 8 * 2 ^ 96 < Fintype.card BB4 := by
  rw [bb4_card]
  norm_num [psThreshold, babyBearP]

/-- …and it is TIGHT at that resolution: the same ratio is NOT below `2⁻⁹⁷`. The 96 is the real
number, not a rounded-down flourish. -/
theorem deployed_alpha_price_arity8_tight :
    ¬ (psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 8 * 2 ^ 97 < Fintype.card BB4) := by
  rw [bb4_card]
  norm_num [psThreshold, babyBearP]

end Cap

/-! ## §4 — NON-VACUITY OF THE DEPLOYED STATEMENT (the numbers, and that they are satisfiable). -/

section NonVacuity

-- The deployed parameters, pinned.
#guard 8 * 2 ^ 21 = 16777216
#guard 2 ^ 18 * 8 - 1 = 2097151
#guard 8 * 2 ^ 21 - 7340028 = 9437188
-- The PS thresholds at the DEEP code (one degree below the committed code).
#guard psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 2 = 16777197
#guard psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 8 = 117440384
#guard psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 256 = 4278185417
-- …against the TARGET threshold at the same radius (the residual band, `< 1.2` bits).
#guard (8 - 1) * (7340028 + 1) = 51380203
-- The classical ceilings actually used above.
#guard (8 + 1) * 1631118 + (2 ^ 18 * 8 - 1) ≤ 8 * 2 ^ 21
#guard (256 + 1) * 57120 + (2 ^ 18 * 8 - 1) ≤ 8 * 2 ^ 21

/-- **The §3 radius arithmetic is a REAL FIT, with 5 to spare** — at the full UD radius, the CA
agreement floor beats the commitment error plus the code's own degree budget by exactly `5`. -/
theorem deployed_radius_slack :
    7340028 + 7340032 + (2 ^ 18 * 8 - 1) + 5 = 8 * 2 ^ 21 := by norm_num

/-- …and the ceiling is REAL, not slack in the write-up: the §3 side condition holds at CA radius
`7340032` and FAILS at `7340033`. The deployed `7340028` clears it by exactly `4`. -/
theorem deployed_radius_ceiling :
    7340032 + 7340032 + (2 ^ 18 * 8 - 1) < 8 * 2 ^ 21 ∧
      ¬ (7340033 + 7340032 + (2 ^ 18 * 8 - 1) < 8 * 2 ^ 21) :=
  ⟨by norm_num, by norm_num⟩

/-- **The challenge threshold is satisfiable over the deployed field**: `|BB4| = p⁴ ≈ 2^124`
dwarfs `psThreshold … 8 = 117440384`, so the `hL` hypothesis of §3 is not empty. -/
theorem psThreshold_lt_card_bb4 :
    psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 256 < Fintype.card BB4 := by
  rw [bb4_card]
  norm_num [psThreshold, babyBearP]

/-- **A good set of the required size EXISTS** — the §3 hypothesis bundle is inhabited at the
deployed arity `c = 8`, not true by emptiness of `Good`. -/
theorem deployed_good_set_exists :
    ∃ Good : Finset BB4, psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 8 < Good.card := by
  have hle : psThreshold (8 * 2 ^ 21) (2 ^ 18 * 8 - 1) 7340028 8 + 1
      ≤ (Finset.univ : Finset BB4).card := by
    rw [Finset.card_univ, bb4_card]
    norm_num [psThreshold, babyBearP]
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq hle
  exact ⟨T, by omega⟩

end NonVacuity

/-! ## §5 — ⚑ THE FIRING, at `c = 2` columns and radius `1` — NOT a degenerate corner.

The pre-existing discharge of the `RlcDistributes` shape (`rlcDistributes_one_column`) is at
`c = 1`, where the RLC IS the column and correlated agreement buys nothing. Here it fires at
`c = 2` on the genuinely corrupted pair `Theorems.lean` §6 uses (`cw 0 = ![0,0,0,1]`, which is at
distance `≥ 1` from every codeword of `RS(4,1)/ZMod 5`), and the `r = 0` version of the SAME
conclusion is PROVEN FALSE on it. -/

section Fire

/-- `RScode pt5 1` and the deployed `rsCode pt5 1` are the same code. -/
theorem rscode_pt5_eq : (RScode pt5 1 : Set (Fin 4 → ZMod 5)) = (↑(rsCode pt5 1) : Set _) := by
  rw [Interface.RScode_eq_rsCode (by norm_num) pt5]

/-- **⚑ `RlcDistributes` FIRES AT TWO COLUMNS AND POSITIVE RADIUS** — `c = 2`, `r = 1`, list size
`(2−1)(1+1) = 2`, agreement floor `4 − 1 = 3`. `rlcDistributes_one_column` cannot state this. -/
theorem rlcDistributes_fires_two_columns :
    RlcDistributes (rsCode pt5 1) 1 ((2 - 1) * (1 + 1)) (4 - 1) cw :=
  rlcDistributes_of_curveUDParam (rscode_pt5_eq ▸ curveUDParam_fires) cw

/-- The firing APPLIED, with only three good challenges: a common agreement set of size `≥ 3`
for BOTH rows at once. -/
theorem rlcDistributes_fires_concrete :
    ∃ g : Fin 2 → Fin 4 → ZMod 5, (∀ j, g j ∈ rsCode pt5 1) ∧
      4 - 1 ≤ (Finset.univ.filter fun x => ∀ j, cw j x = g j x).card :=
  rlcDistributes_fires_two_columns {0, 1, 2}
    (fun α hα => (Interface.closeN_coe_iff (rsCode pt5 1) 1 _).mp
      (rscode_pt5_eq ▸ cw_close {0, 1, 2} α hα)) (by decide)

/-- **⚑ THE RADIUS IS LOAD-BEARING — the `r = 0` corner is FALSE here.** Full simultaneous
agreement (`4` of `4` points) would make `cw 0` a codeword of `RS(4,1)` (a constant), and it is
not. So §5's positive radius is doing real work, and this is not the degenerate instance every
earlier object in this area lived at. -/
theorem fire_radius_zero_false :
    ¬ ∃ g : Fin 2 → Fin 4 → ZMod 5, (∀ j, g j ∈ RScode pt5 1) ∧
      4 ≤ (Finset.univ.filter fun x => ∀ j, cw j x = g j x).card := by
  rintro ⟨g, hg, hcard⟩
  have hall : ∀ x : Fin 4, ∀ j : Fin 2, cw j x = g j x := by
    intro x j
    have huniv : (Finset.univ.filter fun x => ∀ j, cw j x = g j x)
        = (Finset.univ : Finset (Fin 4)) :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_filter_le _ _) hcard)
    have hx : x ∈ (Finset.univ.filter fun x => ∀ j, cw j x = g j x) := by
      rw [huniv]; exact Finset.mem_univ x
    exact (Finset.mem_filter.mp hx).2 j
  obtain ⟨q, hqdeg, hq⟩ := mem_RScode.mp (hg 0)
  have hC : q = Polynomial.C (q.coeff 0) := by
    rcases eq_or_ne q 0 with rfl | hq0
    · simp
    · have hnd : q.natDegree < 1 :=
        (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr (by simpa using hqdeg)
      exact Polynomial.eq_C_of_natDegree_le_zero (by omega)
  have hconst : ∀ x : Fin 4, cw 0 x = q.coeff 0 := by
    intro x
    rw [hall x 0, hq x, hC]
    simp
  have h0 : (cw 0 0 : ZMod 5) = q.coeff 0 := hconst 0
  have h3 : (cw 0 3 : ZMod 5) = q.coeff 0 := hconst 3
  have : (0 : ZMod 5) = 1 := by
    rw [show (0 : ZMod 5) = cw 0 0 from by decide, show (1 : ZMod 5) = cw 0 3 from by decide,
      h0, h3]
  exact absurd this (by decide)

end Fire

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [rlcDistributes_of_curveUDParamAt, rlcDistributes_of_curveUDParam,
  deepCode_eq_RScode, curveUDParam_deepDeployed, curveUDParamAt_deepDeployed_ps,
  rlcDistributes_deployed_ps, rlcDistributes_deployed_classical,
  rlcDistributes_deployed_batch256, rlcDistributes_deployed_arity8,
  oodValues_correct_deployed_ps, oodValues_correct_deployed_batch256,
  deployed_good_card_le_ps, deployed_good_card_le_batch256, deployed_alpha_price_arity8,
  deployed_alpha_price_arity8_tight,
  deployed_radius_slack, deployed_radius_ceiling, psThreshold_lt_card_bb4,
  deployed_good_set_exists, rscode_pt5_eq, rlcDistributes_fires_two_columns,
  rlcDistributes_fires_concrete, fire_radius_zero_false]

end Dregg2.Circuit.CorrelatedAgreement.RlcDischarge
