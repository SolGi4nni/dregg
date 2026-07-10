import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.BabyBearFriSetup

/-!
# DEBT-A — a REAL `FriExtract` instance (rejecting verifier + contentful CVS), and the PRECISE
gap between `friProximity_discharge` and the extraction `FriExtract` demands.

**Honest scope (first sentence).** This file builds a genuinely NON-DEGENERATE `FriExtract` instance
over the deployed `babyBearFriSetup` — a native `verify` that REALLY REJECTS (witnessed by a far word
at a bad challenge, `verify_rejects_far`) and a `ChildVerifierSat` with genuine CONTENT (bound to the
transcript by `vkOf`/`piOf`, with an exhibited falsifier `cvs_falsifiable`), and it proves the extracted
honest child's oracle is genuinely low-degree via the PROVED `babyBear_friProximity_discharge` — but the
`∃ p` EXTRACTION in `FriExtract` is still discharged by the reflection assumption that a satisfied
in-circuit verifier CARRIES its transcript, NOT by `friProximity_discharge`; that residual reflection
obligation is the precise, named gap (`§4`), because `friProximity_discharge` consumes an EXPLICIT
transcript and yields a PROPERTY (soundness/proximity), whereas `FriExtract` consumes a PROPERTY (columns
satisfied) and must yield an EXPLICIT witness (knowledge-soundness/extraction) — the wrong direction.

This REDUCES the debt from the committed degenerate witness (`AggAirSound.wit_friExtract`, over
`witVerify = fun _ => true` and `witCVS = fun _ _ => True` — accept-everything ⊕ trivially-true) to the
SINGLE honest reflection obligation, and makes the vacuity of that degenerate witness VISIBLE as a
theorem (`§5`: the degenerate floor extracts a "verifying" child for EVERY `(c, s)` including absurd
ones, whereas the real floor cannot — `real_extract_not_total`).

Imports the committed FRI machinery PROVED; adds no `axiom`, no `sorry`, no `def …Hard`, re-assumes no
hypothesis. New module; NOT wired into `Dregg2.lean` (built directly).
-/

namespace Dregg2.Circuit.FriExtractReal

open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriSetup
open Dregg2.Circuit.FriSoundness

attribute [local instance] Classical.propDecidable

/-! ## §1. A child proof = a FRI transcript over the deployed setup, plus a native verifier.

A `ChildProof` bundles the committed low-degree oracle `f`, the fold challenge `α`, and the committed
folded oracle `f'`. The native `verify` runs the ACTUAL FRI query/final check on the whole domain
(`Fin 2`): every point passes the fold relation AND the final oracle is a codeword of `C'`. Over
BabyBear the field is noncomputable, so `verify` is a classical `Bool` — but it is a GENUINE predicate
that REJECTS (`verify_rejects_far`), not the committed `fun _ => true`. -/

/-- A child STARK/recursion proof, modeled as its FRI transcript over `babyBearFriSetup`. -/
structure ChildProof where
  /-- The committed domain oracle (the child's trace-derived low-degree function). -/
  f  : Fin 4 → BabyBear
  /-- The fold challenge. -/
  α  : BabyBear
  /-- The committed folded oracle. -/
  f' : Fin 2 → BabyBear

/-- **The real FRI acceptance predicate.** Every query point (all of `L² = Fin 2`) satisfies the fold
relation `f' y = Fold α f y`, AND the final oracle is a genuine codeword of the folded code `C'`. This
is the deterministic core of the FRI query phase (`FriSoundness.query_sound_of_cover` + the final
low-degree check), specialized to the full query set. -/
def friAccepts (p : ChildProof) : Prop :=
  (∀ y, p.f' y = Fold babyBearFriGeom p.α p.f y) ∧ p.f' ∈ babyBearFriSetup.C'

/-- **The native verifier** — a classical `Bool` (the field is noncomputable), TRUE exactly when the
FRI transcript accepts. Crucially NOT `fun _ => true`: `verify_rejects_far` exhibits a rejected proof. -/
noncomputable def verify (p : ChildProof) : Bool := if friAccepts p then true else false

theorem verify_iff (p : ChildProof) : verify p = true ↔ friAccepts p := by
  unfold verify; split <;> simp_all

/-! ## §2. The pinned commitment / exposed segment — read from the ORACLE, so `ChildVerifierSat`
is CONTENT, not `True`.

`vkOf` reads the child's VK-core commitment off the oracle; `piOf` reads the exposed segment. Because
they are functions of the transcript, the pinned `(c, s)` a node claims is BOUND to the proof — a `c`
outside their image is UNSATISFIABLE (`cvs_falsifiable`). Contrast the committed `witCVS = fun _ _ => True`
which every `(c, s)` satisfies. -/

/-- The child's VK-core commitment, read off the oracle (a nonneg value — an evaluation `.val`). -/
def vkOf (f : Fin 4 → BabyBear) : ℤ := ((f 0).val : ℤ)

/-- The child's exposed segment, read off the oracle. -/
def piOf (f : Fin 4 → BabyBear) : Seg :=
  { firstOld := ((f 0).val : ℤ), lastNew := ((f 1).val : ℤ), count := 0, acc := ((f 2).val : ℤ) }

/-- The pinned commitment / exposed segment the AIR reads for a child proof. -/
def vkCommit (p : ChildProof) : ℤ := vkOf p.f
def exposedPI (p : ChildProof) : Seg := piOf p.f

/-- **`ChildVerifierSat c s`** — the in-circuit child-verifier columns SATISFIED at pinned commitment
`c` claiming exposed segment `s`: there is an accepting FRI transcript whose oracle commits to `c` and
exposes `s`. CONTENTFUL — bound to a real accepting transcript AND to `(c, s) = (vkOf, piOf)`. -/
def ChildVerifierSat (c : ℤ) (s : Seg) : Prop :=
  ∃ p : ChildProof, friAccepts p ∧ vkOf p.f = c ∧ piOf p.f = s

/-! ## §3. THE REAL `FriExtract` INSTANCE — a rejecting verifier + a contentful CVS.

`FriExtract` holds over these carriers: a satisfied in-circuit verifier yields a genuinely `verify`-ing
child whose `vkCommit`/`exposedPI` are the pinned `c`/`s`. Honest reading: the extraction UNPACKS the
transcript the (contentful) CVS carries — see `§4` for exactly why `friProximity_discharge` does not
supply this existential. -/

theorem real_friExtract : FriExtract ChildProof verify vkCommit exposedPI ChildVerifierSat := by
  intro c s hcvs
  obtain ⟨p, hacc, hvk, hpi⟩ := hcvs
  exact ⟨p, (verify_iff p).mpr hacc, hvk, hpi⟩

/-! ### Non-degeneracy — the verifier REALLY rejects, and the CVS is REALLY contentful. -/

/-- A far word `fFar = ![1,0,0,0]` at the BAD challenge `α = 0`: the fold LEAVES `C'`. -/
noncomputable def farProof : ChildProof :=
  { f := fFar, α := 0, f' := Fold babyBearFriGeom 0 fFar }

/-- **`verify_rejects_far` (THE REJECTING TOOTH).** The native verifier REJECTS the far transcript:
`fFar` at `α = 0` folds to a non-constant oracle (`fFar_bad_alpha`), so the final low-degree check
fails. This is what the committed `witVerify = fun _ => true` provably CANNOT do. -/
theorem verify_rejects_far : verify farProof = false := by
  unfold verify
  rw [if_neg]
  rintro ⟨_, hmem⟩
  exact fFar_bad_alpha hmem

/-- **`cvs_falsifiable` (THE CONTENT TOOTH).** No pinned commitment `-1` is satisfiable: `vkOf` reads a
nonneg evaluation `.val`, so `ChildVerifierSat (-1) s` is FALSE for every `s`. So `ChildVerifierSat` is
NOT `fun _ _ => True` — it has genuine content, an exhibited unsatisfiable claim. -/
theorem cvs_falsifiable (s : Seg) : ¬ ChildVerifierSat (-1) s := by
  rintro ⟨p, _, hvk, _⟩
  have hnn : (0 : ℤ) ≤ vkOf p.f := by unfold vkOf; exact Int.natCast_nonneg _
  rw [hvk] at hnn
  norm_num at hnn

/-! ### The honest child extracts — and its oracle is genuinely LOW-DEGREE (the FRI payoff). -/

/-- The honest low-degree child: the codeword `fHonest = 2 + 3·pVal`, folded at `α = 0`. -/
noncomputable def honestProof : ChildProof :=
  { f := fHonest, α := 0, f' := Fold babyBearFriGeom 0 fHonest }

theorem verify_accepts_honest : verify honestProof = true := by
  rw [verify_iff]
  exact ⟨fun _ => rfl, fHonest_fold_mem 0⟩

/-- The honest node's in-circuit verifier is satisfied at its own pinned `(vkOf, piOf)`. -/
theorem cvs_honest : ChildVerifierSat (vkOf fHonest) (piOf fHonest) :=
  ⟨honestProof, ⟨fun _ => rfl, fHonest_fold_mem 0⟩, rfl, rfl⟩

/-- **`honest_extracts` (THE DISCHARGE FIRES).** `real_friExtract` fires on the honest node: a genuinely
`verify`-ing child proof exposing the pinned commitment and segment. A real, non-vacuous firing. -/
theorem honest_extracts :
    ∃ p, verify p = true ∧ vkCommit p = vkOf fHonest ∧ exposedPI p = piOf fHonest :=
  real_friExtract (vkOf fHonest) (piOf fHonest) cvs_honest

/-- **`extracted_is_low_degree` (THE PROXIMITY PAYOFF).** The extracted honest child's committed oracle
is `0`-close to the Reed-Solomon code — a GENUINE low-degree codeword — by the PROVED, field-instantiated
`babyBear_friProximity_discharge`. This is the crypto content the FRI machinery adds to the extraction:
the extracted child is proximate to the code, not garbage. -/
theorem extracted_is_low_degree : FriProximity babyBearFriSetup 0 honestProof.f :=
  babyBear_friProximity_discharge

/-- **`far_not_proximate` (PROXIMITY BITES).** The far word is NOT proximate: a `verify`-rejected oracle
is provably far from the code (`fFar_not_mem` via `closeN_zero_iff_mem`). So the proximity guarantee
distinguishes a genuine low-degree child from a far one — it is not vacuous. -/
theorem far_not_proximate : ¬ FriProximity babyBearFriSetup 0 fFar := by
  unfold FriProximity
  rw [closeN_zero_iff_mem]
  exact fFar_not_mem

/-! ## §4. THE PRECISE GAP between `friProximity_discharge` and `FriExtract`.

Both statements, quoted, with the difference NAMED:

`friProximity_discharge` (`FriSoundness.lean:409`, PROVED):
  `(Q : Finset κ) (hcover : disagree f' (Fold α f) ⊆ Q) (hpass : ∀ y ∈ Q, f' y = Fold α f y)`
  `(hfinal : f' ∈ S.C') (hgeneric : Fold α f ∈ S.C' → f ∈ S.C) → FriProximity S 0 f`
It CONSUMES an EXPLICIT transcript `(f, α, f', Q)` + its checks, and PRODUCES a PROPERTY of the oracle
(`f ∈ S.C`, i.e. proximity). It is SOUNDNESS: *given the transcript*, accept ⟹ low-degree.

`FriExtract` (`AggAirSound.lean:140`, the floor to discharge):
  `∀ c s, ChildVerifierSat c s → ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s`
It CONSUMES a PROPERTY (the verifier columns satisfied, `ChildVerifierSat c s`) and must PRODUCE an
EXPLICIT WITNESS (a child proof `p` whose NATIVE verifier passes with the pinned commit/seg). It is
KNOWLEDGE-SOUNDNESS / EXTRACTION.

**The named difference — DIRECTION.** `friProximity_discharge` goes transcript ⟶ property;
`FriExtract` goes property ⟶ transcript. Proximity PRESUPPOSES you already hold `(f, α, f', Q)` and its
Merkle openings; it never MANUFACTURES them from "the recursion-verifier subcircuit is satisfied." To
close `FriExtract` from FRI one additionally needs:
  (i)  **In-circuit ⇒ native reflection / knowledge extraction:** `ChildVerifierSat c s` (the AIR columns
       of the recursion-verifier chip) ⟹ ∃ the underlying transcript `(f, α, f', Q)` + its openings —
       the SNARK-of-a-fixed-verifier *knowledge* soundness, which `friProximity_discharge` does NOT give;
  (ii) **binding of the pinned `c`, `s`:** the extracted proof's `vkCommit`/`exposedPI` equal the pinned
       values — riding `FriSoundness.oracle_binding` (HashCR) for the commitment and the PI-exposure gate,
       again ABOVE FRI proximity.
`friProximity_discharge` discharges exactly ONE sub-obligation *inside* (i): once you hold the transcript,
an accepting generic run means the oracle is low-degree, so the sampled AIR checks bind the actual trace
(`FriSoundness.air_binds_of_proximity`). It supplies the PROXIMITY, never the EXISTENTIAL of the transcript.

`the_gap_is_reflection` makes the residual honest: this file's `real_friExtract` discharges the `∃ p` by
`ChildVerifierSat` CARRYING the transcript (`∃ p, friAccepts p ∧ …`) — i.e. it ASSUMES reflection (i);
that assumption is the whole residual gap. `bridged_extract` shows that once (i) is granted (as CVS's
`∃ p` here IS), the FRI payoff (ii-proximity) genuinely attaches. -/

/-- **`the_gap_is_reflection`.** The extraction the floor demands is exactly the reflection assumption:
`ChildVerifierSat c s` (this file's contentful CVS) already CONTAINS the child proof; `real_friExtract`
merely UNPACKS it. So the honest residual is: deriving `ChildVerifierSat`'s `∃ p` from raw AIR-column
satisfaction (knowledge extraction) — NOT provided by `friProximity_discharge`, which needs the
transcript as input. Stated as the literal equivalence extraction ⟺ CVS-carries-a-verifying-child. -/
theorem the_gap_is_reflection (c : ℤ) (s : Seg) :
    (∃ p : ChildProof, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s)
      ↔ ChildVerifierSat c s := by
  constructor
  · rintro ⟨p, hv, hvk, hpi⟩
    exact ⟨p, (verify_iff p).mp hv, hvk, hpi⟩
  · rintro ⟨p, hacc, hvk, hpi⟩
    exact ⟨p, (verify_iff p).mpr hacc, hvk, hpi⟩

/-- **`bridged_extract`.** GRANTING the reflection (i) — i.e. holding an accepting transcript for the
honest oracle, exactly what CVS carries — the FRI payoff attaches: the extracted child both `verify`s
AND its oracle is proximate to the code. The extraction and the proximity meet ONLY through the carried
transcript; proximity alone would not have produced the `∃ p`. -/
theorem bridged_extract :
    (∃ p, verify p = true ∧ vkCommit p = vkOf fHonest ∧ exposedPI p = piOf fHonest)
      ∧ FriProximity babyBearFriSetup 0 fHonest :=
  ⟨honest_extracts, babyBear_friProximity_discharge⟩

/-! ## §5. THE VACUITY TOOTH — the committed `witVerify = fun _ => true` witness, exposed.

The degenerate floor's premise `witCVS = fun _ _ => True` holds for EVERY `(c, s)`, and its verifier
accepts EVERYTHING, so it "extracts" a verifying child for every claim — INCLUDING absurd, time-reversed
segments. The real floor cannot: `real_extract_not_total`. -/

/-- An ABSURD exposed segment: `lastNew = -999 < 999 = firstOld` (time-reversed) — no honest child
exposes it. -/
def brokenSeg : Seg := { firstOld := 999, lastNew := -999, count := 0, acc := 0 }

/-- **`degenerate_extracts_absurd` (THE VACUITY, VISIBLE).** The committed degenerate floor certifies a
"verifying" child exposing the ABSURD `brokenSeg`: `witVerify` accepts the pair `(0, brokenSeg)` because
`witVerify = fun _ => true`, and it exposes `brokenSeg`. The floor asserts a genuine child for a claim no
sound verifier would accept — the exact hollowness `witVerify = fun _ => true` hides. -/
theorem degenerate_extracts_absurd :
    ∃ p, AggAirSound.witVerify p = true ∧ AggAirSound.witExposedPI p = brokenSeg :=
  ⟨(0, brokenSeg), rfl, rfl⟩

/-- **`degenerate_extract_total` (the degenerate floor is UNCONDITIONALLY total).** Because
`witVerify = fun _ => true` accepts everything, the degenerate carriers extract a verifying child for
EVERY `(c, s)` with NO premise — the `witCVS = True` guard carries no information. This totality IS the
vacuity: the "extraction" is free. -/
theorem degenerate_extract_total (c : ℤ) (s : Seg) :
    ∃ p, AggAirSound.witVerify p = true ∧ AggAirSound.witVkCommit p = c ∧ AggAirSound.witExposedPI p = s :=
  ⟨(c, s), rfl, rfl, rfl⟩

/-- **`real_extract_not_total` (the REAL floor is NOT vacuous).** The real carriers CANNOT extract a
verifying child unconditionally: the claim `c = -1` has NO child at all (`vkCommit` is a nonneg
evaluation), so the unconditional totality that the degenerate floor enjoys provably FAILS here. The
contrast is the whole point — a real verifier's acceptance is EARNED, not free. -/
theorem real_extract_not_total :
    ¬ ∀ (c : ℤ) (s : Seg), ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s := by
  intro htot
  obtain ⟨p, _, hvk, _⟩ := htot (-1) brokenSeg
  have hnn : (0 : ℤ) ≤ vkCommit p := by unfold vkCommit vkOf; exact Int.natCast_nonneg _
  rw [hvk] at hnn
  norm_num at hnn

/-! ## §6. Axiom hygiene — every result rests only on the kernel axioms (the imported FRI machinery is
PROVED and instantiated; the degenerate `witVerify`/`witCVS` are the committed defs, exposed not used). -/

#assert_axioms real_friExtract
#assert_axioms verify_rejects_far
#assert_axioms cvs_falsifiable
#assert_axioms honest_extracts
#assert_axioms extracted_is_low_degree
#assert_axioms far_not_proximate
#assert_axioms the_gap_is_reflection
#assert_axioms bridged_extract
#assert_axioms degenerate_extracts_absurd
#assert_axioms degenerate_extract_total
#assert_axioms real_extract_not_total

end Dregg2.Circuit.FriExtractReal
