import Dregg2.Circuit.AggAirSound
import Dregg2.Circuit.BabyBearFriSetup

/-!
# A REAL rejecting FRI verifier over the deployed setup — the honest data behind extraction.

**Honest scope (first sentence).** This file builds a genuinely NON-DEGENERATE native `verify` over the
deployed `babyBearFriSetup` — one that REALLY REJECTS (witnessed by a far word at a bad challenge,
`verify_rejects_far`) — together with the transcript-bound readbacks `vkOf`/`piOf` and the honest child
(`honestProof`, `verify_accepts_honest`, `honest_extracts`), whose oracle is genuinely low-degree via the
PROVED `babyBear_friProximity_discharge` (`extracted_is_low_degree`). The real floor is NOT vacuous:
extraction cannot be unconditionally total (`real_extract_not_total`).

The reflexive extraction machinery that used to live here (`ChildVerifierSat` carrying its own
transcript, `real_friExtract`, `the_gap_is_reflection`) is SUPERSEDED by the non-circular extraction
core in `FriExtractNonCircular.lean`, which derives extraction from opened column data instead of
assuming reflection.

Imports the committed FRI machinery PROVED; adds no `axiom`, no `sorry`, no `def …Hard`, re-assumes no
hypothesis. Imported into `Dregg2.lean` (in the trusted closure).
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

/-! ## §2. The pinned commitment / exposed segment — read from the ORACLE.

`vkOf` reads the child's VK-core commitment off the oracle; `piOf` reads the exposed segment. Because
they are functions of the transcript, the pinned `(c, s)` a node claims is BOUND to the proof — a `c`
outside their image (e.g. `-1`) has no child at all (`real_extract_not_total`). -/

/-- The child's VK-core commitment, read off the oracle (a nonneg value — an evaluation `.val`). -/
def vkOf (f : Fin 4 → BabyBear) : ℤ := ((f 0).val : ℤ)

/-- The child's exposed segment, read off the oracle. -/
def piOf (f : Fin 4 → BabyBear) : Seg :=
  { firstOld := ((f 0).val : ℤ), lastNew := ((f 1).val : ℤ), count := 0, acc := ((f 2).val : ℤ) }

/-- The pinned commitment / exposed segment the AIR reads for a child proof. -/
def vkCommit (p : ChildProof) : ℤ := vkOf p.f
def exposedPI (p : ChildProof) : Seg := piOf p.f

/-! ### Non-degeneracy — the verifier REALLY rejects. -/

/-- A far word `fFar = ![1,0,0,0]` at the BAD challenge `α = 0`: the fold LEAVES `C'`. -/
noncomputable def farProof : ChildProof :=
  { f := fFar, α := 0, f' := Fold babyBearFriGeom 0 fFar }

/-- **`verify_rejects_far` (THE REJECTING TOOTH).** The native verifier REJECTS the far transcript:
`fFar` at `α = 0` folds to a non-constant oracle (`fFar_bad_alpha`), so the final low-degree check
fails. This is what an accept-everything `fun _ => true` verifier provably CANNOT do. -/
theorem verify_rejects_far : verify farProof = false := by
  unfold verify
  rw [if_neg]
  rintro ⟨_, hmem⟩
  exact fFar_bad_alpha hmem

/-! ### The honest child extracts — and its oracle is genuinely LOW-DEGREE (the FRI payoff). -/

/-- The honest low-degree child: the codeword `fHonest = 2 + 3·pVal`, folded at `α = 0`. -/
noncomputable def honestProof : ChildProof :=
  { f := fHonest, α := 0, f' := Fold babyBearFriGeom 0 fHonest }

theorem verify_accepts_honest : verify honestProof = true := by
  rw [verify_iff]
  exact ⟨fun _ => rfl, fHonest_fold_mem 0⟩

/-- **`honest_extracts` (THE DISCHARGE FIRES).** The honest node yields a genuinely `verify`-ing child
proof exposing the pinned commitment and segment: `honestProof` itself, accepted by
`verify_accepts_honest`, with both readbacks definitional. A real, non-vacuous firing. -/
theorem honest_extracts :
    ∃ p, verify p = true ∧ vkCommit p = vkOf fHonest ∧ exposedPI p = piOf fHonest :=
  ⟨honestProof, verify_accepts_honest, rfl, rfl⟩

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

/-! ## §5. THE NON-VACUITY TOOTH — extraction is EARNED, not free. -/

/-- An ABSURD exposed segment: `lastNew = -999 < 999 = firstOld` (time-reversed) — no honest child
exposes it. -/
def brokenSeg : Seg := { firstOld := 999, lastNew := -999, count := 0, acc := 0 }

/-- **`real_extract_not_total` (the REAL floor is NOT vacuous).** The real carriers CANNOT extract a
verifying child unconditionally: the claim `c = -1` has NO child at all (`vkCommit` is a nonneg
evaluation), so unconditional totality provably FAILS here. The point — a real verifier's acceptance is
EARNED, not free. -/
theorem real_extract_not_total :
    ¬ ∀ (c : ℤ) (s : Seg), ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s := by
  intro htot
  obtain ⟨p, _, hvk, _⟩ := htot (-1) brokenSeg
  have hnn : (0 : ℤ) ≤ vkCommit p := by unfold vkCommit vkOf; exact Int.natCast_nonneg _
  rw [hvk] at hnn
  norm_num at hnn

/-! ## §6. Axiom hygiene — every result rests only on the kernel axioms (the imported FRI machinery is
PROVED and instantiated). -/

#assert_axioms verify_rejects_far
#assert_axioms honest_extracts
#assert_axioms extracted_is_low_degree
#assert_axioms far_not_proximate
#assert_axioms real_extract_not_total

end Dregg2.Circuit.FriExtractReal
