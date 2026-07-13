/-
# FriExtract — a NON-CIRCULAR extraction core (DEBT-A, the reflection broken in two).

**Honest scope (first sentence).** This file replaces the circular extraction of
`FriExtractReal` — whose `ChildVerifierSat` (`FriExtractReal.lean:92`) is DEFINED to contain
the very `∃`-accepting-transcript the `FriExtract` floor must produce, so
`the_gap_is_reflection` (`:206`) is literally an `iff` — with a two-part decomposition:

  [real knowledge-extraction of the WITNESS POLYNOMIAL from opened column data]
      +  [ONE honestly-named transcript-assembly residual]

**The contentful predicate.** `ChildSatColumns k pts w Q` is stated over the ACTUAL opened
column data of the child-verifier chip: the committed column word `w`, the query sample `Q`
(opened values = `w ∘ Q`), the AIR/proximity fact — SOME `natDegree < k` polynomial lies
within the unique-decoding radius of `w` AND matches every opened value (exactly what the
FRI query-phase analysis certifies of the columns; an existential over a POLYNOMIAL, a
property-level object) — and the deployed sample-richness `k ≤ |queried points|`. It carries
NO transcript: no fold challenge, no folded oracle, no `friAccepts`, no `verify`.

**The knowledge-extraction core (PROVED).** `child_pins_unique_polynomial`: from
`ChildSatColumns` the low-degree polynomial EXISTS and is UNIQUE — uniqueness by
`openings_pin_polynomial` (the openings determine it) and, composed in
`child_pins_unique_polynomial_both` / `child_decoders_agree`, by
`decode_existsUnique`/`unique_nearest_codeword` (the ball determines it; the two decoders
AGREE). It is moreover COMPUTED: `child_extracted_eq_interpolant` pins it to
`extractColumnPoly` — the Lagrange interpolant of the opened values, a concrete extractor
running on column data alone. This is knowledge-extraction of the polynomial, not
reflection of a carried transcript: the `∃` the AIR fact supplies is upgraded to a unique,
computable witness.

**The residual (NAMED, not hidden).** `TranscriptOfPolynomial` is the single remaining
assumption: given the column-pinned polynomial (low-degree, in-radius, opening-consistent)
and the pinned `(c, s)` read off the column word (`vkOf`/`piOf`), an accepting FRI
transcript (`friAccepts`: fold challenge + folded oracle in `C'`) with that commitment and
exposure can be ASSEMBLED — the prover-simulation / FRI-completeness step, including
re-encoding the extracted polynomial onto the FRI evaluation domain and reproducing the
pinned `vkCommit`/`exposedPI` readings. `friExtract_from_columns` /
`friExtract_nonCircular` prove the `FriExtract`-shaped floor follows from
[`child_pins_unique_polynomial` + `TranscriptOfPolynomial`]; the residual is strictly
smaller than `ChildVerifierSat`'s whole-transcript reflection (the polynomial-knowledge
half is now a theorem, and `columns_cvs_not_reflection` exhibits data separating
`ColumnsCVS` from the extraction conclusion — no `iff`). `honest_transcript_of_polynomial`
DISCHARGES the residual on the honest setup-domain instance, giving a fully-proved
end-to-end non-circular extraction (`nonCircular_extract_fires`).

FIRE on concrete openings (the `RsUniqueDecoding`/`DecodeAgreesOpenings` fixtures —
`w4 = ![1,2,3,42]`, the codeword of `X + 1` with coordinate 3 GENUINELY corrupted): the
column predicate holds, pins `X + C 1` uniquely, and the extractor computes it. BITE:
pinning at commitment `-1` is unsatisfiable, and a 1-query sample provably fails the
predicate (`childSat_needs_sample`) — the sample-richness hypothesis is load-bearing.

No `axiom`, no `sorry`; every theorem `#assert_axioms`-clean.
-/
import Dregg2.Circuit.FriExtractReal
import Dregg2.Circuit.DecodeAgreesOpenings
import Dregg2.Circuit.NearDecodesWitness
import Dregg2.Tactics

namespace Dregg2.Circuit.FriExtractNonCircular

open Polynomial
open Dregg2.Circuit.RecursiveAggregation (Seg)
open Dregg2.Circuit.AggAirSound (FriExtract)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.BabyBearFriSetup
open Dregg2.Circuit.FriQuerySoundness (Accepts)
open Dregg2.Circuit.RsUniqueDecoding
open Dregg2.Circuit.DecodeAgreesOpenings
open Dregg2.Circuit.NearDecodesWitness
open Dregg2.Circuit.FriExtractReal

/-! ## §1 — `ChildSatColumns`: child-verifier satisfaction over the OPENED COLUMN DATA.

The data: the committed column word `w : Fin n → F` (the child's trace-column oracle), the
query sample `Q : Fin m → Fin n` (opened values are `w ∘ Q`), the code parameters
`(n, k)`. NO transcript is carried — contrast `FriExtractReal.ChildVerifierSat`, whose
definition is `∃ p : ChildProof, friAccepts p ∧ …` (an accepting transcript, the very
object `FriExtract` must produce). -/

/-- **`ChildSatColumns k pts w Q`** — the child-verifier columns SATISFIED, stated over the
opened column data alone:

* `proximity` — the AIR/proximity fact the FRI query phase certifies of the columns: SOME
  `natDegree < k` polynomial is within the unique-decoding radius of the committed word
  (`2·d + k ≤ n`) AND agrees with every opened value (`Accepts`). An existential over a
  POLYNOMIAL — a property-level low-degreeness fact about `w` — NOT over a transcript; no
  fold challenge, folded oracle, or acceptance bit appears.
* `sampleRich` — the deployed query sample touches at least `k` distinct field points, so
  the openings carry enough information to pin the polynomial
  (`underdetermined_openings_bite` shows this is load-bearing). -/
structure ChildSatColumns {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (w : Fin n → F) (Q : Fin m → Fin n) : Prop where
  proximity : ∃ p : Polynomial F, p.natDegree < k ∧
      2 * hammingDist w (evalVec pts p) + k ≤ n ∧ Accepts w (evalVec pts p) Q
  sampleRich : k ≤ (queriedPts pts Q).card

/-! ## §2 — THE NON-CIRCULAR CORE: column satisfaction pins a UNIQUE polynomial.

The extracted witness polynomial EXISTS and is UNIQUE — determined by the opened data, not
reflected from a carried transcript. Uniqueness holds through BOTH committed bricks: the
openings pin it (`openings_pin_polynomial`) and the unique-decoding ball pins it
(`decode_existsUnique` / `unique_nearest_codeword`), and the two decoders agree. -/

/-- **`child_pins_unique_polynomial` (THE CORE).** From `ChildSatColumns` alone: EXACTLY ONE
`natDegree < k` polynomial is in-radius and opening-consistent. Existence is the AIR
proximity fact; uniqueness is `openings_pin_polynomial` on the `≥ k` distinct queried
points — the openings DETERMINE the extracted polynomial. -/
theorem child_pins_unique_polynomial {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (w : Fin n → F) {Q : Fin m → Fin n}
    (hsat : ChildSatColumns k pts w Q) :
    ∃! p : Polynomial F, p.natDegree < k ∧
      2 * hammingDist w (evalVec pts p) + k ≤ n ∧ Accepts w (evalVec pts p) Q := by
  obtain ⟨p, hpd, hball, hacc⟩ := hsat.proximity
  refine ⟨p, ⟨hpd, hball, hacc⟩, ?_⟩
  rintro q ⟨hqd, -, hqacc⟩
  exact openings_pin_polynomial pts w hqd hpd hsat.sampleRich hqacc hacc

/-- **Ball-route pinning.** The same unique witness through `decode_existsUnique`: the
in-radius `natDegree < k` polynomial is unique with NO reference to the openings — the
unique-decoding radius alone already determines it. -/
theorem child_pins_in_ball {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F)
    {Q : Fin m → Fin n} (hsat : ChildSatColumns k pts w Q) :
    ∃! p : Polynomial F,
      p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k ≤ n := by
  obtain ⟨p, hpd, hball, -⟩ := hsat.proximity
  exact decode_existsUnique pts hinj w ⟨p, hpd, hball⟩

/-- **The two decoders AGREE.** Under `ChildSatColumns`, any in-ball low-degree `p` and any
opening-consistent low-degree `q` are EQUAL: the ball-decoder
(`unique_nearest_codeword`) and the openings-decoder (`openings_pin_polynomial`) return
the same polynomial — the composition the survey asked for. -/
theorem child_decoders_agree {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F)
    {Q : Fin m → Fin n} (hsat : ChildSatColumns k pts w Q)
    {p q : Polynomial F} (hp : p.natDegree < k) (hq : q.natDegree < k)
    (hpball : 2 * hammingDist w (evalVec pts p) + k ≤ n)
    (hqacc : Accepts w (evalVec pts q) Q) :
    p = q := by
  obtain ⟨r, hrd, hrball, hracc⟩ := hsat.proximity
  have h₁ : p = r := unique_nearest_codeword pts hinj w hp hrd hpball hrball
  have h₂ : q = r := openings_pin_polynomial pts w hq hrd hsat.sampleRich hqacc hracc
  rw [h₁, h₂]

/-- **Strong pinning (both scopes at once).** The extracted polynomial is unique among ALL
in-ball low-degree candidates AND among ALL opening-consistent low-degree candidates —
`unique_nearest_codeword` + `openings_pin_polynomial` composed on one witness. -/
theorem child_pins_unique_polynomial_both {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F)
    {Q : Fin m → Fin n} (hsat : ChildSatColumns k pts w Q) :
    ∃ p : Polynomial F,
      (p.natDegree < k ∧ 2 * hammingDist w (evalVec pts p) + k ≤ n ∧
        Accepts w (evalVec pts p) Q) ∧
      (∀ q : Polynomial F, q.natDegree < k →
        2 * hammingDist w (evalVec pts q) + k ≤ n → q = p) ∧
      (∀ q : Polynomial F, q.natDegree < k → Accepts w (evalVec pts q) Q → q = p) := by
  obtain ⟨p, hpd, hball, hacc⟩ := hsat.proximity
  refine ⟨p, ⟨hpd, hball, hacc⟩, ?_, ?_⟩
  · intro q hqd hqball
    exact unique_nearest_codeword pts hinj w hqd hpd hqball hball
  · intro q hqd hqacc
    exact openings_pin_polynomial pts w hqd hpd hsat.sampleRich hqacc hacc

/-- The core at the SHIPPED query count: sample length is literally
`plonky3ProverParams.numQueries` (`= 38`, `circuit/src/plonky3_prover.rs:99`). Pure
instantiation of `child_pins_unique_polynomial` over the deployed prover field. -/
theorem child_pins_unique_polynomial_deployed38 {n : ℕ} (k : ℕ)
    (pts : Fin n → BabyBear) (w : Fin n → BabyBear)
    {Q : Fin (Dregg2.Circuit.DeployedUdrRegime.plonky3ProverParams.numQueries) → Fin n}
    (hsat : ChildSatColumns k pts w Q) :
    ∃! p : Polynomial BabyBear, p.natDegree < k ∧
      2 * hammingDist w (evalVec pts p) + k ≤ n ∧ Accepts w (evalVec pts p) Q :=
  child_pins_unique_polynomial k pts w hsat

/-! ## §3 — The extractor is a CONCRETE ALGORITHM on the opened data.

Not just `∃!`: the pinned polynomial IS the Lagrange interpolant of the opened values —
a function of the column data alone. Knowledge-extraction = interpolation. -/

/-- The concrete extractor: Lagrange-interpolate the opened column values on the queried
coordinate set. A function of `(pts, w, Q)` only — no transcript input. -/
noncomputable def extractColumnPoly {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (pts : Fin n → F) (w : Fin n → F) (Q : Fin m → Fin n) : Polynomial F :=
  Lagrange.interpolate ((Finset.univ.image Q).image pts) id (extendWord pts w)

/-- The queried point set is the `pts`-image of the queried coordinate set. -/
theorem queriedPts_eq {F : Type*} [DecidableEq F] {n m : ℕ}
    (pts : Fin n → F) (Q : Fin m → Fin n) :
    queriedPts pts Q = (Finset.univ.image Q).image pts := by
  rw [Finset.image_image]
  rfl

/-- **The pinned polynomial is COMPUTED by the extractor.** Any `natDegree < k` polynomial
consistent with the openings (on a `≥ k`-point sample) equals `extractColumnPoly` — the
Lagrange interpolant of the opened values (`decoded_eq_interpolant` on the queried
coordinate set). The unique witness of §2 is therefore extractor output, not a choice. -/
theorem child_extracted_eq_interpolant {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}
    (k : ℕ) (pts : Fin n → F) (hinj : Function.Injective pts) (w : Fin n → F)
    {Q : Fin m → Fin n} (hcard : k ≤ (queriedPts pts Q).card)
    {p : Polynomial F} (hp : p.natDegree < k) (hacc : Accepts w (evalVec pts p) Q) :
    p = extractColumnPoly pts w Q := by
  have hkS : k ≤ (Finset.univ.image Q).card := by
    refine le_trans hcard ?_
    rw [queriedPts_eq]
    exact Finset.card_image_le
  unfold extractColumnPoly
  refine decoded_eq_interpolant pts hinj w hp (Finset.univ.image Q) hkS ?_
  intro i hi
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
  exact (hacc j).symm

/-! ## §4 — The NAMED residual, and the `FriExtract`-shaped floor from core + residual.

Everything below is at the deployed carriers of `FriExtractReal` (`ChildProof` over
`babyBearFriSetup`, column words on `Fin 4 → BabyBear`), so the conclusion is literally
the committed `FriExtract` shape. -/

/-- The pinned commitment / exposed segment, read off the COLUMN WORD — the same readers
(`vkOf`/`piOf`) `FriExtractReal` applies to the transcript oracle, here applied to the
column data the chip actually holds. -/
def ColumnsPinned (w : Fin 4 → BabyBear) (c : ℤ) (s : Seg) : Prop :=
  vkOf w = c ∧ piOf w = s

/-- **`TranscriptOfPolynomial` — THE RESIDUAL, named.** What transcript-assembly still
assumes: for every `(c, s)` and every polynomial `p` that the COLUMNS pin (low-degree,
within the unique-decoding radius of the column word, consistent with every opening) with
`(c, s)` read off the column word, an ACCEPTING FRI transcript exists (`friAccepts`: a
fold challenge and a folded oracle in `C'`) whose oracle reproduces the pinned commitment
and exposed segment. This is the prover-simulation / FRI-completeness step — assembling
`π` from the KNOWN polynomial — plus the commitment-binding that the assembled oracle
reads back `(c, s)`. It consumes a POLYNOMIAL (already knowledge-extracted by §2), NOT a
satisfaction property; that is what makes it strictly smaller than `ChildVerifierSat`'s
whole-transcript reflection. Discharged below on the honest instance
(`honest_transcript_of_polynomial`); open in general. -/
def TranscriptOfPolynomial (k : ℕ) (pts : Fin 4 → BabyBear) (w : Fin 4 → BabyBear)
    {m : ℕ} (Q : Fin m → Fin 4) : Prop :=
  ∀ (c : ℤ) (s : Seg) (p : Polynomial BabyBear),
    p.natDegree < k →
    2 * hammingDist w (evalVec pts p) + k ≤ 4 →
    Accepts w (evalVec pts p) Q →
    ColumnsPinned w c s →
    ∃ π : ChildProof, friAccepts π ∧ vkOf π.f = c ∧ piOf π.f = s

/-- **`ColumnsCVS`** — the column-level child-verifier-satisfaction predicate for the
`FriExtract` floor: SOME column word satisfies `ChildSatColumns` and pins `(c, s)`. The
existential is over a WORD (column data) — it carries proximity and openings facts, never
a fold challenge, folded oracle, or acceptance. Contrast `ChildVerifierSat c s =
∃ p : ChildProof, friAccepts p ∧ …`. -/
def ColumnsCVS (k : ℕ) (pts : Fin 4 → BabyBear) {m : ℕ} (Q : Fin m → Fin 4)
    (c : ℤ) (s : Seg) : Prop :=
  ∃ w : Fin 4 → BabyBear, ChildSatColumns k pts w Q ∧ ColumnsPinned w c s

/-- **Core + residual ⟹ extraction (per column word).** From `ChildSatColumns` the §2 core
pins THE unique polynomial; the named residual assembles its transcript; `verify_iff`
converts acceptance to the native verifier bit. The `FriExtract`-shaped conclusion, with
the reflection replaced by [proved knowledge-extraction] + [named assembly residual]. -/
theorem friExtract_from_columns {m : ℕ} (k : ℕ) (pts : Fin 4 → BabyBear)
    (w : Fin 4 → BabyBear) {Q : Fin m → Fin 4} (c : ℤ) (s : Seg)
    (hsat : ChildSatColumns k pts w Q) (hpin : ColumnsPinned w c s)
    (hTP : TranscriptOfPolynomial k pts w Q) :
    ∃ π : ChildProof, verify π = true ∧ vkCommit π = c ∧ exposedPI π = s := by
  obtain ⟨p, ⟨hpd, hball, hacc⟩, -⟩ := child_pins_unique_polynomial k pts w hsat
  obtain ⟨π, hπacc, hπvk, hπpi⟩ := hTP c s p hpd hball hacc hpin
  exact ⟨π, (verify_iff π).mpr hπacc, hπvk, hπpi⟩

/-- **The `FriExtract` instance itself.** Over the REAL carriers (`ChildProof`, the
genuinely-rejecting `verify`, `vkCommit`, `exposedPI`) with the COLUMN-LEVEL `ColumnsCVS`:
granting only the named residual (for each column word), the committed `FriExtract` floor
holds. The extraction direction property ⟶ witness is now: columns ⟶ (unique polynomial,
PROVED) ⟶ (transcript, residual). -/
theorem friExtract_nonCircular {m : ℕ} (k : ℕ) (pts : Fin 4 → BabyBear)
    (Q : Fin m → Fin 4)
    (hTP : ∀ w : Fin 4 → BabyBear, TranscriptOfPolynomial k pts w Q) :
    FriExtract ChildProof verify vkCommit exposedPI (ColumnsCVS k pts Q) := by
  rintro c s ⟨w, hsat, hpin⟩
  exact friExtract_from_columns k pts w c s hsat hpin (hTP w)

/-! ## §5 — TEETH: the new predicate has content, needs its hypotheses, and is NOT the
reflection. -/

/-- **Content tooth.** No column word pins commitment `-1` (`vkOf` reads a nonneg
evaluation `.val`), so `ColumnsCVS k pts Q (-1) s` is FALSE for every `s` — the predicate
is falsifiable, not `fun _ _ => True`. -/
theorem columnsCVS_falsifiable {m : ℕ} (k : ℕ) (pts : Fin 4 → BabyBear)
    (Q : Fin m → Fin 4) (s : Seg) : ¬ ColumnsCVS k pts Q (-1) s := by
  rintro ⟨w, -, hvk, -⟩
  have hnn : (0 : ℤ) ≤ vkOf w := by unfold vkOf; exact Int.natCast_nonneg _
  rw [hvk] at hnn
  norm_num at hnn

/-- **Sample tooth.** A 1-query sample can NEVER satisfy `ChildSatColumns` at `k = 2`: it
touches at most one field point, below the pinning threshold — `sampleRich` is
load-bearing (it is exactly what rules out the `underdetermined_openings_bite` regime). -/
theorem childSat_needs_sample (w : Fin 4 → BabyBear) :
    ¬ ChildSatColumns 2 pts4 w Q1 := by
  intro hsat
  have hrich := hsat.sampleRich
  have hle : (queriedPts pts4 Q1).card ≤ 1 := by
    have h : (queriedPts pts4 Q1).card ≤ (Finset.univ : Finset (Fin 1)).card :=
      Finset.card_image_le
    simpa using h
  omega

/-- **NOT the reflection.** `FriExtractReal.the_gap_is_reflection` proved extraction ⟺
`ChildVerifierSat` — a literal `iff`, for ALL `(c, s)`. Here the analogous `iff` FAILS:
there is a `(c, s)` where the extraction conclusion HOLDS (the honest child,
`honest_extracts`) but `ColumnsCVS` (on the undersized sample) is FALSE. The column
predicate is a genuinely different — strictly stronger-premised — object than the
conclusion it feeds, not a definitional unpacking of it. -/
theorem columns_cvs_not_reflection :
    (∃ π : ChildProof, verify π = true ∧
        vkCommit π = vkOf fHonest ∧ exposedPI π = piOf fHonest) ∧
      ¬ ColumnsCVS 2 pts4 Q1 (vkOf fHonest) (piOf fHonest) := by
  refine ⟨honest_extracts, ?_⟩
  rintro ⟨w, hsat, -⟩
  exact childSat_needs_sample w hsat

/-! ## §6 — FIRE on concrete openings: the corrupted-word fixtures.

`pts4 = ![0,1,2,3]`, `w4 = ![1,2,3,42]` (the codeword of `X + 1` with coordinate 3
GENUINELY corrupted, `w4_corrupted`), sample `Q3 = ![0,1,2]`. Every §1–§3 hypothesis is
discharged on this data. -/

/-- **FIRE (the predicate holds on real column data).** The corrupted word `w4` with the
3-query sample satisfies `ChildSatColumns` at `(n, k) = (4, 2)`: proximity witnessed by
`X + C 1` (degree 1, distance 1, radius `2·1 + 2 ≤ 4`, openings pass — `fire_accepts`),
sample touches 3 ≥ 2 points (`fire_queried_card`). -/
theorem fire_childSat : ChildSatColumns 2 pts4 w4 Q3 :=
  ⟨⟨X + C 1, by rw [natDegree_X_add_C]; norm_num,
      by rw [evalVec_pts4_XaddOne, w4_dist], fire_accepts⟩,
    by rw [fire_queried_card]; norm_num⟩

/-- **FIRE (the core fires).** On the corrupted column data, EXACTLY ONE `natDegree < 2`
polynomial is in-radius and opening-consistent — `child_pins_unique_polynomial` with every
hypothesis concrete. -/
theorem fire_child_pins :
    ∃! p : Polynomial BabyBear, p.natDegree < 2 ∧
      2 * hammingDist w4 (evalVec pts4 p) + 2 ≤ 4 ∧ Accepts w4 (evalVec pts4 p) Q3 :=
  child_pins_unique_polynomial 2 pts4 w4 fire_childSat

/-- **FIRE (ball route).** The same data through `decode_existsUnique`: the in-radius
witness is unique with no reference to the openings. -/
theorem fire_in_ball :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ∧ 2 * hammingDist w4 (evalVec pts4 p) + 2 ≤ 4 :=
  child_pins_in_ball 2 pts4 pts4_injective w4 fire_childSat

/-- **FIRE (the pinned VALUE).** Any in-radius `natDegree < 2` polynomial IS `X + C 1` —
the two decoders agree on the corrupted data (`child_decoders_agree`, with the openings
side held by `fire_accepts`). The extracted witness is FORCED, not chosen. -/
theorem fire_pinned_value {p : Polynomial BabyBear} (hpd : p.natDegree < 2)
    (hball : 2 * hammingDist w4 (evalVec pts4 p) + 2 ≤ 4) :
    p = X + C 1 := by
  refine child_decoders_agree 2 pts4 pts4_injective w4 fire_childSat hpd ?_ hball
    fire_accepts
  rw [natDegree_X_add_C]
  norm_num

/-- **FIRE (the extractor computes it).** The concrete extractor output on the opened
column data `(pts4, w4, Q3)` IS `X + C 1` — through `child_extracted_eq_interpolant`,
i.e. the pinned polynomial is literally the Lagrange interpolant of the three opened
values. -/
theorem fire_extractor : extractColumnPoly pts4 w4 Q3 = X + C 1 :=
  (child_extracted_eq_interpolant 2 pts4 pts4_injective w4
    (by rw [fire_queried_card]; norm_num)
    (by rw [natDegree_X_add_C]; norm_num) fire_accepts).symm

/-! ## §7 — FIRE end-to-end: the honest instance, residual DISCHARGED.

Over the FRI setup domain itself (`pts := pVal`, the order-4 subgroup `{1, i, -1, -i}`):
the honest column word is `fHonest = 2 + 3·pVal`, i.e. the evaluations of the polynomial
`pHon = C 2 + C 3·X` at `pVal`. Here `TranscriptOfPolynomial` is PROVED (the honest
transcript `honestProof` assembles), so the whole non-circular chain closes with zero
assumptions: columns ⟶ unique polynomial (§2) ⟶ transcript (residual, discharged) ⟶
`verify = true`. -/

/-- The honest witness polynomial: `pHon = 2 + 3·X`, whose `pVal`-evaluations are exactly
`fHonest`. -/
noncomputable def pHon : Polynomial BabyBear := C 2 + C 3 * X

theorem pHon_natDegree_lt : pHon.natDegree < 2 := by
  have h : pHon.natDegree ≤ 1 := by unfold pHon; compute_degree
  omega

/-- `pHon`'s codeword on the setup domain IS the honest oracle `fHonest`. -/
theorem evalVec_pVal_pHon : evalVec pVal pHon = fHonest := by
  funext x
  simp [evalVec, pHon, fHonest]

/-- The honest 2-query sample: positions `0, 1` of the setup domain. -/
def QH : Fin 2 → Fin 4 := ![0, 1]

/-- The honest sample touches 2 distinct field points (`pVal 0 = 1 ≠ i = pVal 1`). -/
theorem QH_sampleRich : 2 ≤ (queriedPts pVal QH).card := by
  have hne : pVal (QH 0) ≠ pVal (QH 1) := by decide
  have hsub : ({pVal (QH 0), pVal (QH 1)} : Finset BabyBear) ⊆ queriedPts pVal QH := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · subst h; exact mem_queriedPts pVal QH 0
    · rw [Finset.mem_singleton] at h
      subst h; exact mem_queriedPts pVal QH 1
  have hcard : ({pVal (QH 0), pVal (QH 1)} : Finset BabyBear).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  omega

/-- **FIRE (honest columns satisfy).** The honest column word over the setup domain
satisfies `ChildSatColumns`: `pHon` at distance 0, openings trivially consistent. -/
theorem honest_childSat : ChildSatColumns 2 pVal fHonest QH :=
  ⟨⟨pHon, pHon_natDegree_lt,
      by rw [evalVec_pVal_pHon, hammingDist_self]; omega,
      fun _ => by rw [evalVec_pVal_pHon]⟩,
    QH_sampleRich⟩

/-- **THE RESIDUAL, DISCHARGED at the honest instance.** For the honest column word the
transcript-assembly assumption is a THEOREM: the honest transcript `honestProof`
(`fHonest` folded at `α = 0`, final oracle a genuine `C'` codeword — `fHonest_fold_mem`)
accepts and reads back the pinned `(c, s)`. So `TranscriptOfPolynomial` is satisfiable —
a real obligation with real instances, not an unfalsifiable placeholder. -/
theorem honest_transcript_of_polynomial : TranscriptOfPolynomial 2 pVal fHonest QH := by
  rintro c s _p - - - ⟨hc, hs⟩
  exact ⟨honestProof, ⟨fun _ => rfl, fHonest_fold_mem 0⟩, hc, hs⟩

/-- The honest columns pin `(vkOf fHonest, piOf fHonest)` at the column level. -/
theorem honest_columnsCVS :
    ColumnsCVS 2 pVal QH (vkOf fHonest) (piOf fHonest) :=
  ⟨fHonest, honest_childSat, rfl, rfl⟩

/-- **FIRE (END-TO-END, ZERO ASSUMPTIONS).** The full non-circular extraction chain closed
on the honest instance: column satisfaction (`honest_childSat`) ⟶ the §2 core pins the
unique polynomial ⟶ the DISCHARGED residual assembles its transcript ⟶ a genuinely
`verify`-ing child with the pinned commitment and segment. Same conclusion as
`FriExtractReal.honest_extracts`, but derived from OPENED COLUMN DATA through
`friExtract_from_columns` — no carried transcript in the premise. -/
theorem nonCircular_extract_fires :
    ∃ π : ChildProof, verify π = true ∧
      vkCommit π = vkOf fHonest ∧ exposedPI π = piOf fHonest :=
  friExtract_from_columns 2 pVal fHonest (vkOf fHonest) (piOf fHonest)
    honest_childSat ⟨rfl, rfl⟩ honest_transcript_of_polynomial

/-- **FIRE (knowledge is real).** Two honest openings FORCE the witness polynomial: any
`natDegree < 2` polynomial consistent with the opened values of `fHonest` on `QH` IS
`pHon` — the extractor recovers the honest prover's polynomial from the openings alone. -/
theorem honest_extracted_poly_unique {p : Polynomial BabyBear} (hpd : p.natDegree < 2)
    (hacc : Accepts fHonest (evalVec pVal p) QH) : p = pHon :=
  openings_pin_polynomial pVal fHonest hpd pHon_natDegree_lt QH_sampleRich hacc
    (fun _ => by rw [evalVec_pVal_pHon])

/-! ## §8 — Axiom hygiene: every theorem kernel-clean. -/

#assert_axioms child_pins_unique_polynomial
#assert_axioms child_pins_in_ball
#assert_axioms child_decoders_agree
#assert_axioms child_pins_unique_polynomial_both
#assert_axioms child_pins_unique_polynomial_deployed38
#assert_axioms queriedPts_eq
#assert_axioms child_extracted_eq_interpolant
#assert_axioms friExtract_from_columns
#assert_axioms friExtract_nonCircular
#assert_axioms columnsCVS_falsifiable
#assert_axioms childSat_needs_sample
#assert_axioms columns_cvs_not_reflection
#assert_axioms fire_childSat
#assert_axioms fire_child_pins
#assert_axioms fire_in_ball
#assert_axioms fire_pinned_value
#assert_axioms fire_extractor
#assert_axioms pHon_natDegree_lt
#assert_axioms evalVec_pVal_pHon
#assert_axioms QH_sampleRich
#assert_axioms honest_childSat
#assert_axioms honest_transcript_of_polynomial
#assert_axioms honest_columnsCVS
#assert_axioms nonCircular_extract_fires
#assert_axioms honest_extracted_poly_unique

end Dregg2.Circuit.FriExtractNonCircular
