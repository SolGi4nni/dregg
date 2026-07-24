/-
# `Dregg2.Circuit.CorrelatedAgreement.Interface` — PINNING THE INTERFACE: which
correlated-agreement statement the FRI extractor residual actually consumes, stated as
Lean theorems with the CA Props as EXPLICIT HYPOTHESES.

## ⚑ THE REGIME VERDICT (the decisive question, answered with citations)

**Verdict: (1) UD-regime BCIKS is what `DecodedLdtLink` consumes — over the QUARTIC
EXTENSION. Neither (0) the base-field collapse nor (2) Johnson-regime BCIKS fills the
consumer.** The in-progress UD formalization
(docs/RESEARCH-correlated-agreement-UD-prompt-2026-07-24.md) is the RIGHT target, with one
refinement forced by (0): the deployed instantiation is at F := the degree-4 extension.

**(0) The base-field collapse (`FriExtChallengeCollapse.lean` b95db24ddd) does NOT discharge
the consumer — the CA-consuming words are EXTENSION-valued.** The collapse theorem
(`extChallenge_forces_correlatedAgreement`, `FriExtChallengeCollapse.lean:82-86`) types its
words `u₀ u₁ : κ → K` (BASE-field), and its own scope note (`:30-34`) excludes
extension-valued words. At the consumer, the words are extension-valued at EVERY CA site:
the deployed DEEP reduction (`vendor/plonky3-fri-82cfad73/src/verifier.rs:617-640`, the
pinned rev `82cfad7` of `fri/src/verifier.rs`) computes
`ro : Challenge` (`or_insert((Challenge::ONE, Challenge::ZERO))`),
`quotient = (*z - x).inverse() : Challenge` (ζ is drawn from the extension), and
`*ro += *alpha_pow * (p_at_z - p_at_x) * quotient` — the base-field committed column value
`p_at_x : Val` becomes extension-valued the INSTANT the quotient is formed, before any
challenge ever multiplies it. So (a) the per-column DEEP quotients
`q_j = (p_j(ζ) − p_j(·))/(ζ − ·) : ι → L` that the α-RLC distribution must separate are
L-valued, and (b) the FRI input word `ro` and every fold-tower layer under it are L-valued.
The ONLY base-field words in the pipeline — the committed trace columns `p_j` themselves —
are consumed by the UNIQUE DECODE, which needs no CA; they never meet a challenge while
still base-valued. Dimension count seals the door even for hypothetical re-architectures
that would fold raw base words: one quartic challenge exposes only `[L:K] = 4` basis
coordinates per point, and the deployed fold arity is `8 > 4` — a single challenge cannot
separate 8 base decimations (nor `numCols·4 > 4` quotient coordinates in the RLC). What the
collapse DOES do: it removes the base-field corner from the counterexample search space and
would serve a protocol that pairwise-RLCs base words before quotienting — real, but not
this consumer.

**(1) UD-regime BCIKS is required, and it is the right target.** Why UD and not Johnson:

  * The residual's antecedent is `MatrixOracle.ColsClose friSetupDeployed.C 7340032`
    (`FriDecodedTraceWitness.lean:461`), and everything downstream of it is UNIQUE decoding:
    `closeN_rsCode_decode` demands `2·e < N − D + 1` (`FriCloseNUniqueDecode.lean:119-122`),
    and the `∃!` is REFUTED one past the radius (`deployed_radius_plus_one_not_unique`,
    `FriCloseNUniqueDecode.lean` header: at `7340033` both `0` and `geomWord` decode). A
    Johnson-regime CA delivers closeness only at radii where the decoded object is a LIST —
    it literally cannot feed `decodedMatrix` / `colsClose_unique_vmTrace`
    (`FriDecodedTraceWitness.lean:246/:279`). The batch→column distribution the R4b header
    itemizes as sub-piece 2 (`FriDecodedTraceWitness.lean:44-48`) must deliver per-column
    closeness AT the UD radius, so the CA it needs is the UD-regime one.
**(2) Johnson-regime BCIKS is NOT required for this consumer.**
  * The JOHNSON radius enters the record at a DIFFERENT column — the ledger's per-fold BITS:
    `FriJohnsonRadiusGap.deployed_M1_false_at_johnson` (`:318`) refutes the `M = 1` route at
    Johnson, and the honest Johnson object (`arity8_johnson_good_card_le` `:556`, ~111 bits,
    `M ≤ 7`/`s = 8`) is a WEAKER, non-comparable claim, exactly as that file reports.
    Johnson-regime CA would defend THAT column (and needs the GS/list machinery the plan §5
    rightly skips); it would NOT close `DecodedLdtLink`. No plan change — but the per-fold
    soundness bits the UD route yields are the `(m−1)(r+1)`-type counts of this file
    (≈ 2^22.6 bad challenges per fold at the top layer, ≈ 101 bits over the quartic
    extension |R| ≈ 2^123.6), NOT the ledger's 109/111. Those remain separate objects;
    reporting them as one column was the error `FriJohnsonRadiusGap` already named.

**Which CA VARIANT (the load-bearing output for L1–L6):**
  * `CorrelatedAgreementCurveUDParam` — the m-term power-curve version, at **generic
    parameters**, in TWO instantiations: `m = 8` (the deployed fold arity — the per-fold
    round-by-round consumer, §5 below, needs it at EVERY layer `(nᵢ, rᵢ)` of the fold tower
    with the schedule `m·rᵢ₊₁ ≤ rᵢ`), and `m = numCols` (the α-RLC batch width — the
    batch→column distribution, §4 below). ⚑ The single deployed instantiation
    `(n = 2²⁴, r = 7340028)` is NOT enough: the tower consumes the theorem at every layer's
    shaved radius, and the schedule-composed top radius is `8^depth · r_last` (e.g.
    `8⁵·220 = 7208960 < 7340028` at an illustrative depth-5 tower to `n = 512`), so L5/L6
    must land the `Param` (generic `(n, k, r, m)`) form — which `Scaffolding.lean` already
    states. The plain-UD `r = 7340028` instantiation is right for the top-level batch/DEEP
    site. ⚑ Per verdict (0): the DEPLOYED instantiation of the Props is at F := the quartic
    extension (L-valued words on the base-domain points, code = RS over L — which is
    `extCode` of the base RS, so the base decode still receives base columns through the
    coordinate projection); the `Param` form is field-generic, so this costs L1–L6 nothing.
    The §4 weld below is stated at the tree's CURRENT model resolution (the whole in-tree
    decode chain `friSetupDeployed`/`ColsClose` is base-field BabyBear); when the L-valued
    FRI-input modeling lands, the same weld shape re-instantiates at L.
  * `CorrelatedAgreementPairUDParam` — the line version, for the DEEP two-term quotient
    (`u + α·v`) split (§4).
  * The CONSTRAINED / WEIGHTED / MUTUAL strengthenings (Kopparty 2025 §4.2–4.3, Thms
    4.3/4.5/4.6) are NOT required by the consumer as the tree currently shapes it: the
    in-tree round-by-round object propagates PLAIN farness through honest folds
    (`FriChainStepIdx.chain_far_survival_idx`), and prover deviation from the honest fold is
    the QUERY phase's job (the L6 dichotomy of `DeployedTraceExtract`), not the CA's. If
    that shape is later reworked to track per-position agreement weights across layers,
    Kopparty Thm 4.5 (weighted) becomes the ask — scope it then, as the plan §7 says.

## What this file PROVES (no sorry, no axiom, additive only)

  1. §1–§2: the CA Props' conclusion projected to what the consumers eat — simultaneous
     closeness ⟹ per-column closeness (`simClose_cols`), and the CA hypothesis ⟹ the
     good-challenge-set CAP `(m−1)(r+1)` (`curveGood_card_le`, `pairGood_card_le`) — the
     externally-proven cap the survival machinery demands (`FriChainStepIdx` §7's vacuity
     trap is exactly a cap-less good set).
  2. §3: the Props are INHABITED (non-vacuity): `curveUDParam_one` (m = 1, any code, any
     radius) and `curveUDParam_pair_exact` (m = 2, r = 0, any LINEAR code — the exact
     two-point Vandermonde solve), and the cap FIRES SHARP on RS(4,1)/ZMod 5:
     `curveGood_fire` pins the good set to EXACTLY `{1}`.
  3. §4: the deployed weld — UD curve CA at the deployed instance ⟹ THE LITERAL
     `MatrixOracle.ColsClose friSetupDeployed.C 7340032` that `DecodedLdtLink` and
     `decodedMatrix` consume (`deployed_colsClose_of_curveUD`), the pair version for the
     DEEP split (`deployed_deep_pair_close`), and the FS pricing of the RLC challenge
     (`rlc_alpha_bad_bound`: the drawn α is bad with probability ≤ (m−1)(r+1)/|F|, over the
     landed `hitWin`/`hit_bound` substrate).
  4. §5: ⚑ THE ROUND-BY-ROUND / FS SOUNDNESS STATEMENT with CA as the explicit hypothesis
     (`ud_tower_far_survival`): a fold tower with per-layer UD-regime curve CA (m = arity)
     and the decimation-lift weld prices the whole FS fold chain at
     `rounds·(m−1)(r₁+1)/|F|` — the CONSTANT-RELATIVE-RADIUS schedule that replaces the
     CA-free `n²`-loss route (`FriChainStepIdx.goodδ_card_lt`, whose `64×`-per-layer radius
     decay cannot reach the deployed depth). Proven over the EXISTING
     `Strategy`/`fsRun`/`winProb` layer via `chain_far_survival_idx`; fired end-to-end at a
     concrete instance (`tower_fire`).

## What is CARRIED as precisely-named hypotheses (never axioms)

  * The CA Props themselves (`CorrelatedAgreementCurveUDParam` at each layer /
    `CorrelatedAgreementPairUDParam`) — the L1–L6 targets.
  * `DecimLift` (§5) — the RS fold-geometry weld: simultaneous e-closeness of the m phase
    decimations lifts to (m·e)-closeness of the un-decimated word. True for the deployed
    phase decomposition (`FriArityTransfer` header: the deployed fold IS the moment curve of
    the decimations); its deployed-instance proof is the setup-TOWER engineering
    `FriChainStepIdx`'s header already names as missing. Named, not faked.
  * NOT carried and NOT claimed: the wire from the deployed verifier's transcript to these
    words (the RLC input-reduction residual, `DeployedTraceExtract.lean:414-419`) — the
    remaining assembly between §4 and §5 and the query-phase dichotomy stays where the tree
    already names it.
-/
import Dregg2.Circuit.CorrelatedAgreement.Scaffolding
import Dregg2.Circuit.FriChainStepIdx
import Dregg2.Circuit.FriBatchedOracle
import Dregg2.Circuit.FriCloseNUniqueDecode
import Dregg2.Tactics

namespace Dregg2.Circuit.CorrelatedAgreement.Interface

open Polynomial
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ProbCrypto (winProb winProb_nonneg winProb_le_of_imp)
open Dregg2.Circuit.FriChainStepIdx
  (hitWin hitWin_query hit_bound ChainStepIdx chain_far_survival_idx sigFar sigFold)
open Dregg2.Circuit.FriAdversaryObject (Strategy fsRun fsChain honestStrategy)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)
open Dregg2.Circuit.FriDeployedRateInstance (rsCode friSetupDeployed pR omega24)
open Dregg2.Circuit.FriCloseNUniqueDecode (mem_rsCode_iff_lowDegree_evalVec)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## §0 — Vocabulary bridges: the Scaffolding objects ARE the deployed objects.

The CA Props live over `CorrelatedAgreement.closeN` (Mathlib `hammingDist`) and
`Scaffolding.RScode`; the consumer (`ColsClose`, the decode rung) lives over
`FriSoundness.closeN` (`disagree`) and `FriDeployedRateInstance.rsCode`. Both bridges are
definitional or near-definitional — the two vocabularies name ONE object. -/

section Bridges

variable {F : Type*} [Field F] [DecidableEq F]

/-- The Scaffolding `closeN` over a submodule's coercion IS the deployed `FriSoundness.closeN`:
`hammingDist` and `disagree`-cardinality are the same filter cardinality, definitionally. -/
theorem closeN_coe_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule F (ι → F)) (r : ℕ) (f : ι → F) :
    closeN (↑C : Set (ι → F)) r f ↔ Dregg2.Circuit.FriSoundness.closeN C r f :=
  Iff.rfl

/-- **The code weld**: the Scaffolding RS code (degree-`< k` polynomials, evaluated) IS the
deployed coefficient-sum `rsCode`, for `0 < k`. Routes through
`mem_rsCode_iff_lowDegree_evalVec` plus the `degree`/`natDegree` bridge. -/
theorem RScode_eq_rsCode {N k : ℕ} (hk : 0 < k) (pts : Fin N → F) :
    RScode pts k = rsCode pts k := by
  ext f
  rw [mem_RScode, mem_rsCode_iff_lowDegree_evalVec hk]
  constructor
  · rintro ⟨p, hdeg, hev⟩
    refine ⟨p, ?_, funext hev⟩
    rcases eq_or_ne p 0 with rfl | hp
    · simpa using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr hdeg
  · rintro ⟨p, hdeg, rfl⟩
    exact ⟨p, lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hdeg),
      fun i => rfl⟩

end Bridges

/-! ## §1 — The combination words and SIMULTANEOUS closeness (the CA conclusions, as defs). -/

section Comb

variable {F : Type*} [Field F] [DecidableEq F] {n m : ℕ}

/-- The m-term power-curve combination — EXACTLY the word of
`CorrelatedAgreementCurveUDParam`'s hypothesis (and, per the `FriArityTransfer` header, the
shape of the deployed arity-`m` fold: the moment curve of the phase decimations). -/
def curveComb (u : Fin m → Fin n → F) (α : F) : Fin n → F :=
  fun x => ∑ j : Fin m, α ^ (j : ℕ) * u j x

/-- The affine-line combination — the word of `CorrelatedAgreementPairUDParam`'s hypothesis
(the DEEP two-term quotient split). -/
def pairComb (u v : Fin n → F) (α : F) : Fin n → F :=
  fun x => u x + α * v x

/-- **Simultaneous r-closeness** — verbatim the CONCLUSION of
`CorrelatedAgreementCurveUDParam`: one common agreement set of size ≥ n − r for all m rows. -/
def SimClose (V : Set (Fin n → F)) (r : ℕ) (u : Fin m → Fin n → F) : Prop :=
  ∃ g : Fin m → Fin n → F, (∀ j, g j ∈ V) ∧
    n - r ≤ (Finset.univ.filter fun x => ∀ j, u j x = g j x).card

/-- **Simultaneous pair closeness** — verbatim the conclusion of
`CorrelatedAgreementPairUDParam`. -/
def PairSimClose (V : Set (Fin n → F)) (r : ℕ) (u v : Fin n → F) : Prop :=
  ∃ gu ∈ V, ∃ gv ∈ V,
    n - r ≤ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x).card

/-- `SimClose` IS the Scaffolding L0.3 interleaved distance (`interleavedClose`), through
`interleavedClose_iff_filter` — the two statements of "Δ([u], C^m) ≤ r" coincide. -/
theorem simClose_iff_interleavedClose (V : Set (Fin n → F)) (r : ℕ) (u : Fin m → Fin n → F) :
    SimClose V r u ↔ interleavedClose V u r := by
  rw [interleavedClose_iff_filter]
  unfold SimClose
  simp [Fintype.card_fin]

/-- **The column projection — what `ColsClose` eats.** Simultaneous closeness of the batch
gives EACH row individually r-close: row j's disagreements with `g j` sit inside the
complement of the common agreement set. -/
theorem simClose_cols {V : Set (Fin n → F)} {r : ℕ} {u : Fin m → Fin n → F}
    (h : SimClose V r u) (j : Fin m) : closeN V r (u j) := by
  obtain ⟨g, hg, hcard⟩ := h
  refine ⟨g j, hg j, ?_⟩
  have hsub : (Finset.univ.filter fun x => u j x ≠ g j x)
      ⊆ (Finset.univ.filter fun x => ∀ j', u j' x = g j' x)ᶜ := by
    intro x hx
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
      not_forall] at hx ⊢
    exact ⟨j, hx⟩
  have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_compl _)
  rw [hammingDist_eq_card_filter, Fintype.card_fin] at *
  omega

/-- The pair projection: simultaneous pair closeness gives both words individually close. -/
theorem pairSimClose_cols {V : Set (Fin n → F)} {r : ℕ} {u v : Fin n → F}
    (h : PairSimClose V r u v) : closeN V r u ∧ closeN V r v := by
  obtain ⟨gu, hgu, gv, hgv, hcard⟩ := h
  constructor
  · refine ⟨gu, hgu, ?_⟩
    have hsub : (Finset.univ.filter fun x => u x ≠ gu x)
        ⊆ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x)ᶜ := by
      intro x hx
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun hand => hx hand.1
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_compl _)
    rw [hammingDist_eq_card_filter, Fintype.card_fin] at *
    omega
  · refine ⟨gv, hgv, ?_⟩
    have hsub : (Finset.univ.filter fun x => v x ≠ gv x)
        ⊆ (Finset.univ.filter fun x => u x = gu x ∧ v x = gv x)ᶜ := by
      intro x hx
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact fun hand => hx hand.2
    have hc := (Finset.card_le_card hsub).trans_eq (Finset.card_compl _)
    rw [hammingDist_eq_card_filter, Fintype.card_fin] at *
    omega

end Comb

/-! ## §2 — The good-challenge sets, and the CA hypothesis ⟹ THE CAP.

`FriChainStepIdx` §7 proves a by-definition good set is admissible ONLY with an
externally-proven cardinality cap. These theorems ARE that cap, with the UD-regime CA Prop
as the named hypothesis — the exact shape `ChainStep`'s pricing consumes. -/

section Good

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F] {n m : ℕ}

open Classical in
/-- The good-challenge set of a batch: challenges whose combination is r-close to `V`. -/
noncomputable def curveGood (V : Set (Fin n → F)) (r : ℕ) (u : Fin m → Fin n → F) :
    Finset F :=
  Finset.univ.filter fun α => closeN V r (curveComb u α)

theorem mem_curveGood {V : Set (Fin n → F)} {r : ℕ} {u : Fin m → Fin n → F} {α : F} :
    α ∈ curveGood V r u ↔ closeN V r (curveComb u α) := by
  simp [curveGood]

open Classical in
/-- The good-challenge set of a pair. -/
noncomputable def pairGood (V : Set (Fin n → F)) (r : ℕ) (u v : Fin n → F) : Finset F :=
  Finset.univ.filter fun α => closeN V r (pairComb u v α)

theorem mem_pairGood {V : Set (Fin n → F)} {r : ℕ} {u v : Fin n → F} {α : F} :
    α ∈ pairGood V r u v ↔ closeN V r (pairComb u v α) := by
  simp [pairGood]

/-- **⚑ THE CAP FROM CA (curve).** Under the UD-regime m-term correlated agreement, a batch
that is NOT simultaneously r-close has at most `(m−1)(r+1)` good challenges. This is the
contrapositive of the Prop, and it is the externally-proven per-fold/per-batch cap the
survival machinery (`chain_far_survival_idx`) consumes as `b`. -/
theorem curveGood_card_le {V : Set (Fin n → F)} {r : ℕ} {u : Fin m → Fin n → F}
    (hCA : CorrelatedAgreementCurveUDParam F n V r m)
    (hfar : ¬ SimClose V r u) :
    (curveGood V r u).card ≤ (m - 1) * (r + 1) := by
  by_contra hcon
  rw [not_le] at hcon
  exact hfar (hCA u (curveGood V r u) (fun α hα => mem_curveGood.1 hα) hcon)

/-- **The cap from CA (pair).** At most `r + 1` good challenges for a non-simultaneously-close
pair — the DEEP-split pricing. -/
theorem pairGood_card_le {V : Set (Fin n → F)} {r : ℕ} {u v : Fin n → F}
    (hCA : CorrelatedAgreementPairUDParam F n V r)
    (hfar : ¬ PairSimClose V r u v) :
    (pairGood V r u v).card ≤ r + 1 := by
  by_contra hcon
  rw [not_le] at hcon
  exact hfar (hCA u v (pairGood V r u v) (fun α hα => mem_pairGood.1 hα) hcon)

end Good

/-! ## §3 — Non-vacuity: the Props are INHABITED, and the cap FIRES SHARP.

The full UD-regime Props at the deployed radii are the L1–L6 targets and are NOT claimed
here. What IS proven: two genuine instances (m = 1 at any radius; m = 2 at radius 0 over any
linear code — the exact two-point Vandermonde solve), certifying the Prop SHAPE is provable
and non-degenerate; then the §2 cap fires on RS(4,1)/ZMod 5 with the good set pinned to
EXACTLY `{1}` — the bound is attained, not slack. -/

section Inhabit

variable {F : Type*} [Field F] [DecidableEq F]

/-- **m = 1 instance, PROVEN**: the 1-term "curve" is the word itself; one good challenge
already yields the (trivially simultaneous) closeness. Threshold `(1−1)(r+1) = 0`. -/
theorem curveUDParam_one (n : ℕ) (V : Set (Fin n → F)) (r : ℕ) :
    CorrelatedAgreementCurveUDParam F n V r 1 := by
  intro u Good hGood hcard
  have hpos : 0 < Good.card := by simpa using hcard
  obtain ⟨α, hα⟩ := Finset.card_pos.mp hpos
  obtain ⟨v, hv, hd⟩ := hGood α hα
  have hcomb : (fun x => ∑ j : Fin 1, α ^ (j : ℕ) * u j x) = u 0 := by
    funext x
    simp
  rw [hcomb] at hd
  refine ⟨fun _ => v, fun _ => hv, ?_⟩
  have hfe : (Finset.univ.filter fun x => ∀ j : Fin 1, u j x = (fun _ : Fin 1 => v) j x)
      = Finset.univ.filter fun x => u 0 x = v x := by
    refine Finset.filter_congr fun x _ => ?_
    constructor
    · intro h
      exact h 0
    · intro h j
      exact Fin.fin_one_eq_zero j ▸ h
  rw [hfe]
  have hne : (Finset.univ.filter fun x : Fin n => u 0 x ≠ v x).card ≤ r :=
    le_trans (le_of_eq (hammingDist_eq_card_filter (u 0) v).symm) hd
  have hnot : (Finset.univ.filter fun x : Fin n => u 0 x ≠ v x)
      = Finset.univ \ (Finset.univ.filter fun x : Fin n => u 0 x = v x) := by
    simp [ne_eq, Finset.filter_not]
  rw [hnot, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin] at hne
  omega

/-- **m = 2, r = 0 instance over any LINEAR code, PROVEN** — the exact two-point Vandermonde
solve: two exact memberships of `u₀ + αᵢ·u₁` pin `u₀, u₁ ∈ C` and the agreement is total.
This is the r = 0 shadow of the full theorem (the general r is L1–L6's job); it certifies
the pair/curve Prop shape has REAL instances over every submodule code. -/
theorem curveUDParam_pair_exact (n : ℕ) (C : Submodule F (Fin n → F)) :
    CorrelatedAgreementCurveUDParam F n (↑C : Set (Fin n → F)) 0 2 := by
  intro u Good hGood hcard
  have h1 : 1 < Good.card := by simpa using hcard
  obtain ⟨α₁, hα₁, α₂, hα₂, hne⟩ := Finset.one_lt_card.mp h1
  obtain ⟨g₁, hg₁, hd₁⟩ := hGood α₁ hα₁
  obtain ⟨g₂, hg₂, hd₂⟩ := hGood α₂ hα₂
  have he₁ : (fun x => ∑ j : Fin 2, α₁ ^ (j : ℕ) * u j x) = g₁ :=
    hammingDist_eq_zero.mp (Nat.le_zero.mp hd₁)
  have he₂ : (fun x => ∑ j : Fin 2, α₂ ^ (j : ℕ) * u j x) = g₂ :=
    hammingDist_eq_zero.mp (Nat.le_zero.mp hd₂)
  have hp₁ : ∀ x, u 0 x + α₁ * u 1 x = g₁ x := by
    intro x
    have h := congrFun he₁ x
    simpa [Fin.sum_univ_two] using h
  have hp₂ : ∀ x, u 0 x + α₂ * u 1 x = g₂ x := by
    intro x
    have h := congrFun he₂ x
    simpa [Fin.sum_univ_two] using h
  have hsub : α₁ - α₂ ≠ 0 := sub_ne_zero.mpr hne
  have hu1 : u 1 = (α₁ - α₂)⁻¹ • (g₁ - g₂) := by
    funext x
    have h₁ := hp₁ x
    have h₂ := hp₂ x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    linear_combination h₁ - h₂
  have hu1C : u 1 ∈ C := by
    rw [hu1]
    exact C.smul_mem _ (C.sub_mem hg₁ hg₂)
  have hu0 : u 0 = g₁ - α₁ • u 1 := by
    funext x
    have h₁ := hp₁ x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination h₁
  have hu0C : u 0 ∈ C := by
    rw [hu0]
    exact C.sub_mem hg₁ (C.smul_mem _ hu1C)
  refine ⟨u, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact hu0C
    · exact hu1C
  · have huniv : (Finset.univ.filter fun x => ∀ j, u j x = u j x) = Finset.univ := by
      simp
    rw [huniv, Finset.card_univ, Fintype.card_fin]
    omega

end Inhabit

section Fire

/-- The received word `![2,2,2,3]` is NOT a codeword of RS(4,1)/ZMod 5 (it is not constant). -/
theorem w4_not_mem : w4 ∉ RScode pt5 1 := by
  intro h
  obtain ⟨p, hdeg, hev⟩ := mem_RScode.mp h
  have hp : p = Polynomial.C (p.coeff 0) :=
    Polynomial.eq_C_of_degree_le_zero
      (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hdeg))
  have h03 : w4 0 = w4 3 := by
    rw [hev 0, hev 3, hp]
    simp
  exact absurd h03 (by decide)

/-- The FIRE batch: `u₀ = w4` (a non-codeword), `u₁ = c2 − w4` (so `α = 1` lands exactly on
the constant-2 codeword). -/
noncomputable def uFire : Fin 2 → Fin 4 → ZMod 5 := ![w4, c2 - w4]

/-- The FIRE batch is NOT simultaneously 0-close: total agreement would force `w4` into the
code. -/
theorem uFire_not_simClose :
    ¬ SimClose (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5)) 0 uFire := by
  rintro ⟨g, hg, hcard⟩
  have hle : (Finset.univ.filter fun x => ∀ j, uFire j x = g j x).card ≤ 4 :=
    (Finset.card_le_univ _).trans_eq (by simp)
  have huniv : (Finset.univ.filter fun x => ∀ j, uFire j x = g j x) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using le_antisymm hle (by simpa using hcard))
  have h0 : ∀ x, uFire 0 x = g 0 x := by
    intro x
    have hx : x ∈ Finset.univ.filter fun x => ∀ j, uFire j x = g j x := by
      rw [huniv]
      exact Finset.mem_univ x
    exact (Finset.mem_filter.mp hx).2 0
  have hw4 : w4 = g 0 := by
    funext x
    have := h0 x
    simpa [uFire] using this
  exact w4_not_mem (hw4 ▸ hg 0)

/-- `α = 1` IS a good challenge for the FIRE batch: the combination collapses to `c2`. -/
theorem one_mem_curveGood :
    (1 : ZMod 5) ∈ curveGood (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5)) 0 uFire := by
  rw [mem_curveGood]
  have hcomb : curveComb uFire (1 : ZMod 5) = c2 := by
    funext x
    show ∑ j : Fin 2, (1 : ZMod 5) ^ (j : ℕ) * uFire j x = c2 x
    rw [Fin.sum_univ_two]
    simp [uFire]
  rw [hcomb]
  exact ⟨c2, c2_mem, by simp⟩

/-- **⚑ THE CAP FIRES SHARP** — on RS(4,1)/ZMod 5 the good set of the FIRE batch is EXACTLY
`{1}`: the §2 cap gives `≤ (2−1)·(0+1) = 1`, and `α = 1` inhabits it. The CA-derived bound
is attained — full strength, zero slack — on a concrete non-degenerate instance. -/
theorem curveGood_fire :
    curveGood (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5)) 0 uFire = {1} := by
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro α hα
    rw [Finset.mem_singleton] at hα
    subst hα
    exact one_mem_curveGood
  · have hcap := curveGood_card_le (curveUDParam_pair_exact 4 (RScode pt5 1))
      uFire_not_simClose
    simpa using hcap

end Fire

/-! ## §4 — THE STEP TOWARD `DecodedLdtLink`: UD curve CA ⟹ the literal `ColsClose`
antecedent, plus the FS pricing of the RLC challenge.

`DecodedLdtLink` (`FriDecodedTraceWitness.lean:450`) and the decode-as-data
(`decodedMatrix`, `:246`) consume `MatrixOracle.ColsClose friSetupDeployed.C 7340032`. The
theorem below produces EXACTLY that object from the deployed-instance UD curve CA — the
batch→column distribution of the R4b header's sub-piece 2, in Lean. What remains between
this and the closed residual is (a) proving the CA Prop (L1–L6) and (b) the deployed
transcript wire (the RLC input-reduction residual, named in `DeployedTraceExtract`), plus
the DEEP domain-re-base — carried exactly where the tree already names them. -/

section Deployed

/-- The deployed evaluation points, at the `Fin (2²⁴)` index the CA Props use
(definitionally `Fin (8·2²¹)`). -/
noncomputable def deployedPts : Fin (2 ^ 24) → BabyBear := pR 8 (2 ^ 21) omega24

/-- The Scaffolding RS code at the deployed points IS the deployed FRI domain code. -/
theorem deployed_code_eq : RScode deployedPts (2 ^ 21) = friSetupDeployed.C := by
  rw [RScode_eq_rsCode (by norm_num) deployedPts]
  rfl

/-- **⚑ UD curve CA ⟹ `DecodedLdtLink`'s `ColsClose` antecedent.** If the deployed-instance
m-term UD correlated agreement holds, then ANY batched commitment whose α-RLC is
`7340028`-close to the deployed code for more than `(numCols−1)·7340029` challenges has
EVERY committed column `7340032`-close — the literal input of `decodedMatrix` /
`colsClose_unique_vmTrace` / `DecodedLdtLink`. The radius slack `7340028 ≤ 7340032` is the
doc-§4(i) boundary shave, absorbed by `closeN` monotonicity. -/
theorem deployed_colsClose_of_curveUD {numCols : ℕ}
    (hCA : CorrelatedAgreementCurveUD (F := BabyBear) deployedPts numCols)
    (M : MatrixOracle (Fin (2 ^ 24)) numCols BabyBear)
    (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good,
      Dregg2.Circuit.FriSoundness.closeN friSetupDeployed.C 7340028
        (fun x => ∑ j : Fin numCols, α ^ (j : ℕ) * M.col j x))
    (hcard : (numCols - 1) * 7340029 < Good.card) :
    MatrixOracle.ColsClose friSetupDeployed.C 7340032 M := by
  have hcode : (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear))
      = ↑friSetupDeployed.C := by
    rw [deployed_code_eq]
  have hsim : SimClose (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear))
      7340028 (fun j => M.col j) := by
    refine hCA (fun j => M.col j) Good (fun α hα => ?_) hcard
    rw [show closeN (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear)) 7340028
        = closeN (↑friSetupDeployed.C : Set (Fin (2 ^ 24) → BabyBear)) 7340028 from by
      rw [hcode]]
    exact (closeN_coe_iff friSetupDeployed.C 7340028 _).mpr (hGood α hα)
  intro j
  have hj := simClose_cols hsim j
  have hj' : closeN (↑friSetupDeployed.C : Set (Fin (2 ^ 24) → BabyBear)) 7340032 (M.col j) := by
    rw [← hcode]
    exact closeN_mono (by norm_num) hj
  exact (closeN_coe_iff friSetupDeployed.C 7340032 (M.col j)).mp hj'

/-- **UD pair CA ⟹ the DEEP two-term split.** The deployed-instance line version distributes
`u + α·v` closeness (for > 7340029 challenges) to BOTH terms individually at the UD radius —
the shape of the DEEP quotient consistency step (R4b sub-piece 2's two-term core). -/
theorem deployed_deep_pair_close
    (hCA : CorrelatedAgreementPairUD (F := BabyBear) deployedPts)
    (u v : Fin (2 ^ 24) → BabyBear) (Good : Finset BabyBear)
    (hGood : ∀ α ∈ Good,
      Dregg2.Circuit.FriSoundness.closeN friSetupDeployed.C 7340028
        (fun x => u x + α * v x))
    (hcard : 7340029 < Good.card) :
    Dregg2.Circuit.FriSoundness.closeN friSetupDeployed.C 7340028 u ∧
      Dregg2.Circuit.FriSoundness.closeN friSetupDeployed.C 7340028 v := by
  have hcode : (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear))
      = ↑friSetupDeployed.C := by
    rw [deployed_code_eq]
  have hp : PairSimClose (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear))
      7340028 u v := by
    refine hCA u v Good (fun α hα => ?_) hcard
    rw [show closeN (↑(RScode deployedPts (2 ^ 21)) : Set (Fin (2 ^ 24) → BabyBear)) 7340028
        = closeN (↑friSetupDeployed.C : Set (Fin (2 ^ 24) → BabyBear)) 7340028 from by
      rw [hcode]]
    exact (closeN_coe_iff friSetupDeployed.C 7340028 _).mpr (hGood α hα)
  obtain ⟨hu, hv⟩ := pairSimClose_cols hp
  rw [hcode] at hu hv
  exact ⟨(closeN_coe_iff friSetupDeployed.C 7340028 u).mp hu,
    (closeN_coe_iff friSetupDeployed.C 7340028 v).mp hv⟩

end Deployed

section RlcFs

variable {F : Type} [Field F] [DecidableEq F] [Fintype F]

local instance {n m : ℕ} : Fintype (MatrixOracle (Fin n) m F) :=
  inferInstanceAs (Fintype (Fin n → Fin m → F))

local instance {n m : ℕ} : DecidableEq (MatrixOracle (Fin n) m F) :=
  inferInstanceAs (DecidableEq (Fin n → Fin m → F))

open Classical in
/-- **The FS pricing of the RLC challenge, from CA** — the first probabilistic step of the
batch side, over the landed `hitWin`/`hit_bound` substrate: for a committed batch that is
NOT simultaneously r-close, the FS-drawn (ROM-answered) α lands in its good set with
probability at most `(m−1)(r+1)/|F|`. The bad-set cap is §2's `curveGood_card_le` — the CA
hypothesis is exactly what turns the by-definition good set into a PRICED one. -/
theorem rlc_alpha_bad_bound {n m : ℕ} (V : Set (Fin n → F)) (r : ℕ)
    (hCA : CorrelatedAgreementCurveUDParam F n V r m)
    (M0 : MatrixOracle (Fin n) m F) :
    winProb (fun H : MatrixOracle (Fin n) m F → F =>
        decide (¬ SimClose V r (fun j => M0.col j) ∧
          closeN V r (curveComb (fun j => M0.col j) (H M0))))
      ≤ (((m - 1) * (r + 1) : ℕ) : ℝ) / (Fintype.card F : ℝ) := by
  haveI : Nonempty F := ⟨0⟩
  set E : MatrixOracle (Fin n) m F → Finset F := fun M =>
    if SimClose V r (fun j => M.col j) then ∅ else curveGood V r (fun j => M.col j)
    with hE
  have hEcard : ∀ d, (E d).card ≤ (m - 1) * (r + 1) := by
    intro d
    simp only [hE]
    split_ifs with h
    · simp
    · exact curveGood_card_le hCA h
  have himp : ∀ H : MatrixOracle (Fin n) m F → F,
      (decide (¬ SimClose V r (fun j => M0.col j) ∧
        closeN V r (curveComb (fun j => M0.col j) (H M0)))) = true →
      hitWin E (OracleComp.query M0 (fun _ => OracleComp.pure ())) H = true := by
    intro H hH
    obtain ⟨hfar, hclose⟩ := of_decide_eq_true hH
    rw [hitWin_query]
    have hmem : H M0 ∈ E M0 := by
      simp only [hE]
      rw [if_neg hfar]
      exact mem_curveGood.2 hclose
    simp [hmem]
  refine (winProb_le_of_imp himp).trans ?_
  have hqb : QueryBounded 1 (OracleComp.query M0 (fun _ : F => OracleComp.pure ())) :=
    QueryBounded.query 0 _ _ (fun _ => QueryBounded.pure 0 ())
  refine (hit_bound _ hqb E hEcard).trans (le_of_eq ?_)
  push_cast
  ring

end RlcFs

/-! ## §5 — ⚑ THE ROUND-BY-ROUND SOUNDNESS STATEMENT: the fold tower priced by UD CA.

THE interface theorem: `CA-theorem ⟹ (a step toward) the residual`, over the EXISTING
adversary layer. The deployed FRI is a shrinking-domain fold tower (arity m = 8); the word
at layer i decimates into m phase words on the layer-(i+1) domain, and the fold at challenge
α is their power-curve combination (`FriArityTransfer`: the deployed `fold_row` IS this
moment curve). Given

  * per-layer UD-regime curve CA (`hCA` — the L1–L6 target, at the layer's parameters),
  * the decimation lift `DecimLift` (the RS fold-geometry weld — the named tower residual),
  * the radius schedule `m·rᵢ₊₁ ≤ rᵢ` (constant RELATIVE radius; contrast the CA-free
    `n²·d` schedule of `goodδ_card_lt`, which decays 64× per layer and cannot reach the
    deployed depth),

every FS event implying "the terminal word of the honest-fold chain is not far" has
probability ≤ `rounds·(m−1)(r₁+1)/|F|` — `chain_far_survival_idx` with the CA-derived cap.
Contrapositive reading: except with that probability, the layer-0 committed word is
`r₀`-close — which is (per column, through §4) the `ColsClose` the decode consumes. -/

section Tower

variable {F : Type} [Field F] [DecidableEq F]

/-- The per-layer fold: decimate, then take the α-power-curve combination — the deployed
arity-`m` fold shape. -/
def towerFold (nn : ℕ → ℕ) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)) :
    ∀ i, (Fin (nn i) → F) → F → (Fin (nn (i + 1)) → F) :=
  fun i w α => curveComb (dec i w) α

/-- **`DecimLift` — the decimation-lift weld, NAMED (carried, not faked).** Simultaneous
e-closeness of the m phase decimations (one common agreement set) lifts to (m·e)-closeness
of the un-decimated word: the m fibers over each agreeing point recombine, and a codeword
tuple of the folded code assembles to a codeword of the domain code. TRUE for the deployed
phase decomposition; its deployed-instance proof is the setup-tower engineering
`FriChainStepIdx`'s header names as missing (no welded `FriSetupK` tower in-tree). -/
def DecimLift (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F)) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)) : Prop :=
  ∀ (i : ℕ) (w : Fin (nn i) → F) (g : Fin m → Fin (nn (i + 1)) → F),
    (∀ j, g j ∈ V (i + 1)) →
    ∀ e : ℕ,
      nn (i + 1) - e ≤ (Finset.univ.filter fun y => ∀ j, dec i w j y = g j y).card →
      closeN (V i) (m * e) w

/-- The per-layer farness schedule, truncated at depth L (`True` above it — the chain runs
`rounds ≤ L` layers; the truncation is what keeps the ROM query domain finite). -/
def towerFar (L : ℕ) (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F)) (rr : ℕ → ℕ)
    (i : ℕ) (w : Fin (nn i) → F) : Prop :=
  if i ≤ L then ¬ closeN (V i) (rr i) w else True

/-- Reading the truncated farness at layers the chain actually reaches. -/
theorem towerFar_of_le {L : ℕ} {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ}
    {i : ℕ} (hi : i ≤ L) (w : Fin (nn i) → F) :
    towerFar L nn V rr i w ↔ ¬ closeN (V i) (rr i) w := by
  unfold towerFar
  rw [if_pos hi]

variable [Fintype F]

open Classical in
/-- The layer-i good set: challenges folding `w` to within the NEXT layer's radius. -/
noncomputable def towerGood (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F)) (rr : ℕ → ℕ)
    (m : ℕ) (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F))
    (i : ℕ) (w : Fin (nn i) → F) : Finset F :=
  Finset.univ.filter fun α => closeN (V (i + 1)) (rr (i + 1)) (towerFold nn m dec i w α)

theorem mem_towerGood {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ}
    {m : ℕ} {dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)}
    {i : ℕ} {w : Fin (nn i) → F} {α : F} :
    α ∈ towerGood nn V rr m dec i w ↔
      closeN (V (i + 1)) (rr (i + 1)) (towerFold nn m dec i w α) := by
  simp [towerGood]

/-- The depth-truncated good set (empty above the tower). -/
noncomputable def towerGoodTrunc (L : ℕ) (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F))
    (rr : ℕ → ℕ) (m : ℕ) (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F))
    (i : ℕ) (w : Fin (nn i) → F) : Finset F :=
  if i < L then towerGood nn V rr m dec i w else ∅

/-- **THE PER-LAYER CAP FROM CA** — the tower's `b`: at a layer-i far word, under the layer's
UD curve CA and the lift weld, at most `(m−1)(rᵢ₊₁+1)` challenges fold it close. This is the
cap that replaces the CA-free `n²`-loss schedule with a constant-relative-radius one. -/
theorem towerGood_card_le {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ}
    {m : ℕ} {dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)}
    {i : ℕ} {w : Fin (nn i) → F}
    (hsched : m * rr (i + 1) ≤ rr i)
    (hlift : DecimLift nn V m dec)
    (hCA : CorrelatedAgreementCurveUDParam F (nn (i + 1)) (V (i + 1)) (rr (i + 1)) m)
    (hfar : ¬ closeN (V i) (rr i) w) :
    (towerGood nn V rr m dec i w).card ≤ (m - 1) * (rr (i + 1) + 1) := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨g, hg, hagree⟩ := hCA (dec i w) (towerGood nn V rr m dec i w)
    (fun α hα => mem_towerGood.1 hα) hcon
  exact hfar (closeN_mono hsched (hlift i w g hg (rr (i + 1)) hagree))

/-- The tower `ChainStepIdx` instance — definitional (the CAP is the content, and it is
external, §above): a far word folded at a challenge outside its good set lands far at the
next layer's radius. -/
theorem towerChainStepIdx (L : ℕ) (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F))
    (rr : ℕ → ℕ) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)) :
    ChainStepIdx (W := fun i => Fin (nn i) → F)
      (towerFar L nn V rr) (towerGoodTrunc L nn V rr m dec) (towerFold nn m dec) := by
  intro i w α hfar hα
  unfold towerFar
  by_cases hi : i < L
  · rw [if_pos (by omega : i + 1 ≤ L)]
    intro hclose
    apply hα
    unfold towerGoodTrunc
    rw [if_pos hi]
    exact mem_towerGood.mpr hclose
  · rw [if_neg (by omega : ¬ i + 1 ≤ L)]
    trivial

/-- The finite ROM query domain of the tower run: layer-tagged words up to depth L
(the `Option` sink absorbs the truncated layers). -/
abbrev towerD (L : ℕ) (nn : ℕ → ℕ) (F : Type) : Type :=
  Option (Σ k : Fin (L + 1), (Fin (nn (k : ℕ)) → F))

/-- The query-point encoding: the layer-tagged word itself (below the truncation). -/
def towerEnc (L : ℕ) (nn : ℕ → ℕ) :
    (Σ i, (Fin (nn i) → F)) → List F → towerD L nn F :=
  fun w _ => if h : w.1 < L + 1 then some ⟨⟨w.1, h⟩, w.2⟩ else none

open Classical in
/-- The bad-set cover: the layer good set at far in-tower words, empty elsewhere. -/
noncomputable def towerE (L : ℕ) (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F))
    (rr : ℕ → ℕ) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)) :
    towerD L nn F → Finset F :=
  fun d => d.elim ∅ fun kw =>
    if ¬ closeN (V (kw.1 : ℕ)) (rr (kw.1 : ℕ)) kw.2 ∧ (kw.1 : ℕ) < L then
      towerGood nn V rr m dec (kw.1 : ℕ) kw.2
    else ∅

/-- The radius schedule is antitone below layer 1 (needed for the uniform cap). -/
theorem rr_succ_le_rr_one {rr : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    (hsched : ∀ i, m * rr (i + 1) ≤ rr i) : ∀ j, rr (j + 1) ≤ rr 1 := by
  intro j
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
      exact le_trans (le_trans (Nat.le_mul_of_pos_left _ hm) (hsched (j + 1))) ih

/-- The uniform cover cap: every point's bad set is ≤ `(m−1)(r₁+1)` — the per-layer CA caps,
majorized along the antitone schedule. -/
theorem towerE_card_le {L : ℕ} {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ}
    {m : ℕ} {dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)}
    (hm : 1 ≤ m) (hsched : ∀ i, m * rr (i + 1) ≤ rr i)
    (hlift : DecimLift nn V m dec)
    (hCA : ∀ i, i < L →
      CorrelatedAgreementCurveUDParam F (nn (i + 1)) (V (i + 1)) (rr (i + 1)) m) :
    ∀ d, (towerE L nn V rr m dec d).card ≤ (m - 1) * (rr 1 + 1) := by
  intro d
  match d with
  | none => simp [towerE]
  | some kw =>
      simp only [towerE, Option.elim]
      split_ifs with h
      · obtain ⟨hfar, hkL⟩ := h
        refine (towerGood_card_le (hsched _) hlift (hCA _ hkL) hfar).trans ?_
        exact Nat.mul_le_mul_left _ (by
          have := rr_succ_le_rr_one hm hsched (kw.1 : ℕ)
          omega)
      · simp

/-- The far-conditional cover: at far in-tower words the cover IS the good set. -/
theorem towerE_cover {L : ℕ} {nn : ℕ → ℕ} {V : ∀ i, Set (Fin (nn i) → F)} {rr : ℕ → ℕ}
    {m : ℕ} {dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F)} :
    ∀ (i : ℕ) (w : Fin (nn i) → F) (cs : List F),
      towerFar L nn V rr i w →
      towerGoodTrunc L nn V rr m dec i w
        ⊆ towerE L nn V rr m dec (towerEnc L nn ⟨i, w⟩ cs) := by
  intro i w cs hfar
  by_cases hi : i < L
  · have hi1 : i < L + 1 := by omega
    have hfar' : ¬ closeN (V i) (rr i) w :=
      (towerFar_of_le (by omega : i ≤ L) w).mp hfar
    unfold towerEnc
    rw [dif_pos hi1]
    simp only [towerE, Option.elim]
    rw [if_pos ⟨hfar', hi⟩]
    unfold towerGoodTrunc
    rw [if_pos hi]
  · unfold towerGoodTrunc
    rw [if_neg hi]
    exact Finset.empty_subset _

open Classical in
/-- **⚑ THE INTERFACE THEOREM — round-by-round FS soundness of the fold tower, with the
UD-regime correlated agreement as the EXPLICIT hypothesis.** Under

  * `hCA` — per-layer `CorrelatedAgreementCurveUDParam` at the fold arity m (the L1–L6
    deliverable, consumed at every layer's parameters — this is why the Param form, not the
    single deployed instantiation, is the target),
  * `hlift` — the decimation-lift weld (the named tower residual),
  * `hsched` — the constant-relative-radius schedule `m·rᵢ₊₁ ≤ rᵢ`,

any event implying "the terminal word of the `rounds`-round honest-fold FS chain from the
far `w0` is not far" has probability at most `rounds·(m−1)(r₁+1)/|F|` over the random
oracle. Contrapositive: except with that probability, farness SURVIVES to the terminal
round — where the query phase (priced separately, the L6 dichotomy) finishes; equivalently,
an accepting run's committed word is `r₀`-close, which per §4 is the decode's `ColsClose`.
One application of the landed `chain_far_survival_idx`; the CA enters ONLY as the bad-set
cap, which is exactly the interface the plan needs L1–L6 to fill. -/
theorem ud_tower_far_survival
    (L : ℕ) (nn : ℕ → ℕ) (V : ∀ i, Set (Fin (nn i) → F)) (rr : ℕ → ℕ) (m : ℕ)
    (dec : ∀ i, (Fin (nn i) → F) → Fin m → (Fin (nn (i + 1)) → F))
    (hm : 1 ≤ m) (hsched : ∀ i, m * rr (i + 1) ≤ rr i)
    (hlift : DecimLift nn V m dec)
    (hCA : ∀ i, i < L →
      CorrelatedAgreementCurveUDParam F (nn (i + 1)) (V (i + 1)) (rr (i + 1)) m)
    (w0 : Fin (nn 0) → F) (hfar0 : ¬ closeN (V 0) (rr 0) w0)
    (rounds : ℕ) {bad : (towerD L nn F → F) → Bool}
    (hbad : ∀ H : towerD L nn F → F, bad H = true →
      ¬ sigFar (towerFar L nn V rr)
          (honestStrategy (sigFold (towerFold nn m dec)) ⟨0, w0⟩
            (fsChain (towerEnc L nn)
              (honestStrategy (sigFold (towerFold nn m dec)) ⟨0, w0⟩) H rounds []))) :
    winProb bad
      ≤ ((rounds : ℝ) * (((m - 1) * (rr 1 + 1) : ℕ) : ℝ)) / (Fintype.card F : ℝ) := by
  haveI : Nonempty F := ⟨0⟩
  exact chain_far_survival_idx (towerChainStepIdx L nn V rr m dec)
    (towerEnc L nn) (towerE L nn V rr m dec)
    (towerE_card_le hm hsched hlift hCA) w0 towerE_cover
    ((towerFar_of_le (Nat.zero_le L) w0).mpr hfar0) rounds hbad

end Tower

/-! ### §5-FIRE — the interface theorem runs END-TO-END on a concrete instance.

`m = 1` over RS(4,1)/ZMod 5: the 1-term fold is the identity, `curveUDParam_one` discharges
the CA hypothesis, the lift weld is proven directly, and the far word is `w4`. The cap is
`(1−1)(r+1) = 0`, so the composed bound is EXACTLY 0 — and since the identity fold preserves
farness deterministically, that is the true value: every hypothesis of the headline theorem
is discharged concretely and the conclusion is attained, not slack. -/

section TowerFire

/-- The identity decimation lift at the constant RS(4,1)/ZMod 5 tower. -/
theorem fireLift : DecimLift (fun _ => 4)
    (fun _ => (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5))) 1 (fun _ w _ => w) := by
  intro i w g hg e hagree
  refine ⟨g 0, hg 0, ?_⟩
  rw [one_mul]
  have hfe : (Finset.univ.filter fun y => ∀ j : Fin 1, w y = g j y)
      = Finset.univ.filter fun y : Fin 4 => w y = g 0 y := by
    refine Finset.filter_congr fun y _ => ?_
    constructor
    · intro h
      exact h 0
    · intro h j
      exact Fin.fin_one_eq_zero j ▸ h
  rw [hfe] at hagree
  have hagree4 : 4 - e ≤ (Finset.univ.filter fun y : Fin 4 => w y = g 0 y).card := hagree
  have hne : (Finset.univ.filter fun y : Fin 4 => w y ≠ g 0 y).card ≤ e := by
    have hnot : (Finset.univ.filter fun y : Fin 4 => w y ≠ g 0 y)
        = Finset.univ \ (Finset.univ.filter fun y : Fin 4 => w y = g 0 y) := by
      simp [ne_eq, Finset.filter_not]
    rw [hnot, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    omega
  exact le_trans (le_of_eq (hammingDist_eq_card_filter w (g 0))) hne

/-- `w4` is 0-far (not a codeword) — the chain's initial farness, concrete. -/
theorem w4_far0 : ¬ closeN (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5)) 0 w4 := by
  rintro ⟨v, hv, hd⟩
  exact w4_not_mem ((hammingDist_eq_zero.mp (Nat.le_zero.mp hd)) ▸ hv)

open Classical in
/-- **FIRE — the interface theorem, end-to-end, bound attained.** One FS round of the
concrete tower: the probability that the far `w4` chain terminates non-far is EXACTLY 0 —
`ud_tower_far_survival` gives ≤ 0 (all hypotheses discharged: `curveUDParam_one`,
`fireLift`, `w4_far0`), and `winProb_nonneg` closes the other side. -/
theorem tower_fire :
    winProb (fun H : towerD 1 (fun _ => 4) (ZMod 5) → ZMod 5 =>
        decide (¬ sigFar (towerFar 1 (fun _ => 4)
            (fun _ => (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5))) (fun _ => 0))
          (honestStrategy (sigFold (towerFold (fun _ => 4) 1 (fun _ w _ => w))) ⟨0, w4⟩
            (fsChain (towerEnc 1 (fun _ => 4))
              (honestStrategy (sigFold (towerFold (fun _ => 4) 1 (fun _ w _ => w)))
                ⟨0, w4⟩) H 1 [])))) = 0 := by
  have h := ud_tower_far_survival 1 (fun _ => 4)
    (fun _ => (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5))) (fun _ => 0) 1
    (fun _ w _ => w) le_rfl (fun _ => by norm_num) fireLift
    (fun i _ => curveUDParam_one 4 _ 0) w4 w4_far0 1
    (bad := fun H => decide (¬ sigFar (towerFar 1 (fun _ => 4)
        (fun _ => (↑(RScode pt5 1) : Set (Fin 4 → ZMod 5))) (fun _ => 0))
      (honestStrategy (sigFold (towerFold (fun _ => 4) 1 (fun _ w _ => w))) ⟨0, w4⟩
        (fsChain (towerEnc 1 (fun _ => 4))
          (honestStrategy (sigFold (towerFold (fun _ => 4) 1 (fun _ w _ => w)))
            ⟨0, w4⟩) H 1 []))))
    (fun H hH => of_decide_eq_true hH)
  have h0 : ((1 : ℕ) : ℝ) * ((((1 - 1) * (0 + 1) : ℕ)) : ℝ)
      / (Fintype.card (ZMod 5) : ℝ) = 0 := by
    norm_num
  rw [h0] at h
  exact le_antisymm h (winProb_nonneg _)

end TowerFire

/-! ## §6 — Deployed-schedule arithmetic (the numbers the interface fixes for L1–L6). -/

-- The UD side condition and the boundary shave (mirrors Scaffolding).
#guard 2 * 7340028 + 2 ^ 21 ≤ 2 ^ 24
-- Single top fold of the deployed tower (arity 8): the schedule m·r₁ ≤ r₀ admits
-- r₁ = 917503 under the doc-§4 top radius 7340028.
#guard 8 * 917503 = 7340024
#guard 7340024 ≤ 7340028
-- The per-fold bad-set cap the tower theorem consumes at the top layer: (m−1)(r₁+1).
-- ≈ 2^22.6 bad challenges; over the quartic extension |R| ≈ 2^123.6 this is ≈ 101 bits/fold
-- — the honest UD-route per-fold number, NOT the ledger's Johnson-column 109/111.
#guard (8 - 1) * (917503 + 1) = 6422528
-- Illustrative depth-5 tower (2^24 → 2^9): last layer n = 512, k = 64, r₅ = 220 sits inside
-- its UD regime, and the schedule-composed TOP radius is 8^5·220 = 7208960 — inside the
-- decode radius 7340032 (feeds ColsClose a fortiori), but BELOW the single-shot 7340028:
-- the tower consumer needs the Param form at every layer, not one instantiation.
#guard 2 * 220 + 64 ≤ 512
#guard 8 ^ 5 * 220 = 7208960
#guard 7208960 ≤ 7340032
-- The RLC batch threshold at width 256 (doc §4(ii)): (m−1)(r+1) ≈ 2^30.8 ⟹ ≈ 92.8 bits.
#guard (256 - 1) * 7340029 = 1871707395

/-! ## §7 — Axiom hygiene: every theorem pinned to the three kernel axioms. -/

#assert_all_clean [closeN_coe_iff, RScode_eq_rsCode, simClose_iff_interleavedClose,
  simClose_cols, pairSimClose_cols, mem_curveGood, mem_pairGood, curveGood_card_le,
  pairGood_card_le, curveUDParam_one, curveUDParam_pair_exact, w4_not_mem,
  uFire_not_simClose, one_mem_curveGood, curveGood_fire, deployed_code_eq,
  deployed_colsClose_of_curveUD, deployed_deep_pair_close, rlc_alpha_bad_bound,
  towerFar_of_le, mem_towerGood, towerGood_card_le, towerChainStepIdx,
  rr_succ_le_rr_one, towerE_card_le, towerE_cover, ud_tower_far_survival, fireLift,
  w4_far0, tower_fire]

end Dregg2.Circuit.CorrelatedAgreement.Interface
